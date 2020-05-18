import tempfile
import copy
import random
import itertools
import math
import os
import sage
from pathlib import Path
from collections import defaultdict 
import traceback
# from numba import njit 
# import numpy as np

import settings as dig_settings
import helpers.vcommon as dig_common_helpers
import helpers.src as dig_src
import data.prog as dig_prog
from data.prog import Symb, Symbs
from data.traces import Traces, Inps
from helpers.miscs import Z3, Miscs
# from bin import Bin

from utils import settings
from utils.logic import *
from utils.loop import *
from lib import *
from solver import ZSolver, Z3Py, Z3Bin, PySMT
from validate import Validator, CPAchecker, UAutomizer, UTaipan, Portfolio
import utils.profiling
from utils.profiling import timeit

mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

class Stack(object):
    def __init__(self):
        self.store = []

    def push(self, elem):
        self.store.append(elem)

    def pop(self):
        if len(self.store) > 0:
            return self.store.pop()
        else:
            return None

    def dequeue(self):
        if len(self.store) > 0:
            return self.store.pop(0)
        else:
            return None

    def items(self):
        return self.store

    def size(self):
        return len(self.store)

    def __repr__(self):
        return self.store.__repr__()

class DStack(object):
    def __init__(self, key_of):
        self.store = defaultdict(Stack)
        self.min_key = 0
        self.max_key = -1
        self.key_of = key_of

    def push(self, elem):
        k = self.key_of(elem)
        self.min_key = min(self.min_key, k)
        self.max_key = max(self.max_key, k)
        self.store[k].push(elem)

    def pop(self):
        if self.size() <= 0:
            return None
        
        # while self.store[self.max_key].size() == 0:
        #     self.store.pop(self.max_key)
        #     self.max_key = self.max_key + 1

        while self.max_key not in self.store:
            self.max_key = self.max_key + 1
        
        max_store = self.store[self.max_key]
        elem = max_store.pop()
        if max_store.size() == 0:
            self.store.pop(self.max_key)
            self.max_key = self.max_key - 1
        return elem

    def dequeue(self):
        if self.size() <= 0:
            return None

        # while self.store[self.min_key].size() == 0:
        #     self.store.pop(self.min_key)
        #     self.min_key = self.min_key + 1

        while self.min_key not in self.store:
            self.min_key = self.min_key + 1

        min_store = self.store[self.min_key]
        elem = min_store.dequeue()
        if min_store.size() == 0:
            self.store.pop(self.min_key)
            self.min_key = self.min_key + 1
        return elem

    def items(self):
        return [e for _, s in self.store.items() for e in s.items()]

    def size(self):
        return sum([s.size() for _, s in self.store.items()])

class Setup(object):
    def __init__(self, seed, inp):
        self.seed = seed
        self.inp = inp
        self.is_java_inp = inp.endswith(".java") or inp.endswith(".class")
        self.is_c_inp = inp.endswith(".c")
        self.is_binary_inp = self.is_binary(inp)
        assert (self.is_java_inp or self.is_c_inp or self.is_binary_inp), inp

        # Dig's settings
        dig_settings.DO_MINMAXPLUS = False
        dig_settings.DO_MINMAXPLUS = False

        self.n_inps = settings.n_inps
        # self.preloop_loc = dig_settings.TRACE_INDICATOR + '1' # vtrace1
        # self.inloop_loc = dig_settings.TRACE_INDICATOR + '2' # vtrace2
        # self.postloop_loc = dig_settings.TRACE_INDICATOR + '3' # vtrace3
        # self.transrel_loc = dig_settings.TRACE_INDICATOR + '4' # vtrace4
        # self.refinement_depth = 1
        self.tmpdir = Path(tempfile.mkdtemp(dir=dig_settings.tmpdir, prefix="Dig_"))
        self.symstates = None
        # self.solver = ZSolver(self.tmpdir)
        # self.solver = PySMT() 
        self.solver = Z3Py()
                
        self.init_symvars_prefix = None
        if self.is_binary_inp:
            from bin import Bin
            prog = Bin(self.inloop_loc, inp)
            inp_decls, inv_decls, mainQ_name = prog.parse()
        else:
            if self.is_java_inp:
                from helpers.src import Java as java_src
                src = java_src(Path(inp), self.tmpdir)
                exe_cmd = dig_settings.Java.JAVA_RUN(tracedir=src.tracedir, funname=src.funname)
            else:
                from helpers.src import C as c_src
                # import alg
                mlog.debug("Create C source for mainQ: {}".format(self.tmpdir))

                self.init_symvars_prefix = dig_settings.C.CIVL_INIT_SYMVARS_PREFIX
                
                trans_outf = self.tmpdir / (os.path.basename(inp))
                trans_cmd = settings.CIL.TRANSFORM(inf=inp,
                                                   outf=trans_outf, 
                                                   bnd=settings.LOOP_ITER_BND)
                mlog.debug("trans_cmd: {}".format(trans_cmd))
                trans_rmsg, trans_errmsg = CM.vcmd(trans_cmd)
                # assert not trans_errmsg, "'{}': {}".format(trans_cmd, trans_errmsg)
                assert trans_outf.exists(), trans_outf
                # mlog.debug("trans_rmsg: {}".format(trans_rmsg))

                cg = self._parse_call_graph(trans_rmsg)
                mlog.debug("cg: {}".format(cg))

                self.trans_inp = trans_outf
                self.cg = cg

                src = c_src(Path(self.trans_inp), self.tmpdir)
                exe_cmd = dig_settings.C.C_RUN(exe=src.traceexe)

                self.src = src

                postorder_vloop_ids = self._collect_vloops_in_postorder_from_main(self.cg)
                mlog.debug('postorder_vloop_ids: {}'.format(postorder_vloop_ids))

                self.vloop_info = []
                for vloop_id in postorder_vloop_ids:
                    self.vloop_info.append(LoopInfo(vloop_id, src.inv_decls))
                
            inp_decls, inv_decls, mainQ_name = src.inp_decls, src.inv_decls, src.mainQ_name
            prog = dig_prog.Prog(exe_cmd, inp_decls, inv_decls)

        mlog.debug("inp_decls ({}): {}".format(type(inp_decls), inp_decls))
        mlog.debug("inv_decls ({}): {}".format(type(inv_decls), inv_decls))

        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self.mainQ_name = mainQ_name

        self.init_inp_decls = None
        if self.is_c_inp:
            assert self.init_symvars_prefix, self.init_symvars_prefix
            self.init_inp_decls = Symbs([Symb(self.init_symvars_prefix + s.name, s.typ) 
                                         for s in self.inp_decls])

        # self.transrel_pre_inv_decls, self.transrel_pre_sst, \
        #     self.transrel_post_sst, transrel_inv_decls = self.gen_transrel_sst()
        # self.inv_decls[self.transrel_loc] = transrel_inv_decls
        # mlog.debug("transrel_pre_inv_decls: {}".format(self.transrel_pre_inv_decls))
        # mlog.debug("transrel_pre_sst: {}".format(self.transrel_pre_sst))
        # mlog.debug("transrel_post_sst: {}".format(self.transrel_post_sst))

        # if settings.prove_nonterm:
        #     try:
        #         mlog.debug("Get symstates for proving NonTerm (prove_nonterm={})".format(settings.prove_nonterm))
        #         self.symstates = self._get_symstates_from_src(self.src)
        #     except Exception as e:
        #         mlog.debug("Get symstates for proving NonTerm: {}".format(e))
        #         raise e
        #     # ss = self.symstates.ss
        #     # for loc in ss:
        #         # for depth in ss[loc]:
        #             # pcs = ss[loc][depth]
        #             # mlog.debug("DEPTH {}".format(depth))
        #             # mlog.debug("pcs ({}):\n{}".format(len(pcs.lst), pcs))
        # else:
        #     pass

        self.exe = Execution(prog)
        self.dig = Inference(self.inv_decls, self.seed, self.tmpdir)

        # mlog.debug("generate random inputs")
        # rand_inps = self.exe.gen_rand_inps(self.n_inps)
        # mlog.debug("get traces from random inputs")
        # self.rand_itraces = self.exe.get_traces_from_inps(rand_inps)  # itraces: input to dtraces

    @timeit
    def gen_rand_inps(self):
        return self.exe.gen_rand_inps(self.n_inps)

    # @timeit
    def get_traces_from_inps(self, inps):
        return self.exe.get_traces_from_inps(inps)

    def _collect_vloops_in_postorder_from_main(self, cg):
        # Do not support mutual loops
        # https://github.com/sosy-lab/sv-benchmarks/blob/master/c/termination-numeric/twisted.c
        postorder_meth_calls = []
        def visit(caller, visited):
            if caller not in visited:
                visited.add(caller)
                callees = cg[caller]
                for callee in callees:
                    visit(callee, visited)
                postorder_meth_calls.append(caller)
        
        visit(dig_settings.MAINQ_FUN, set())
        postorder_vloop_calls = [c for c in postorder_meth_calls if c.startswith(settings.VLOOP_FUN)]
        return postorder_vloop_calls

    @timeit
    def _get_symstates_from_src(self, src, target_loc=None, min_depth=None):

        # exe_cmd = dig_settings.C.C_RUN(exe=src.traceexe)
        inp_decls, inv_decls, mainQ_name = src.inp_decls, src.inv_decls, src.mainQ_name

        if self.is_c_inp:
            from data.symstates import SymStatesC
            mlog.debug('SymStatesC.maxdepth: {}'.format(SymStatesC.maxdepth))
            if min_depth and min_depth > SymStatesC.maxdepth:
                SymStatesC.mindepth = min_depth
                SymStatesC.maxdepth = min_depth + dig_settings.C.SE_DEPTH_INCR

            symstates = SymStatesC(inp_decls, inv_decls)
        
        try:
            symstates.compute(src.symexefile, src.mainQ_name, src.funname, src.symexedir)
        except SystemExit:
            # mlog.debug(traceback.format_exc())
            symstates.ss = {}
        # mlog.debug("symstates: {}".format(symstates.ss))
        mlog.debug('target_loc: {}'.format(target_loc))
        if target_loc:
            if target_loc in symstates.ss:
                return symstates
            else:
                # Increase the depth and try again
                return self._get_symstates_from_src(src, target_loc, min_depth=symstates.maxdepth + 1)
        return symstates

    @timeit
    def _get_loopinfo_from_symstates(self, vloop):
        stem = self._get_stem_from_symstates(vloop)
        loop = self._get_loop_from_symstates(vloop)
        return stem, loop

    def _get_stem_from_symstates(self, vloop):
        # Use symstates of mainQ
        # assert self.symstates, self.symstates

        def _get_stem_from_ss(ss):
            preloop_symstates = ss[vloop.preloop_loc]
            preloop_ss_depths = sorted(preloop_symstates.keys())
            preloop_fst_symstate = None
            while preloop_fst_symstate is None and preloop_ss_depths:
                depth = preloop_ss_depths.pop()
                symstates = preloop_symstates[depth]
                if symstates.lst:
                    preloop_fst_symstate = symstates.lst[0]
            mlog.debug("preloop_fst_symstate: {}".format(preloop_fst_symstate))

            if preloop_fst_symstate:
                mlog.debug("mainQ init_symvars: {}".format(self.symstates.init_symvars))
                stem_cond = preloop_fst_symstate.pc
                stem_transrel = preloop_fst_symstate.slocal
                mlog.debug("stem_cond ({}): {}".format(type(stem_cond), stem_cond))
                mlog.debug("stem_transrel ({}): {}".format(type(stem_transrel), stem_transrel))
                stem = Stem(self.inp_decls, stem_cond, stem_transrel)
                return stem
            else:
                return None

        # mlog.debug('ss: {}'.format(ss))
        mlog.debug('vloop.preloop_loc: {}'.format(vloop.preloop_loc))
        stem = None
            
        if not (self.symstates and vloop.preloop_loc in self.symstates.ss):
            if self.symstates:
                min_depth = self.symstates.maxdepth + 1
            else:
                min_depth = None
            self.symstates = self._get_symstates_from_src(self.src, target_loc=vloop.preloop_loc,
                                                          min_depth=min_depth)

        ss = self.symstates.ss
        assert vloop.preloop_loc in ss, vloop.preloop_loc

        stem = _get_stem_from_ss(ss)
            
        return stem

    def _strip_ptr_loop_params(self, symbs):
        symbs = [Symb(s.name.replace(settings.CIL.PTR_VARS_PREFIX, ''), 'I') 
                 if settings.CIL.PTR_VARS_PREFIX in s.name and s.typ == 'P' 
                 else s for s in symbs]
        return Symbs(symbs)

    def _get_loop_from_symstates(self, vloop):
        # Use symstates of vloop
        if self.is_c_inp:
            from helpers.src import C as c_src
        
            tmpdir = Path(tempfile.mkdtemp(dir=dig_settings.tmpdir, prefix="Dig_"))
            mlog.debug("Create C source for {}: {}".format(vloop.vloop_id, tmpdir))
            src = c_src(Path(self.trans_inp), tmpdir, mainQ=vloop.vloop_id)
            symstates = self._get_symstates_from_src(src, target_loc=vloop.inloop_loc)
            ss = symstates.ss
        else:
            raise NotImplementedError

        inp_decls, inv_decls = src.inp_decls, src.inv_decls
        loop_init_symvars = symstates.init_symvars
        inp_decls = self._strip_ptr_loop_params(inp_decls)
        loop_init_symvars = self._strip_ptr_loop_params(loop_init_symvars)
        mlog.debug("vloop inp_decls: {}".format(inp_decls))
        mlog.debug("vloop inv_decls: {}".format(inv_decls))
        mlog.debug("vloop init_symvars: {}".format(loop_init_symvars))
        
        assert vloop.inloop_loc in ss, vloop.inloop_loc

        if vloop.inloop_loc in ss:
            inloop_symstates = ss[vloop.inloop_loc]
            inloop_ss_depths = sorted(inloop_symstates.keys())
            inloop_fst_symstate = None
            inloop_snd_symstate = None
            while (inloop_fst_symstate is None or inloop_snd_symstate is None):
                if inloop_ss_depths:
                    depth = inloop_ss_depths.pop()
                    depth_symstates = inloop_symstates[depth]
                    # mlog.debug("DEPTH {}".format(depth))
                    # mlog.debug("symstates ({}):\n{}".format(len(symstates.lst), symstates))
                    if len(depth_symstates.lst) >= 2:
                        inloop_fst_symstate = depth_symstates.lst[0]
                        inloop_snd_symstate = depth_symstates.lst[1]
                else:
                    symstates = self._get_symstates_from_src(src, target_loc=vloop.inloop_loc,
                                                             min_depth=symstates.maxdepth + 1)
                    ss = symstates.ss
                    inloop_symstates = ss[vloop.inloop_loc]
                    inloop_ss_depths = sorted(inloop_symstates.keys())
            
            assert inloop_fst_symstate, inloop_fst_symstate
            assert inloop_snd_symstate, inloop_snd_symstate
            
            if inloop_fst_symstate and inloop_snd_symstate:
                # Get loop's condition and transition relation
                inloop_fst_slocal = z3.substitute(inloop_fst_symstate.slocal, vloop.transrel_pre_sst)
                inloop_snd_slocal = z3.substitute(inloop_snd_symstate.slocal, vloop.transrel_post_sst)
                mlog.debug("inloop_fst_slocal: {}".format(inloop_fst_slocal))
                mlog.debug("inloop_snd_slocal: {}".format(inloop_snd_slocal))
                # inloop_vars = Z3.get_vars(inloop_fst_symstate.slocal).union(Z3.get_vars(inloop_snd_symstate.slocal))
                # inloop_inv_vars = inv_decls[vloop.inloop_loc].exprs(settings.use_reals)
                # inloop_ex_vars = inloop_vars.difference(inloop_inv_vars)
                # mlog.debug("inloop_ex_vars: {}".format(inloop_ex_vars))
                # inloop_trans_f = z3.Exists(list(inloop_ex_vars), z3.And(inloop_fst_slocal, inloop_snd_slocal))
                # loop_transrel = Z3.qe(inloop_trans_f)
                # X_x, X_y -> x, y
                init_sst = list(zip(loop_init_symvars.exprs(settings.use_reals),
                                    inp_decls.exprs(settings.use_reals)))
                loop_transrel = z3.And(inloop_fst_slocal, inloop_snd_slocal)
                loop_transrel = z3.substitute(loop_transrel, init_sst)
                mlog.debug("loop_transrel: {}".format(loop_transrel))

                mlog.debug("inloop_fst_symstate: pc: {}".format(inloop_fst_symstate.pc))
                mlog.debug("inloop_fst_symstate: slocal: {}".format(inloop_fst_symstate.slocal))
                # loop_cond = Z3.qe(z3.Exists(list(inloop_ex_vars), 
                #                                   z3.And(inloop_fst_symstate.pc, inloop_fst_symstate.slocal)))
                loop_cond = z3.substitute(inloop_fst_symstate.pc, init_sst)
                mlog.debug("loop_cond: {}".format(loop_cond))
                terms = ZSolver.get_mul_terms(loop_cond)
                nonlinear_terms = list(itertools.filterfalse(lambda t: not ZSolver.is_nonlinear_mul_term(t), terms))
                mlog.debug("terms: {}".format(terms))
                mlog.debug("nonlinear_terms: {}".format(nonlinear_terms))

                return Loop(inp_decls, loop_cond, loop_transrel)
        return None

    def _parse_call_graph(self, msg):
        lines = [l.strip().split(':') for l in msg.split('\n') if l.strip() != ''
                #  if l.startswith(dig_settings.MAINQ_FUN)
                #  or l.startswith(settings.VLOOP_FUN)
                ]
        cg = defaultdict(list)

        for l in lines:
            # mlog.debug('l: {}'.format(l))
            caller, s = l
            caller = caller.strip()
            for callee in s.split(','):
                callee = callee.strip()
                if callee != '':
                    cg[caller].append(callee)
        return cg

    def _get_loopinfo_from_traces(self):
        raise NotImplementedError
        # old_do_ieqs = dig_settings.DO_IEQS
        # # dig_settings.DO_IEQS = False
        # transrel_itraces = {}
        # inloop_loc = self.inloop_loc
        # postloop_loc = self.postloop_loc
        # for inp, dtraces in self.rand_itraces.items():
        #     if inloop_loc in dtraces:
        #         inloop_traces = dtraces[inloop_loc]
        #         transrel_traces = []
        #         if len(inloop_traces) >= 1:
        #             if postloop_loc in dtraces:
        #                 inloop_zip_traces = zip(inloop_traces, inloop_traces[1:] + [dtraces[postloop_loc][0]])
        #             else:
        #                 inloop_zip_traces = zip(inloop_traces[:-1], inloop_traces[1:])
        #         else:
        #             inloop_zip_traces = []
        #         for transrel_pre, transrel_post in inloop_zip_traces:
        #             ss = tuple(list(map(lambda s: s + '0', transrel_pre.ss)) + 
        #                        list(map(lambda s: s + '1', transrel_post.ss)))
        #             vs = transrel_pre.vs + transrel_post.vs
        #             transrel_traces.append(Trace.parse(ss, vs))
        #         transrel_itraces[inp] = {self.transrel_loc: transrel_traces}
        # # mlog.debug("transrel_itraces: {}".format(transrel_itraces))
        # transrel_invs = self.dig.infer_from_traces(transrel_itraces, self.transrel_loc)
        # # transrel_invs = self.dig.infer_from_traces(self.rand_itraces, self.transrel_loc)
        # mlog.debug("transrel_invs: {}".format(transrel_invs))
        # dig_settings.DO_IEQS = old_do_ieqs

        # transrel_invs = ZConj(transrel_invs)
        # if transrel_invs.is_unsat():
        #     return None
        # transrel_expr = transrel_invs.expr()
        # return transrel_expr

    @timeit
    def get_loopinfo(self, vloop):
        stem, loop = self._get_loopinfo_from_symstates(vloop)
        mlog.debug('stem: {}'.format(stem))
        mlog.debug('loop: {}'.format(loop))
        if stem is None or loop is None:
            stem, loop = self._get_loopinfo_from_traces()
        return stem, loop

    def infer_precond(self):
        if not self.symstates:
            return None
        else:
            ss = self.symstates
            preloop_symstates = ss[self.preloop_loc]
            preloop_ss_depths = sorted(preloop_symstates.keys())
            for depth in preloop_ss_depths:
                symstates = preloop_symstates[depth]
                return symstates.myexpr

    def infer_loop_cond(self):
        if self.is_c_inp:
            from helpers.src import C as c_src
            from data.symstates import SymStatesC
            import alg
            tmpdir = Path(tempfile.mkdtemp(dir=dig_settings.tmpdir, prefix="Dig_"))
            mlog.debug("Create C source for vloop")
            src = c_src(Path(self.inp), tmpdir, mainQ="vloop")
            exe_cmd = dig_settings.C.C_RUN(exe=src.traceexe)
            inp_decls, inv_decls, mainQ_name = src.inp_decls, src.inv_decls, src.mainQ_name
            prog = dig_prog.Prog(exe_cmd, inp_decls, inv_decls)
            exe = Execution(prog)
            dig = Inference(inv_decls, self.seed)

            symstates = SymStatesC(inp_decls, inv_decls)
            symstates.compute(
                src.symexefile, src.mainQ_name,
                src.funname, src.symexedir)
            ss = symstates.ss
            # mlog.debug("SymStates ({}): {}".format(type(ss), ss))
            # for loc, depthss in ss.items():
            #     for depth, states in depthss.items():
            #         for s in states.lst:
            #             mlog.debug("SymState ({}, {}):\n{}\n{}".format(type(s), s in states, s, s.expr))

            # rand_inps = exe.gen_rand_inps(self.n_inps)
            # rand_itraces = exe.get_traces_from_inps(rand_inps)
            # loop_cond = None
            # no_inloop_invs = False
            # no_postloop_invs = False

            # while loop_cond is None:
            #     postloop_invs = ZConj(dig.infer_from_traces(rand_itraces, self.postloop_loc))
            #     inloop_invs = ZConj(dig.infer_from_traces(rand_itraces, self.inloop_loc))
            #     mlog.debug("postloop_invs: {}".format(postloop_invs))
            #     mlog.debug("inloop_invs: {}".format(inloop_invs))
            #     if not inloop_invs and no_inloop_invs:
            #         loop_cond = postloop_invs.negate()
            #     else:
            #         if not inloop_invs:
            #             no_inloop_invs = True
            #         covered_f = z3.Or(postloop_invs.expr(), inloop_invs.expr())
            #         uncovered_f = z3.Not(covered_f)
            #         models, _ = ZSolver.get_models(uncovered_f, 
            #                                        self.n_inps, self.tmpdir, 
            #                                        settings.use_random_seed)
            #         mlog.debug("uncovered models: {}".format(models))
            #         if isinstance(models, list) and models:
            #             n_inps = ZSolver.mk_inps_from_models(models, self.inp_decls.exprs((settings.use_reals)), exe)
            #             mlog.debug("uncovered inps: {}".format(n_inps))
            #             mlog.debug("Starting get_traces")
            #             nitraces = exe.get_traces_from_inps(n_inps)
            #             mlog.debug("get_traces stopped")
            #             # mlog.debug("uncovered rand_itraces: {}".format(nitraces))
            #             rand_itraces.update(nitraces)
            #         else:
            #             loop_cond = inloop_invs
            
            # mlog.debug("loop_cond: {}".format(loop_cond))
            # return loop_cond

    def is_binary(self, fn):
        import subprocess
        mime = subprocess.Popen(["file", "--mime", fn], stdout=subprocess.PIPE).communicate()[0]
        return b"application/x-executable" in mime

class NonTerm(object):
    def __init__(self, config):
        self._config = config
        # loopinfo = config.get_loopinfo()
        # self.stem = loopinfo.stem
        # self.loop = loopinfo.loop
        self.tCexs = []

    @timeit
    def verify(self, rcs, vloop):
        assert isinstance(rcs, ZFormula), rcs
        assert not rcs.is_unsat(), rcs
        _config = self._config

        if not rcs:
            return False, None, None
        else:
            # assert rcs, rcs
            init_symvars_prefix = _config.init_symvars_prefix

            loop_transrel = vloop.loop.transrel
            loop_cond = vloop.loop.cond

            mlog.debug("loop_transrel: {}".format(loop_transrel))
            mlog.debug("loop_cond: {}".format(loop_cond))
            mlog.debug("rcs: {}".format(rcs))

            if not rcs.implies(ZFormula([loop_cond])):
                mlog.debug("rcs_cond =/=> loop_cond")
                rcs.add(loop_cond)

            rcs_lst = list(rcs)
            def mk_label(e):
                if e in rcs_lst:
                    return 'c_' + str(rcs_lst.index(e))
                else:
                    return None
            labeled_rcs, label_d = ZFormula.label(rcs, mk_label)
            rev_label_d = {v: k for k, v in label_d.items()}
            mlog.debug("labeled_rcs: {}".format(labeled_rcs))

            # R /\ T => R'
            # rcs_l = z3.substitute(rcs.expr(), _config.transrel_pre_sst)
            # mlog.debug("rcs_l: {}".format(rcs_l))
            transrel_rcs = ZFormula.substitue(labeled_rcs, vloop.transrel_pre_sst)
            transrel_rcs.add(loop_transrel)
            mlog.debug("transrel_rcs: {}".format(transrel_rcs))

            init_transrel_rcs = copy.deepcopy(transrel_rcs)
            init_transrel_rcs.add(vloop.stem.cond)
            init_transrel_rcs.add(vloop.stem.transrel)
            mlog.debug("init_transrel_rcs: {}".format(init_transrel_rcs))

            # Unreachable recurrent set
            # if init_transrel_rcs.is_unsat():
            #     return False, None, None

            dg = defaultdict(list)
            def _check(rc):
                rc_label = label_d[rc]
                mlog.debug("rc: {}:{}".format(rc, rc_label))
                # init_transrel_rcs is sat
                f = copy.deepcopy(transrel_rcs)
                rc_r = z3.substitute(rc, vloop.transrel_post_sst)
                f.add(z3.Not(rc_r))
                mlog.debug("rc_r: {}".format(rc_r))
                mlog.debug("f: {}".format(f))

                rs, _, unsat_core = _config.solver.get_models(f, 1, using_random_seed=settings.use_random_seed)
                
                if rs is None:
                    mlog.debug("rs: unknown")
                    return rs
                elif rs is False:
                    mlog.debug("rs: unsat")
                    mlog.debug("unsat_core: {}".format(unsat_core))
                    assert unsat_core is not None, unsat_core
                    dg[rc_label] = unsat_core
                    return rs
                else:
                    # isinstance(rs, list) and rs:
                    mlog.debug("rs: sat")
                    init_f = copy.deepcopy(init_transrel_rcs)
                    init_f.add(z3.Not(rc_r))

                    init_rs, _, _ = _config.solver.get_models(init_f, _config.n_inps, 
                                                              _config.init_inp_decls, 
                                                              settings.use_random_seed)
                    mlog.debug('init_f: {}'.format(init_f))
                    mlog.debug('init_rs: {}'.format(init_rs))
                    if init_rs is None:
                        return []
                    else:
                        init_models = []
                        init_symvars_prefix_len = len(init_symvars_prefix)
                        if isinstance(init_rs, list):
                            for r in init_rs:
                                init_model = []
                                for (x, v) in r:
                                    if x.startswith(init_symvars_prefix):
                                        init_model.append((x[init_symvars_prefix_len:], v))
                                if init_model:
                                    init_models.append(init_model)

                        mlog.debug("init_models: sat ({} models)".format(len(init_models)))
                        inps = _config.solver.mk_inps_from_models(init_models, 
                                                                  _config.inp_decls, 
                                                                  _config.exe,
                                                                  _config.n_inps)
                        mlog.debug("inps: {}".format(inps))
                        return inps

            chks = [(rc, _check(rc)) for rc in rcs]

            # Finding a mutually dependent recurrent set (mds)
            # A mds is a valid recurrent set
            # It can be used to simplify a valid recurrent set
            # or find a valid recurrent set from an invalid one.
            mlog.info("dg: {}".format(dg))
            mlog.info("label_d: {}".format(label_d))
            mlog.info("rev_label_d: {}".format(rev_label_d))
            
            loop_cond_label = label_d[loop_cond]
            mlog.info("loop_cond_label: {}".format(loop_cond_label))
            # A condition whose label is in dg is already proved succesfully
            mds_labels = self._get_mutually_dependent_set(loop_cond_label, dg)
            mds = ZConj([rev_label_d[lbl] for lbl in mds_labels])
            mlog.info("mds_labels: {}".format(mds_labels))
            mlog.info("mds: {}".format(mds))

            if all(rs is False for _, rs in chks):
                return True, None, mds  # valid
            else:
                sCexs = []
                for rc, rs in chks:
                    if rs is None:
                        return False, None, None  # unknown
                    elif rs:  # sat
                        assert isinstance(rs, Inps), rs
                        assert len(rs) > 0
                        itraces = _config.get_traces_from_inps(rs)
                        sCexs.append((rc, itraces))
                return False, sCexs, mds  # invalid with a set of new Inps

    @timeit
    def strengthen(self, rcs, invalid_rc, itraces, vloop):
        _config = self._config
        base_term_inps, term_inps, mayloop_inps = vloop.cl.classify_inps(itraces)
        Classification.print_inps(itraces)
        mlog.debug("base_term_inps: {}".format(len(base_term_inps)))
        mlog.debug("term_inps: {}".format(len(term_inps)))
        mlog.debug("mayloop_inps: {}".format(len(mayloop_inps)))
        mlog.debug("rcs: {}".format(rcs))

        mayloop_invs = ZConj(_config.dig.infer_from_traces(
                                itraces, vloop.inloop_loc, mayloop_inps))
        mlog.debug("mayloop_invs: {}".format(mayloop_invs))

        term_invs = ZConj(_config.dig.infer_from_traces(
                            itraces, vloop.inloop_loc, term_inps, maxdeg=1))
        mlog.debug("term_invs: {}".format(term_invs))

        # term_traces = []
        # for term_inp in term_inps:
        #     term_traces.append(itraces[term_inp])
        term_itraces = {term_inp: itraces[term_inp] for term_inp in term_inps}
        self.tCexs.append((term_invs, term_itraces))
        
        # term_cond = z3.Or(base_term_pre.expr(), term_invs.expr())
        # term_cond = term_invs.expr()
        # simplified_term_cond = Z3.simplify(term_cond)
        # cnf_term_cond = Z3.to_cnf(simplified_term_cond)
        # mlog.debug("simplified_term_cond: {}".format(simplified_term_cond))
        # mlog.debug("cnf_term_cond: {}".format(cnf_term_cond))
        # dnf_neg_term_cond = Z3.to_nnf(z3.Not(cnf_term_cond))
        # mlog.debug("dnf_neg_term_cond: {}".format(dnf_neg_term_cond))

        candidate_nrcs = []

        # Candidate rcs from potential termination invs
        # A /\ B /\ C
        # RCS /\ !A, RCS /\ !B
        for term_inv in term_invs:
            # mlog.debug("term_inv: {}".format(term_inv))
            nrcs = copy.deepcopy(rcs)
            nrcs.add(z3.Not(term_inv))
            candidate_nrcs.append(nrcs)

        # In the next step, we will find a mutually dependent set 
        # from this mayloop_invs. That set will be a valid rcs.
        if mayloop_invs:
            candidate_nrcs.append(mayloop_invs)
        
        # if invalid_rc is not None:
        #     nrcs = copy.deepcopy(rcs)
        #     nrcs.remove(invalid_rc)
        #     mlog.debug("invalid_rc: {}".format(invalid_rc))
        #     mlog.debug("nrcs: {}".format(nrcs))
        #     if nrcs:
        #         candidate_nrcs.append(nrcs)
        
        return candidate_nrcs

    def _get_mutually_dependent_set(self, start, dg):
        ws = [start]
        visited = set()
        while ws:
            node = ws.pop(0)
            if node not in dg:
                return set()
            else:
                visited.add(node)
                node_deps = dg[node]
                for node_dep in node_deps:
                    if node_dep not in visited:
                        ws.append(node_dep)
        return visited

    def _stat_candidate_rcs(self, rcs):
        stat = defaultdict(int)
        for (_, d, _) in rcs.items():
            stat[d] += 1
        mlog.debug("stat ({} total): {}".format(rcs.size(), stat))

    def is_reachable_rcs(self, vloop, rcs):
        init_transrel_rcs = ZFormula.substitue(rcs, vloop.transrel_pre_sst)
        init_transrel_rcs.add(vloop.stem.cond)
        init_transrel_rcs.add(vloop.stem.transrel)
        return not init_transrel_rcs.is_unsat()

    @timeit
    def prove_nonterm_vloop(self, vloop):
        _config = self._config
        stem, loop = _config.get_loopinfo(vloop)
        vloop.stem = stem
        vloop.loop = loop
        valid_rcs = []
        self.tCexs = []

        if vloop.stem is None or vloop.loop is None:
            mlog.debug("No loop information: stem={}, loop={}".format(self.stem, self.loop))
            return []
        else:
            mlog.debug('use_dfs: {}'.format(settings.use_dfs))
            mlog.debug('use_bfs: {}'.format(settings.use_bfs))
            # candidate rcs, depth, ancestors
            # candidateRCS = Stack()
            candidateRCS = DStack(key_of=lambda rcs: rcs[1])
            candidateRCS.push((ZConj([vloop.loop.cond]), 0, []))
            while candidateRCS.size() > 0:
                # mlog.debug("candidateRCS: {}".format(len(candidateRCS)))
                self._stat_candidate_rcs(candidateRCS)
                candidates = []
                if settings.use_dfs:
                    # rcs, depth, ancestors = candidateRCS.pop()
                    candidate = candidateRCS.pop()
                    candidates.append(candidate)
                elif settings.use_bfs:
                    # rcs, depth, ancestors = candidateRCS.dequeue()
                    candidate = candidateRCS.dequeue()
                    candidates.append(candidate)
                else:
                    # use 0 for queue - BFS
                    # rcs, depth, ancestors = candidateRCS.dequeue()
                    fst_candidate = candidateRCS.dequeue()
                    lst_candidate = candidateRCS.pop()
                    candidates.append(fst_candidate)
                    if lst_candidate:
                        candidates.append(lst_candidate)

                def _f(task):
                    chk, rs = self.prove_rcs(vloop, *task)
                    return (chk, rs)

                if len(candidates) > 1:
                    wrs = Miscs.run_mp_ex("prove_rcs", candidates, _f)
                else:
                    wrs = [_f(candidates[0])]
                for chk, rs in wrs:
                    if chk is True:
                        valid_rcs.append(rs)
                        return [rs], []
                        # break
                    elif chk is False:
                        for r in rs:
                            candidateRCS.push(r) 

                # chk, rs = self.prove_rcs(vloop, *candidate)
                # if chk is None:
                #     continue
                # elif chk is True:
                #     valid_rcs.append(rs)
                #     # break
                # else:
                #     for r in rs:
                #         candidateRCS.push(r)
                
            
            term_itraces_cex = {}
            for (tInvs, tTraces) in self.tCexs:
                mlog.debug("tCex: {}".format(tInvs))
                term_itraces_cex.update(tTraces)
            return valid_rcs, term_itraces_cex

    def prove_rcs(self, vloop, rcs, depth, ancestors):
        mlog.debug("PROVE_NT DEPTH {}: {}".format(depth, rcs))
        if rcs.is_unsat():
            return None, None

        if depth < settings.max_nonterm_refinement_depth:
            chk, sCexs, mds = self.verify(rcs, vloop)
            # mlog.debug("sCexs: {}".format(sCexs))
            if mds and len(mds) < len(rcs):
                # mds is a valid recurrent set which is smaller (weaker) than rcs
                nancestors = copy.deepcopy(ancestors)
                nancestors.append((depth, rcs))
                if self.is_reachable_rcs(vloop, mds):
                    # valid_rcs.append((mds, nancestors))
                    return True, (mds, nancestors)
            
            if chk:
                mlog.debug('new valid rcs: {}'.format(rcs))
                if self.is_reachable_rcs(vloop, rcs):
                    # valid_rcs.append((rcs, ancestors))
                    return True, (rcs, ancestors)
                    # break
                    # return the first valid rcs
                    # return valid_rcs
            elif sCexs is not None:
                new_candidates  = []
                for invalid_rc, cexs in sCexs:
                    nrcs = self.strengthen(rcs, invalid_rc, cexs, vloop)
                    # assert nrcs, nrcs
                    for nrc in nrcs:
                        nancestors = copy.deepcopy(ancestors)
                        nancestors.append((depth, rcs))
                        # candidateRCS.push((nrc, depth+1, nancestors))
                        new_candidates.append((nrc, depth+1, nancestors))
                return False, new_candidates
        return None, None

    def print_valid_rcs(self, valid_rcs):
        for rcs, ancestors in valid_rcs:
            f = Z3.to_dnf(rcs.simplify())
            mlog.info("rcs: {}".format(rcs))
            mlog.info("(simplified) rcs: {}".format(f))
            for depth, ancestor in ancestors:
                if ancestor is None:
                    ancestor_ = None
                else:
                    ancestor_ = Z3.to_dnf(ancestor.simplify())
                mlog.info("ancestor {}: {}".format(depth, ancestor_))

    @timeit
    def prove(self):
        _config = self._config
        res = None
        for vloop in _config.vloop_info:
            valid_rcs, _ = self.prove_nonterm_vloop(vloop)
            if valid_rcs:
                res = (False, vloop.vloop_id, valid_rcs)
                break 
        if res is None:
            print('Non-termination result: Unknown')
        else:
            r, vid, valid_rcs = res
            self.print_valid_rcs(valid_rcs)
            print('Non-termination result: {} ({})'.format(r, vid))

class Term(object):
    def __init__(self, config):
        self._config = config
        self.ntCexs = []
        self.MAX_TOTAL_TRANS_NUM = 2000
        self.MAX_TRANS_NUM = 20
        self.MAX_INP_NUM = math.ceil(self.MAX_TOTAL_TRANS_NUM / self.MAX_TRANS_NUM)
        # 2 * MAX_TRANS_NUM = MAX_TRACE_NUM * (MAX_TRACE_NUM - 1) / 2
        self.MAX_TRACE_NUM = math.floor(math.sqrt(4 * self.MAX_TRANS_NUM))

    def _check_ranking_function_trans(self, t1, t2, model):
        # import timeit
        # start_time = timeit.default_timer()
        # s = z3.Solver()
        # s.add(t1 > t2)
        # s.add(t1 >= 0)
        # for d in model.decls():
        #     zuk = globals()[d.name()]
        #     s.add(zuk == model[d])
        # if s.check() == z3.sat:
        #     r = True
        # else:
        #     r = False
        # elapsed = timeit.default_timer() - start_time
        # mlog.debug("z3: {}".format(elapsed * 1000000))
        
        # start_time = timeit.default_timer()
        st1 = (str(t1)).replace("\n", "") 
        st2 = (str(t2)).replace("\n", "")
        for d in model.decls():
            v = model[d]
            sv = v.as_string()
            dn = d.name()
            st1 = st1.replace(dn, sv)
            st2 = st2.replace(dn, sv)
        # mlog.debug('st1:\n{}'.format(repr(st1)))
        # mlog.debug('st2:\n{}'.format(repr(st2)))
        vt1 = eval(st1)
        vt2 = eval(st2)
        r = (vt1 > vt2) and (vt1 >= 0)
        # elapsed = timeit.default_timer() - start_time
        # mlog.debug("py: {}".format(elapsed * 1000000))

        return r

    def _infer_ranking_function_trans(self, t1, t2, opt):
        opt.push()
        # desc_scond = str(sage.all.operator.gt(t1, t2))
        # bnd_scond = str(sage.all.operator.ge(t1, 0))
        # desc_zcond = eval(desc_scond)
        # bnd_zcond = eval(bnd_scond)
        # desc_zcond = Z3.parse(desc_scond, False)
        # bnd_zcond = Z3.parse(bnd_scond, False)
        opt.add(t1 > t2)
        opt.add(t1 >= 0)

        model = None
        if opt.check() == z3.sat:
            model = opt.model()
            # mlog.debug("model: {}".format(model))
        opt.pop()
        return model

    def _to_Z3(self, f):
        return Z3.parse(str(f), False)

    @timeit
    def infer_ranking_functions(self, vloop, vs, term_itraces):
        mlog.debug('vloop: {}'.format(vloop.vloop_id))
        mlog.debug('term_itraces: {}'.format(len(term_itraces)))

        if not term_itraces:
            return []

        _config = self._config
        
        # Create and randomly pick terminating transitive closure transitions 
        # input: (t1: {x=2, y=3, z=5}, t2, t3) -> [(t1, t2), (t1, t3), (t2, t3)]

        train_rand_trans = []
        sampled_term_inps = term_itraces.keys()
        if len(sampled_term_inps) > self.MAX_INP_NUM:
            sampled_term_inps = random.sample(sampled_term_inps, k=self.MAX_INP_NUM)

        for term_inp in sampled_term_inps:
            term_traces = term_itraces[term_inp]
            inloop_term_traces = term_traces[vloop.inloop_loc]
            assert inloop_term_traces, inloop_term_traces

            if vloop.postloop_loc in term_traces:
                postloop_term_traces = term_traces[vloop.postloop_loc][:1]
            else:
                postloop_term_traces = []

            loop_term_traces = inloop_term_traces + postloop_term_traces

            if len(loop_term_traces) > self.MAX_TRACE_NUM:
                sampled_loop_term_trace_indexes = random.sample(range(len(loop_term_traces)), k=self.MAX_TRACE_NUM)
                sorted_loop_term_trace_indexes = sorted(sampled_loop_term_trace_indexes)
                loop_term_traces = [loop_term_traces[i] for i in sorted_loop_term_trace_indexes]

            # mlog.debug('generating transitive closure transitions with {} traces'.format(len(loop_term_traces)))
            assert len(loop_term_traces) <= self.MAX_TRANS_NUM + 1, len(loop_term_traces)
            trans_idx = list(itertools.combinations(range(len(loop_term_traces)), 2))
            # mlog.debug('random.shuffle')
            random.shuffle(trans_idx)
            trans_idx_len = len(trans_idx)
            # mlog.debug('trans_idx_len: {}'.format(trans_idx_len))
            splitter_idx = min(self.MAX_TRANS_NUM, trans_idx_len)
            # splitter_idx = trans_idx_len
            # mlog.debug("splitter_idx: {}".format(splitter_idx))
            for (i1, i2) in trans_idx[:splitter_idx]:
                assert i1 < i2, (i1, i2)
                rand_trans = (loop_term_traces[i1], loop_term_traces[i2])
                # mlog.debug("rand_trans: {} -> {}: {}".format(i1, i2, rand_trans))
                train_rand_trans.append(rand_trans)
        mlog.debug('train_rand_trans: {}'.format(len(train_rand_trans)))
        return self._infer_ranking_functions_from_trans(vs, train_rand_trans)

    def _infer_ranking_functions_from_trans(self, vs, train_rand_trans):
        # Create a ranking function template
        terms = Miscs.get_terms([sage.all.var(v) for v in vs.names], 1)
        rnk_template, uks = Miscs.mk_template(terms, None, retCoefVars=True)
        mlog.debug("rnk_template ({}): {}".format(type(rnk_template), rnk_template))
        mlog.debug("uks: {}".format(uks))

        zuks = []
        for uk in uks:
            suk = str(uk)
            zuk = z3.Int(suk)
            globals()[suk] = zuk
            zuks.append(zuk)

        def zabs(x):
            return z3.If(x >= 0, x, -x)

        opt = z3.Optimize()
        zabs_sum = functools.reduce(lambda u, v: u + v, [zabs(u) for u in zuks])
        opt.minimize(zabs_sum)
        for zuk in zuks:
            opt.minimize(zabs(zuk))

        train_term_rand_trans = []
        for (t1, t2) in train_rand_trans:
            t1_term = self._to_Z3(rnk_template.subs(t1.mydict))
            t2_term = self._to_Z3(rnk_template.subs(t2.mydict))
            train_term_rand_trans.append((t1_term, t2_term))

        mlog.debug("train_term_rand_trans: {}".format(len(train_term_rand_trans)))
        
        rnk_ztemplate = self._to_Z3(rnk_template)
        ranking_function_list = []
        while train_term_rand_trans:
            (t1, t2) = train_term_rand_trans.pop()
            mlog.debug("t1: {}".format(t1))
            mlog.debug("t2: {}".format(t2))
            model = self._infer_ranking_function_trans(t1, t2, opt)
            mlog.debug("model: {}".format(model))
            if model:
                rf = model.evaluate(rnk_ztemplate)
                ranking_function_list.append(rf)
                mlog.debug("rf: {}".format(rf))

                # start_time = timeit.default_timer()
                # l_train_rand_trans = [(t1, t2) for (t1, t2) in train_term_rand_trans 
                #                               if not (self._check_ranking_function_trans(t1, t2, model))]
                # elapsed = timeit.default_timer() - start_time
                # mlog.debug("l_train_rand_trans: {}".format(elapsed * 1000000))
                
                # start_time = timeit.default_timer()
                invalid_train_term_rand_trans = itertools.filterfalse(lambda t: (self._check_ranking_function_trans(*t, model)),
                                                                      train_term_rand_trans)
                # def f(tasks):
                #     r = itertools.filterfalse(lambda t: (self._check_ranking_function_trans(*t, model)), tasks)
                #     return list(r)

                # invalid_train_term_rand_trans = Miscs.run_mp("filterfalse", train_term_rand_trans, f)

                # elapsed = timeit.default_timer() - start_time
                # mlog.debug("invalid_train_term_rand_trans: {}".format(elapsed * 1000000))

                # arr_train_rand_trans = np.asarray(train_term_rand_trans)
                # start_time = timeit.default_timer()
                # f_check = lambda t: not (self._check_ranking_function_trans(*t, model))
                # bool_index = np.apply_along_axis(f_check, 1, arr_train_rand_trans)
                # arr_train_rand_trans = arr_train_rand_trans[bool_index]
                # elapsed = timeit.default_timer() - start_time
                # mlog.debug("a_train_rand_trans: {}".format(elapsed * 1000000))

                train_term_rand_trans = list(invalid_train_term_rand_trans)
            mlog.debug("train_term_rand_trans: {}".format(len(train_term_rand_trans)))
        mlog.debug("ranking_function_list: {}".format(ranking_function_list))
        return ranking_function_list

    @timeit
    def validate_ranking_functions(self, vloop, vs, rfs):
        _config = self._config
        # ranks_str = '|'.join(['{}'.format(rf) for rf in (rfs[1:] if len(rfs) > 1 else rfs)])
        ranks_str = '|'.join(['{}'.format(rf) for rf in rfs])
        mlog.debug("ranks_str: {}".format(ranks_str))
        vloop_pos = vloop.vloop_pos
        assert vloop_pos, vloop_pos
        
        validate_tmpdir = _config.tmpdir / vloop.vloop_id
        # validator = CPAchecker(validate_tmpdir)
        # validator = UAutomizer(validate_tmpdir)
        # validator = UTaipan(validate_tmpdir)
        validator = Portfolio(validate_tmpdir)
        validate_outf = validator.gen_validate_file(_config.inp, vloop_pos, ranks_str)
        r, cex = validator.prove_reach(vs, validate_outf)
        validator.clean()

        mlog.debug('r: {}'.format(r))
        if r is False and cex:
            mlog.debug('cex.trans_cex: {}'.format(cex.trans_cex))

        # if r is False and cex.trans_cex:
        #     imap = cex.imap
        #     mlog.debug('imap: {}'.format(imap))
        #     rs, _, _ = _config.solver.get_models(cex.symb_cex, _config.n_inps, 
        #                                          # _config.init_inp_decls, 
        #                                          None,
        #                                          settings.use_random_seed)
        #     mlog.debug('n_inps: {}'.format(_config.n_inps))
        #     mlog.debug('rs ({})'.format(len(rs)))
            
        #     cex_models = []
        #     for m in rs:
        #         dm = dict(m)
        #         cex_model = [(v, dm[imap[v]]) for v in _config.inp_decls.names]
        #         cex_models.append(cex_model)
        #     mlog.debug('cex_models ({}): {}'.format(len(cex_models), cex_models))
        #     cex_inps = _config.solver.mk_inps_from_models(cex_models, _config.inp_decls, _config.exe)
        #     mlog.debug("cex_inps: {}".format(cex_inps))
        #     return r, cex_inps
        # else:
        #     return r, None

        if r is False and cex and cex.trans_cex:
            n_rfs = self._infer_ranking_functions_from_trans(vs, cex.trans_cex)
            mlog.debug("n_rfs: {}".format(n_rfs))
            # n_rfs \intersect rfs = \emptyset
            return self.validate_ranking_functions(vloop, vs, rfs + n_rfs) 
        else:
            return r, rfs

        # return r, sym_cex

    @timeit
    def prove_term_vloop(self, itraces, vloop):
        _config = self._config
        mlog.debug('classify_inps: {}'.format(vloop.vloop_id))
        base_term_inps, term_inps, mayloop_inps = vloop.cl.classify_inps(itraces)

        mlog.debug('itraces: {}'.format(len(itraces)))
        Classification.print_inps(itraces)
        mlog.debug('base_term_inps: {}'.format(len(base_term_inps)))
        mlog.debug('term_inps: {}'.format(len(term_inps)))
        mlog.debug('mayloop_inps: {}'.format(len(mayloop_inps)))
            
        # inloop_term_invs = ZConj(_config.dig.infer_from_traces(
        #                 itraces, vloop.inloop_loc, term_inps,
        #                 maxdeg=2))
        # mlog.debug("inloop_term_invs: {}".format(inloop_term_invs))

        # if not _config.inp_decls and not term_inps:
        if not term_inps:
            term_itraces = dict((mayloop_inp, itraces[mayloop_inp]) for mayloop_inp in mayloop_inps)
        else:
            term_itraces = dict((term_inp, itraces[term_inp]) for term_inp in term_inps)
        # mlog.debug('term_itraces: {}'.format(term_itraces))
        vs = _config.inv_decls[vloop.inloop_loc]
        rfs = self.infer_ranking_functions(vloop, vs, term_itraces)
        mlog.debug('validate_ranking_functions: {}'.format(vloop.vloop_id))
        r, n_rfs = self.validate_ranking_functions(vloop, vs, rfs)
        mlog.debug('Termination result ({}): {} ({})'.format(vloop.vloop_id, r, n_rfs))
        return r, n_rfs

    @timeit
    def prove(self):
        _config = self._config
        # vs = _config.inv_decls[_config.inloop_loc]
        # itraces = _config.rand_itraces
        rand_inps = _config.gen_rand_inps()
        itraces = _config.get_traces_from_inps(rand_inps)
        # preloop_term_invs = None
        # while preloop_term_invs is None:
        #     base_term_inps, term_inps, mayloop_inps = _config.cl.classify_inps(itraces)
        #     mlog.debug("base_term_inps: {}".format(len(base_term_inps)))
        #     mlog.debug("term_inps: {}".format(len(term_inps)))
        #     mlog.debug("mayloop_inps: {}".format(len(mayloop_inps)))

        #     preloop_term_invs = _config.dig.infer_from_traces(
        #                             itraces, _config.preloop_loc, term_inps, maxdeg=2)
        #     if preloop_term_invs is None:
        #         rand_inps = gen_rand_inps(_config)
        #         rand_itraces = _config.get_traces_from_inps(rand_inps)
        #         old_itraces_len = len(itraces)
        #         old_itraces_keys = set(itraces.keys())
        #         itraces.update(rand_itraces)
        #         new_itraces_len = len(itraces)
        #         new_itraces_keys = set(itraces.keys())
        #         mlog.debug("new rand inps: {}".format(new_itraces_keys.difference(old_itraces_keys)))
        #         if new_itraces_len <= old_itraces_len:
        #             break
                    
        # mlog.debug("preloop_term_invs: {}".format(preloop_term_invs))
        mlog.debug("itraces: {}".format(len(itraces)))
        # mlog.debug("{}".format(itraces))
        # mlog.debug("term_inps: {}".format(len(term_inps)))

        res = None
        for vloop in _config.vloop_info:
            mlog.debug('Analysing Termination {}'.format(vloop.vloop_id))
            vloop_r, vloop_rfs = self.prove_term_vloop(itraces, vloop)
            if not vloop_r:
                res = None
                break
            res = vloop_r
        # mlog.info('Termination result: {} ({})'.format(r, n_rfs))
        print('Termination result: {}'.format(res))

        # rfs = set()
        # r = None
        # while True:
        #     base_term_inps, term_inps, mayloop_inps = _config.cl.classify_inps(itraces)
        #     term_itraces = dict((term_inp, itraces[term_inp]) for term_inp in term_inps)
        #     candidate_rfs = self.infer_ranking_functions(vs, term_itraces)
        #     if len(candidate_rfs) > 1:
        #         candidate_rfs = candidate_rfs[1:]
        #     old_rfs = rfs
        #     rfs = old_rfs | set(candidate_rfs)
        #     if rfs.issubset(old_rfs): # rfs is not changed
        #         r = None
        #         break
        #     else:
        #         r, cex_inps = self.validate_ranking_functions(vs, list(rfs))
        #         if not r and cex_inps:
        #             itraces = _config.get_traces_from_inps(cex_inps)
        #         else: # Unknown
        #             if not r:
        #                 r = None
        #             break

        # mlog.info('Termination result: {} ({})'.format(r, rfs))

class TNT(object):
    def __init__(self, config):
        self._config = config
        self.t_prover = Term(config)
        self.nt_prover = NonTerm(config)

    def prove(self):
        _config = self._config
        rand_inps = _config.gen_rand_inps()
        itraces = _config.get_traces_from_inps(rand_inps)
        
        res = None
        for vloop in _config.vloop_info:
            mlog.debug('Analysing {}'.format(vloop.vloop_id))
            base_term_inps, term_inps, mayloop_inps = vloop.cl.classify_inps(itraces)
            mlog.debug('base_term_inps: {}'.format(len(base_term_inps)))
            mlog.debug('term_inps: {}'.format(len(term_inps)))
            mlog.debug('mayloop_inps: {}'.format(len(mayloop_inps)))

            if len(mayloop_inps) > 4 * (len(base_term_inps) + len(term_inps)):
                mlog.debug('Proving Non-Termination: {}'.format(vloop.vloop_id))
                valid_rcs, term_itraces_cex = self.nt_prover.prove_nonterm_vloop(vloop)
                if valid_rcs:
                    self.nt_prover.print_valid_rcs(valid_rcs)
                    res = (False, (vloop.vloop_id, valid_rcs))
                    break
                else:
                    mlog.debug('Proving Termination: {}'.format(vloop.vloop_id))
                    mlog.debug('term_itraces_cex: {}'.format(term_itraces_cex))
                    # term_traces = _config.get_traces_from_inps(Inps(set(term_inps)))
                    term_traces = {inp: itraces[inp] for inp in term_inps}
                    term_traces.update(term_itraces_cex)
                    if not term_traces:
                        term_traces = {inp: itraces[inp] for inp in mayloop_inps}
                    t_res, t_rfs = self.t_prover.prove_term_vloop(term_traces, vloop)
                    if not t_res:
                        res = None
                        break
                    else:
                        mlog.debug('{} terminates: {}'.format(vloop.vloop_id, t_rfs))
            else:
                mlog.debug('Proving Termination: {}'.format(vloop.vloop_id))
                # term_traces = _config.get_traces_from_inps(Inps(set(term_inps)))
                term_traces = {inp: itraces[inp] for inp in term_inps}
                if not term_traces:
                    term_traces = {inp: itraces[inp] for inp in mayloop_inps}
                t_res, t_rfs = self.t_prover.prove_term_vloop(term_traces, vloop)
                if t_res:
                    mlog.debug('{} terminates: {}'.format(vloop.vloop_id, t_rfs))
                    res = t_res
                else:
                    mlog.debug('Proving Non-Termination: {}'.format(vloop.vloop_id))
                    valid_rcs, _ = self.nt_prover.prove_nonterm_vloop(vloop)
                    if valid_rcs:
                        # mlog.debug('valid_rcs: {}'.format(valid_rcs))
                        self.nt_prover.print_valid_rcs(valid_rcs)
                        res = (False, (vloop.vloop_id, valid_rcs))
                    else:
                        res = None
                    break

        # mlog.info('Termination result: {} ({})'.format(r, n_rfs))
        print('TNT result: {}'.format(res))