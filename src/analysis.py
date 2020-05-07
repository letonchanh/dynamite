import tempfile
import copy
import random
import itertools
import math
import os
import sage
from pathlib import Path
from collections import defaultdict 
# from numba import njit 
# import numpy as np

import settings as dig_settings
import helpers.vcommon as dig_common_helpers
import helpers.src as dig_src
import data.prog as dig_prog
from data.prog import Symb, Symbs
from data.traces import Traces
from helpers.miscs import Z3, Miscs
# from bin import Bin

from utils import settings
from utils.logic import *
from utils.loop import *
from lib import *
from solver import ZSolver, Z3Py, Z3Bin, PySMT
from validate import Validator, CPAchecker, UAutomizer, Portfolio

mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

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
                mlog.debug("trans_rmsg: {}".format(trans_rmsg))

                cg = self._parse_call_graph(trans_rmsg)
                mlog.debug("cg: {}".format(cg))

                self.trans_inp = trans_outf
                self.cg = cg

                vloop_pos = self._get_vloop_pos(self.vloop)
                mlog.debug('vloop_pos: {}'.format(vloop_pos))

                self.preloop_loc = dig_settings.TRACE_INDICATOR + '1' + '_' + vloop_pos # vtrace1
                self.inloop_loc = dig_settings.TRACE_INDICATOR + '2' + '_' + vloop_pos # vtrace2
                self.postloop_loc = dig_settings.TRACE_INDICATOR + '3' + '_' + vloop_pos # vtrace3
                self.transrel_loc = dig_settings.TRACE_INDICATOR 

                src = c_src(Path(self.trans_inp), self.tmpdir)
                exe_cmd = dig_settings.C.C_RUN(exe=src.traceexe)
                if settings.prove_nonterm:
                    try:
                        mlog.debug("Get symstates for proving NonTerm (prove_nonterm={})".format(settings.prove_nonterm))
                        self.symstates = self._get_c_symstates_from_src(src)
                    except Exception as e:
                        mlog.debug("Get symstates for proving NonTerm: {}".format(e))
                        raise e
                    # ss = self.symstates.ss
                    # for loc in ss:
                        # for depth in ss[loc]:
                            # pcs = ss[loc][depth]
                            # mlog.debug("DEPTH {}".format(depth))
                            # mlog.debug("pcs ({}):\n{}".format(len(pcs.lst), pcs))
                else:
                    pass
                
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

        self.transrel_pre_inv_decls, self.transrel_pre_sst, \
            self.transrel_post_sst, transrel_inv_decls = self.gen_transrel_sst()
        self.inv_decls[self.transrel_loc] = transrel_inv_decls
        mlog.debug("transrel_pre_inv_decls: {}".format(self.transrel_pre_inv_decls))
        mlog.debug("transrel_pre_sst: {}".format(self.transrel_pre_sst))
        mlog.debug("transrel_post_sst: {}".format(self.transrel_post_sst))

        self.exe = Execution(prog)
        self.dig = Inference(self.inv_decls, self.seed, self.tmpdir)
        self.cl = Classification(self.preloop_loc, self.inloop_loc, self.postloop_loc)

        # mlog.debug("generate random inputs")
        # rand_inps = self.exe.gen_rand_inps(self.n_inps)
        # mlog.debug("get traces from random inputs")
        # self.rand_itraces = self.exe.get_traces_from_inps(rand_inps)  # itraces: input to dtraces

    @property
    def vloop(self):
        vloops = self.cg[dig_settings.MAINQ_FUN]
        assert len(vloops) >= 1, vloops
        if len(vloops) > 1:
            raise NotImplementedError
        else:
            vloop = vloops[0]
        return vloop

    def _get_vloop_pos(self, vloop_name):
        vloop_prefix = settings.VLOOP_FUN + '_'
        if vloop_name.startswith(vloop_prefix):
            return vloop_name[len(vloop_prefix):]
        else:
            return None

    def _get_c_symstates_from_src(self, src):
        from data.symstates import SymStatesC
        
        # exe_cmd = dig_settings.C.C_RUN(exe=src.traceexe)
        inp_decls, inv_decls, mainQ_name = src.inp_decls, src.inv_decls, src.mainQ_name

        symstates = SymStatesC(inp_decls, inv_decls)
        symstates.compute(src.symexefile, src.mainQ_name,
                          src.funname, src.symexedir)
        # mlog.debug("symstates: {}".format(symstates.ss))
        return symstates

    def _get_loopinfo_from_symstates(self):
        stem = self._get_stem_from_symstates()
        loop = self._get_loop_from_symstates()
        return LoopInfo(stem, loop)

    def _get_stem_from_symstates(self):
        assert self.symstates, self.symstates

        ss = self.symstates.ss
        if self.preloop_loc in ss:
            preloop_symstates = ss[self.preloop_loc]
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
        return None

    def _strip_ptr_loop_params(self, symbs):
        symbs = [Symb(s.name.replace(settings.CIL.PTR_VARS_PREFIX, ''), 'I') if settings.CIL.PTR_VARS_PREFIX in s.name and s.typ == 'P' 
                 else s for s in symbs]
        return Symbs(symbs)

    def _get_loop_from_symstates(self):
        if self.is_c_inp:
            from helpers.src import C as c_src

            vloop = self._get_vloop()
        
            tmpdir = Path(tempfile.mkdtemp(dir=dig_settings.tmpdir, prefix="Dig_"))
            mlog.debug("Create C source for {}: {}".format(vloop, tmpdir))
            src = c_src(Path(self.trans_inp), tmpdir, mainQ=vloop)
            symstates = self._get_c_symstates_from_src(src)
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
        
        if self.inloop_loc in ss:
            inloop_symstates = ss[self.inloop_loc]
            inloop_ss_depths = sorted(inloop_symstates.keys())
            inloop_fst_symstate = None
            inloop_snd_symstate = None
            while (inloop_fst_symstate is None or inloop_snd_symstate is None) and inloop_ss_depths:
                depth = inloop_ss_depths.pop()
                symstates = inloop_symstates[depth]
                # mlog.debug("DEPTH {}".format(depth))
                # mlog.debug("symstates ({}):\n{}".format(len(symstates.lst), symstates))
                if len(symstates.lst) >= 2:
                    inloop_fst_symstate = symstates.lst[0]
                    inloop_snd_symstate = symstates.lst[1]
            
            if inloop_fst_symstate and inloop_snd_symstate:
                # Get loop's condition and transition relation
                inloop_fst_slocal = z3.substitute(inloop_fst_symstate.slocal, self.transrel_pre_sst)
                inloop_snd_slocal = z3.substitute(inloop_snd_symstate.slocal, self.transrel_post_sst)
                mlog.debug("inloop_fst_slocal: {}".format(inloop_fst_slocal))
                mlog.debug("inloop_snd_slocal: {}".format(inloop_snd_slocal))
                inloop_vars = Z3.get_vars(inloop_fst_symstate.slocal).union(Z3.get_vars(inloop_snd_symstate.slocal))
                inloop_inv_vars = inv_decls[self.inloop_loc].exprs(settings.use_reals)
                inloop_ex_vars = inloop_vars.difference(inloop_inv_vars)
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
        lines = [l.split(':') for l in msg.split('\n')
                 if l.startswith(dig_settings.MAINQ_FUN)
                 or l.startswith(settings.VLOOP_FUN)]
        cg = defaultdict(list)

        for caller, s in lines:
            caller = caller.strip()
            for callee in s.split(','):
                cg[caller].append(callee.strip())
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

    def get_loopinfo(self):
        loopinfo = self._get_loopinfo_from_symstates()
        if loopinfo is None:
            loopinfo = self._get_loopinfo_from_traces()
        return loopinfo

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

    def gen_transrel_sst(self):
        inloop_inv_decls = self.inv_decls[self.inloop_loc]
        inloop_inv_exprs = inloop_inv_decls.exprs(settings.use_reals)
        transrel_pre_inv_decls = [dig_prog.Symb(s.name + '0', s.typ) for s in inloop_inv_decls]
        transrel_pre_inv_exprs = dig_prog.Symbs(transrel_pre_inv_decls).exprs(settings.use_reals)
        transrel_post_inv_decls = [dig_prog.Symb(s.name + '1', s.typ) for s in inloop_inv_decls]
        transrel_post_inv_exprs = dig_prog.Symbs(transrel_post_inv_decls).exprs(settings.use_reals)

        transrel_inv_decls = dig_prog.Symbs(transrel_pre_inv_decls + transrel_post_inv_decls)

        return transrel_pre_inv_exprs, \
               list(zip(inloop_inv_exprs, transrel_pre_inv_exprs)), \
               list(zip(inloop_inv_exprs, transrel_post_inv_exprs)), \
               transrel_inv_decls

    def is_binary(self, fn):
        import subprocess
        mime = subprocess.Popen(["file", "--mime", fn], stdout=subprocess.PIPE).communicate()[0]
        return b"application/x-executable" in mime

class NonTerm(object):
    def __init__(self, config):
        self._config = config
        loopinfo = config.get_loopinfo()
        self.stem = loopinfo.stem
        self.loop = loopinfo.loop
        self.tCexs = []

    def verify(self, rcs):
        assert isinstance(rcs, ZFormula), rcs
        assert not rcs.is_unsat(), rcs
        _config = self._config

        if not rcs:
            return True, None 
        else:
            # assert rcs, rcs
            init_symvars_prefix = _config.init_symvars_prefix

            loop_transrel = self.loop.transrel
            loop_cond = self.loop.cond

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
            init_transrel_rcs = ZFormula.substitue(labeled_rcs, _config.transrel_pre_sst)
            init_transrel_rcs.add(loop_transrel)
            init_transrel_rcs.add(self.stem.cond)
            init_transrel_rcs.add(self.stem.transrel)
            mlog.debug("init_transrel_rcs: {}".format(init_transrel_rcs))

            # Unreachable recurrent set
            if init_transrel_rcs.is_unsat():
                return False, None, None

            dg = defaultdict(list)
            def _check(rc):
                rc_label = label_d[rc]
                mlog.debug("rc: {}:{}".format(rc, rc_label))
                # init_transrel_rcs is sat
                init_f = copy.deepcopy(init_transrel_rcs)
                rc_r = z3.substitute(rc, _config.transrel_post_sst)
                init_f.add(z3.Not(rc_r))
                mlog.debug("rc_r: {}".format(rc_r))
                mlog.debug("init_f: {}".format(init_f))
                
                rs, _, unsat_core = _config.solver.get_models(init_f, _config.n_inps, 
                                                              _config.init_inp_decls, 
                                                              settings.use_random_seed)
                if rs is None:
                    mlog.debug("rs: unknown")
                elif rs is False:
                    mlog.debug("rs: unsat")
                    mlog.debug("unsat_core: {}".format(unsat_core))
                    assert unsat_core is not None, unsat_core
                    dg[rc_label] = unsat_core
                else:
                    # isinstance(rs, list) and rs:
                    init_rs = []
                    init_symvars_prefix_len = len(init_symvars_prefix)
                    for r in rs:
                        init_r = []
                        for (x, v) in r:
                            if x.startswith(init_symvars_prefix):
                                init_r.append((x[init_symvars_prefix_len:], v))
                        if init_r:
                            init_rs.append(init_r)

                    mlog.debug("init_rs: sat ({} models)".format(len(init_rs)))
                    rs = _config.solver.mk_inps_from_models(
                                init_rs, _config.inp_decls, _config.exe)
                    # mlog.debug("rs: {}".format(rs))
                return rs

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
                        return False, None  # unknown
                    elif rs:  # sat
                        assert isinstance(rs, Inps), rs
                        assert len(rs) > 0
                        itraces = _config.exe.get_traces_from_inps(rs)
                        sCexs.append((rc, itraces))
                return False, sCexs, mds  # invalid with a set of new Inps

    def strengthen(self, rcs, invalid_rc, itraces):
        _config = self._config
        base_term_inps, term_inps, mayloop_inps = _config.cl.classify_inps(itraces)
        mlog.debug("base_term_inps: {}".format(len(base_term_inps)))
        mlog.debug("term_inps: {}".format(len(term_inps)))
        mlog.debug("mayloop_inps: {}".format(len(mayloop_inps)))
        mlog.debug("rcs: {}".format(rcs))

        mayloop_invs = ZConj(_config.dig.infer_from_traces(
                                itraces, _config.inloop_loc, mayloop_inps))
        mlog.debug("mayloop_invs: {}".format(mayloop_invs))

        term_invs = ZConj(_config.dig.infer_from_traces(
                            itraces, _config.inloop_loc, term_inps, maxdeg=1))
        mlog.debug("term_invs: {}".format(term_invs))

        term_traces = []
        for term_inp in term_inps:
            term_traces.append(itraces[term_inp])
        self.tCexs.append((term_invs, term_traces))
        
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
        for (_, d, _) in rcs:
            stat[d] += 1
        mlog.debug("stat ({} total): {}".format(len(rcs), stat))

    def prove(self):
        _config = self._config
        validRCS = []

        if self.stem is None or self.loop is None:
            mlog.debug("No loop information: stem={}, loop={}".format(self.stem, self.loop))
            return []
        else:
            # candidate rcs, depth, ancestors
            candidateRCS = [(ZConj([self.loop.cond]), 0, [])]
            while candidateRCS:
                # mlog.debug("candidateRCS: {}".format(len(candidateRCS)))
                self._stat_candidate_rcs(candidateRCS)
                # use 0 for queue
                rcs, depth, ancestors = candidateRCS.pop(0)
                mlog.debug("PROVE_NT DEPTH {}: {}".format(depth, rcs))
                if rcs.is_unsat():
                    continue

                if depth < settings.max_nonterm_refinement_depth:
                    chk, sCexs, mds = self.verify(rcs)
                    # mlog.debug("sCexs: {}".format(sCexs))
                    if mds and len(mds) < len(rcs):
                        # mds is a valid recurrent set which is smaller (weaker) than rcs
                        nancestors = copy.deepcopy(ancestors)
                        nancestors.append((depth, rcs))
                        validRCS.append((mds, nancestors))
                    
                    if chk:
                        validRCS.append((rcs, ancestors))
                        # return the first valid rcs
                        # return validRCS
                    elif sCexs is not None:
                        for invalid_rc, cexs in sCexs:
                            nrcs = self.strengthen(rcs, invalid_rc, cexs)
                            # assert nrcs, nrcs
                            for nrc in nrcs:
                                nancestors = copy.deepcopy(ancestors)
                                nancestors.append((depth, rcs))
                                candidateRCS.append((nrc, depth+1, nancestors))
            for (tInvs, tTraces) in self.tCexs:
                mlog.debug("tCex: {}".format(tInvs))
            return validRCS

class Term(object):
    def __init__(self, config):
        self._config = config
        self.ntCexs = []
        self.MAX_TRANS_NUM = 50

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

    def infer_ranking_functions(self, vs, term_itraces):
        _config = self._config
        
        # Create and randomly pick terminating transitive closure transitions 
        # input: (t1: {x=2, y=3, z=5}, t2, t3) -> [(t1, t2), (t1, t3), (t2, t3)]
        train_rand_trans = []
        for term_inp in term_itraces:
            term_traces = term_itraces[term_inp]
            inloop_term_traces = term_traces[_config.inloop_loc]
            postloop_term_traces = term_traces[_config.postloop_loc]

            assert inloop_term_traces, inloop_term_traces
            assert postloop_term_traces, postloop_term_traces

            loop_term_traces = inloop_term_traces + postloop_term_traces[:1]

            trans_idx = list(itertools.combinations(range(len(loop_term_traces)), 2))
            random.shuffle(trans_idx)
            trans_idx_len = len(trans_idx)
            splitter_idx = min(self.MAX_TRANS_NUM, trans_idx_len)
            # splitter_idx = trans_idx_len
            # mlog.debug("splitter_idx: {}".format(splitter_idx))
            for (i1, i2) in trans_idx[:splitter_idx]:
                assert i1 < i2, (i1, i2)
                rand_trans = (loop_term_traces[i1], loop_term_traces[i2])
                # mlog.debug("rand_trans: {} -> {}: {}".format(i1, i2, rand_trans))
                train_rand_trans.append(rand_trans)
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
            model = self._infer_ranking_function_trans(t1, t2, opt)
            mlog.debug("model: {}".format(model))
            if model:
                rf = model.evaluate(rnk_ztemplate)
                ranking_function_list.append(rf)
                mlog.debug("t1: {}".format(t1))
                mlog.debug("t2: {}".format(t2))
                mlog.debug("rf: {}".format(rf))

                # start_time = timeit.default_timer()
                # l_train_rand_trans = [(t1, t2) for (t1, t2) in train_term_rand_trans 
                #                               if not (self._check_ranking_function_trans(t1, t2, model))]
                # elapsed = timeit.default_timer() - start_time
                # mlog.debug("l_train_rand_trans: {}".format(elapsed * 1000000))
                
                # start_time = timeit.default_timer()
                invalid_train_term_rand_trans = itertools.filterfalse(lambda t: (self._check_ranking_function_trans(*t, model)),
                                                                      train_term_rand_trans)
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

    def validate_ranking_functions(self, vs, rfs):
        _config = self._config
        # ranks_str = '|'.join(['{}'.format(rf) for rf in (rfs[1:] if len(rfs) > 1 else rfs)])
        ranks_str = '|'.join(['{}'.format(rf) for rf in rfs])
        mlog.debug("ranks_str: {}".format(ranks_str))
        vloop_pos = _config._get_vloop_pos(_config.vloop)
        assert vloop_pos, vloop_pos
        
        validator = CPAchecker(_config.tmpdir)
        # validator = UAutomizer(_config.tmpdir)
        # validator = Portfolio(_config.tmpdir)
        validate_outf = validator.gen_validate_file(_config.inp, vloop_pos, ranks_str)
        r, cex = validator.prove_reach(vs, validate_outf)
        validator.clean()

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

        if r is False and cex.trans_cex:
            n_rfs = self._infer_ranking_functions_from_trans(vs, cex.trans_cex)
            mlog.debug("n_rfs: {}".format(n_rfs))
            # n_rfs \intersect rfs = \emptyset
            return self.validate_ranking_functions(vs, rfs + n_rfs) 
        else:
            return r, rfs

        # return r, sym_cex

    def prove(self):
        _config = self._config
        vs = _config.inv_decls[_config.inloop_loc]
        # itraces = _config.rand_itraces
        rand_inps = _config.exe.gen_rand_inps(_config.n_inps)
        itraces = _config.exe.get_traces_from_inps(rand_inps)
        preloop_term_invs = None
        while preloop_term_invs is None:
            base_term_inps, term_inps, mayloop_inps = _config.cl.classify_inps(itraces)
            mlog.debug("base_term_inps: {}".format(len(base_term_inps)))
            mlog.debug("term_inps: {}".format(len(term_inps)))
            mlog.debug("mayloop_inps: {}".format(len(mayloop_inps)))

            preloop_term_invs = _config.dig.infer_from_traces(
                                    itraces, _config.preloop_loc, term_inps, maxdeg=2)
            if preloop_term_invs is None:
                rand_inps = _config.exe.gen_rand_inps(_config.n_inps)
                rand_itraces = _config.exe.get_traces_from_inps(rand_inps)
                old_itraces_len = len(itraces)
                old_itraces_keys = set(itraces.keys())
                itraces.update(rand_itraces)
                new_itraces_len = len(itraces)
                new_itraces_keys = set(itraces.keys())
                mlog.debug("new rand inps: {}".format(new_itraces_keys.difference(old_itraces_keys)))
                if new_itraces_len <= old_itraces_len:
                    break
                    
        mlog.debug("preloop_term_invs: {}".format(preloop_term_invs))
        mlog.debug("itraces: {}".format(len(itraces)))
        mlog.debug("term_inps: {}".format(len(term_inps)))
        inloop_term_invs = ZConj(_config.dig.infer_from_traces(
                            itraces, _config.inloop_loc, term_inps,
                            maxdeg=2))
        
        mlog.debug("inloop_term_invs: {}".format(inloop_term_invs))

        term_itraces = dict((term_inp, itraces[term_inp]) for term_inp in term_inps)
        rfs = self.infer_ranking_functions(vs, term_itraces)
        r, n_rfs = self.validate_ranking_functions(vs, rfs)
        # mlog.info('Termination result: {} ({})'.format(r, n_rfs))
        print('Termination result: {} ({})'.format(r, n_rfs))

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
        #             itraces = _config.exe.get_traces_from_inps(cex_inps)
        #         else: # Unknown
        #             if not r:
        #                 r = None
        #             break

        # mlog.info('Termination result: {} ({})'.format(r, rfs))

        """
        ProveT(P):
            P_instr = Instrument(P)
            inps = GenRandomInps(P)
            ranking_function_set = {}
            do {
                \pi = Execute(P, inps)
                \pi_base, \pi_term, \pi_mayloop = Partition(\pi)
                new_ranking_functions = InferRankingFunction(P_instr, \pi_term)
                if new_ranking_functions is non-empty:
                    ranking_function_set = ranking_function_set U new_ranking_functions
                    r, cex = validate_ranking_functions(P, ranking_function_set)
                    if r:
                        return r, ranking_function_sets
                    else:
                        inps = GuessInput(cex)
            } while (ranking_function_sets.unchanged)

        InferRankingFunction(P_instr, \pi_term):
            vloop_params = GetParams(P_instr)
            # x, y, z
            # u_0 + u_1*x + u_2*y + u_3*z
            ranking_function_template = GenRankingFunctionTemplate(P_instr)
            transitive_closure_transitions = {}
            for each snap_shot in \pi_term:
                transitive_closure_transitions = transitive_closure_transitions U GenTransitiveClosureTransitions(snap_shot)
            ranking_function_set = {}
            while transitive_closure_transitions is non-empty:
                (s1, s2) = RandomlyPick(transitive_closure_transitions)
                t1 = ranking_function_template(s1)
                t2 = ranking_function_template(s2)
                ranking_function = SolveTemplate(ranking_function_template, {t1>t2, t1>=0})
                ranking_function_set = ranking_function_set U {ranking_function}
                transitive_closure_transitions.filter(t: NotSatisfied(t, ranking_function))
            return ranking_function_set
        """