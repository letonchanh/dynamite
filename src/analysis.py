import tempfile
import copy
from pathlib import Path

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

mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

class Setup(object):
    def __init__(self, seed, inp):
        self.seed = seed
        self.inp = inp
        self.is_java_inp = inp.endswith(".java") or inp.endswith(".class")
        self.is_c_inp = inp.endswith(".c")
        self.is_binary_inp = self.is_binary(inp)
        assert (self.is_java_inp or self.is_c_inp or self.is_binary_inp), inp

        self.nInps = 20
        self.preloop_loc = dig_settings.TRACE_INDICATOR + '1' # vtrace1
        self.inloop_loc = dig_settings.TRACE_INDICATOR + '2' # vtrace2
        self.postloop_loc = dig_settings.TRACE_INDICATOR + '3' # vtrace3
        self.transrel_loc = dig_settings.TRACE_INDICATOR + '4' # vtrace4
        self.refinement_depth = 5
        self.tmpdir = Path(tempfile.mkdtemp(dir=dig_settings.tmpdir, prefix="Dig_"))
        self.symstates = None
        self.solver = Solver(self.tmpdir)
        
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
                src = c_src(Path(inp), self.tmpdir)
                exe_cmd = dig_settings.C.C_RUN(exe=src.traceexe)
                self.symstates = self._get_c_symstates_from_src(src)
                ss = self.symstates.ss
                # for loc in ss:
                    # for depth in ss[loc]:
                        # pcs = ss[loc][depth]
                        # mlog.debug("DEPTH {}".format(depth))
                        # mlog.debug("pcs ({}):\n{}".format(len(pcs.lst), pcs))
                
            inp_decls, inv_decls, mainQ_name = src.inp_decls, src.inv_decls, src.mainQ_name
            prog = dig_prog.Prog(exe_cmd, inp_decls, inv_decls)

        mlog.debug("inp_decls ({}): {}".format(type(inp_decls), inp_decls))
        mlog.debug("inv_decls ({}): {}".format(type(inv_decls), inv_decls))

        inloop_inv_decls = inv_decls[self.inloop_loc]
        transrel_inv_decls = Symbs([Symb(s.name + '0', s.typ) for s in inloop_inv_decls] +
                                   [Symb(s.name + '1', s.typ) for s in inloop_inv_decls])
        inv_decls[self.transrel_loc] = transrel_inv_decls

        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self.mainQ_name = mainQ_name
        self.exe = Execution(prog)
        self.dig = Inference(self.inv_decls, self.seed, self.tmpdir)
        self.cl = Classification(self.preloop_loc, self.inloop_loc, self.postloop_loc)

        rand_inps = self.exe.gen_rand_inps(self.nInps)
        self.rand_itraces = self.exe.get_traces(rand_inps)  # itraces: input to dtraces

        self.transrel_pre_inv_decls, self.transrel_pre_sst, self.transrel_post_sst = \
            self.gen_transrel_sst()
        mlog.debug("transrel_pre_inv_decls: {}".format(self.transrel_pre_inv_decls))
        mlog.debug("transrel_pre_sst: {}".format(self.transrel_pre_sst))
        mlog.debug("transrel_post_sst: {}".format(self.transrel_post_sst))

    def _get_c_symstates_from_src(self, src):
        from data.symstates import SymStatesC
        
        exe_cmd = dig_settings.C.C_RUN(exe=src.traceexe)
        inp_decls, inv_decls, mainQ_name = src.inp_decls, src.inv_decls, src.mainQ_name

        symstates = SymStatesC(inp_decls, inv_decls)
        symstates.compute(src.symexefile, src.mainQ_name,
                          src.funname, src.symexedir)
        return symstates

    def _get_loopinfo_symstates(self):
        stem = self._get_stem_symstates()
        loop = self._get_loop_symstates()
        return LoopInfo(stem, loop)

    def _get_stem_symstates(self):
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

    def _get_loop_symstates(self):
        if self.is_c_inp:
            from helpers.src import C as c_src
        
            tmpdir = Path(tempfile.mkdtemp(dir=dig_settings.tmpdir, prefix="Dig_"))
            mlog.debug("Create C source for vloop: {}".format(tmpdir))
            src = c_src(Path(self.inp), tmpdir, mainQ="vloop")
            symstates = self._get_c_symstates_from_src(src)
            ss = symstates.ss
        else:
            raise NotImplementedError

        inp_decls, inv_decls = src.inp_decls, src.inv_decls
        mlog.debug("vloop inp_decls: {}".format(inp_decls))
        mlog.debug("vloop inv_decls: {}".format(inv_decls))
        
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
                inloop_vars = Z3.get_vars(inloop_fst_symstate.slocal).union(Z3.get_vars(inloop_snd_symstate.slocal))
                inloop_inv_vars = inv_decls[self.inloop_loc].exprs(settings.use_reals)
                inloop_ex_vars = inloop_vars.difference(inloop_inv_vars)
                mlog.debug("inloop_ex_vars: {}".format(inloop_ex_vars))
                inloop_fst_slocal = z3.substitute(inloop_fst_symstate.slocal, self.transrel_pre_sst)
                inloop_snd_slocal = z3.substitute(inloop_snd_symstate.slocal, self.transrel_post_sst)
                mlog.debug("inloop_fst_slocal: {}".format(inloop_fst_slocal))
                mlog.debug("inloop_snd_slocal: {}".format(inloop_snd_slocal))
                inloop_trans_f = z3.Exists(list(inloop_ex_vars), z3.And(inloop_fst_slocal, inloop_snd_slocal))
                loop_transrel = Z3.qe(inloop_trans_f)
                mlog.debug("loop_transrel: {}".format(loop_transrel))

                loop_cond = Z3.qe(z3.Exists(list(inloop_ex_vars), 
                                                  z3.And(inloop_fst_symstate.pc, inloop_fst_symstate.slocal)))
                mlog.debug("loop_cond: {}".format(loop_cond))

                return Loop(inp_decls, loop_cond, loop_transrel)
        return None

    def _get_loopinfo_traces(self):
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
        loopinfo = self._get_loopinfo_symstates()
        if loopinfo is None:
            loopinfo = self._get_loopinfo_traces()
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

            # rand_inps = exe.gen_rand_inps(self.nInps)
            # rand_itraces = exe.get_traces(rand_inps)
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
            #         models, _ = Solver.get_models(uncovered_f, 
            #                                       self.nInps, self.tmpdir, 
            #                                       settings.use_random_seed)
            #         mlog.debug("uncovered models: {}".format(models))
            #         if isinstance(models, list) and models:
            #             ninps = Solver.mk_inps_from_models(models, self.inp_decls.exprs((settings.use_reals)), exe)
            #             mlog.debug("uncovered inps: {}".format(ninps))
            #             mlog.debug("Starting get_traces")
            #             nitraces = exe.get_traces(ninps)
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
        transrel_pre_inv_decls = Symbs([Symb(s.name + '0', s.typ) for s in inloop_inv_decls])
        transrel_pre_inv_exprs = transrel_pre_inv_decls.exprs(settings.use_reals)
        transrel_post_inv_decls = Symbs([Symb(s.name + '1', s.typ) for s in inloop_inv_decls])
        transrel_post_inv_exprs = transrel_post_inv_decls.exprs(settings.use_reals)

        return transrel_pre_inv_exprs, \
               list(zip(inloop_inv_exprs, transrel_pre_inv_exprs)), \
               list(zip(inloop_inv_exprs, transrel_post_inv_exprs))

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

    def verify(self, rcs, precond):
        assert rcs is None or isinstance(rcs, ZFormula), rcs
        _config = self._config

        if rcs is None:
            sCexs = []
            if precond is None:
                mlog.debug("verify: Using random inps")
                rand_itraces = _config.rand_itraces
            else:
                rs, _ = _config.solver.get_models(precond, _config.nInps, settings.use_random_seed)
                if isinstance(rs, list) and rs:
                    mlog.debug("verify: Using random inps from precond")
                    rs = _config.solver.mk_inps_from_models(
                                    rs, _config.inp_decls.exprs((settings.use_reals)), _config.exe)
                    rand_itraces = _config.exe.get_traces(rs)
                else:
                    mlog.debug("verify: Using random inps")
                    rand_itraces = _config.rand_itraces
            sCexs.append((None, rand_itraces)) # invalid_rc, cexs
            return False, sCexs
        elif not rcs:
            return True, None 
        else:
            # assert rcs, rcs
            rcs_l = z3.substitute(rcs.expr(), _config.transrel_pre_sst)
            loop_transrel = self.loop.transrel
            rcs_transrel = z3.And(rcs_l, loop_transrel)
            mlog.debug("rcs_l: {}".format(rcs_l))
            mlog.debug("loop_transrel: {}".format(loop_transrel))

            if _config.is_c_inp:
                init_symvars_prefix = dig_settings.C.CIVL_INIT_SYMVARS_PREFIX

            def _check(rc):
                rc_r = z3.substitute(rc, _config.transrel_post_sst)
                mlog.debug("rc: {}".format(rc))
                # f = z3.Not(z3.Implies(z3.And(rcs_l, transrel_expr), rc_r))
                f = z3.And(rcs_transrel, z3.Not(rc_r)) # (x0, y0) -> (x1, y1)
                f = z3.substitute(f, [(x0, x) for (x, x0) in _config.transrel_pre_sst]) # (x, y) -> (x1, y1)
                init_f = self.stem.get_initial_cond(f, _config) # stem: (X_xx, X_yy) -> (x, y)
                # mlog.debug("f: {}".format(f))
                # mlog.debug("init_f: {}".format(init_f))
                # using_random_seed = True
                rs, _ = _config.solver.get_models(init_f, _config.nInps, settings.use_random_seed)
                if rs is None:
                    mlog.debug("rs: unknown")
                elif rs is False:
                    mlog.debug("rs: unsat")
                else:
                    if isinstance(rs, list) and rs:
                        rs = [[(x[len(init_symvars_prefix):], v) 
                                if x.startswith(init_symvars_prefix) 
                                else (x, v)
                               for (x, v) in r] for r in rs]
                        mlog.debug("rs: sat ({} models)\n{}".format(len(rs), rs))
                        rs = _config.solver.mk_inps_from_models(
                                    rs, _config.inp_decls.exprs(settings.use_reals), _config.exe)
                return rs

            chks = [(rc, _check(rc)) for rc in rcs]
            if all(rs is False for _, rs in chks):
                return True, None  # valid
            else:
                sCexs = []
                for rc, rs in chks:
                    if rs is None:
                        return False, None  # unknown
                    elif rs:  # sat
                        assert isinstance(rs, Inps), rs
                        assert len(rs) > 0
                        itraces = _config.exe.get_traces(rs)
                        # rcs.remove(rc)
                        sCexs.append((rc, itraces))
                return False, sCexs  # invalid with a set of new Inps

    def strengthen(self, rcs, invalid_rc, itraces):
        _config = self._config
        base_term_inps, term_inps, mayloop_inps = _config.cl.classify_inps(itraces)
        mlog.debug("base_term_inps: {}".format(len(base_term_inps)))
        mlog.debug("term_inps: {}".format(len(term_inps)))
        mlog.debug("mayloop_inps: {}".format(len(mayloop_inps)))

        mayloop_invs = ZConj(_config.dig.infer_from_traces(
            itraces, _config.inloop_loc, mayloop_inps))
        mlog.debug("mayloop_invs: {}".format(mayloop_invs))
        if rcs is None:
            return mayloop_invs
        elif mayloop_invs and rcs.implies(mayloop_invs):
            return mayloop_invs
        else:
            # base_term_pre = ZConj(_config.dig.infer_from_traces(
            #     itraces, _config.preloop_loc, base_term_inps))
            term_invs = ZConj(_config.dig.infer_from_traces(
                                itraces, _config.inloop_loc, term_inps))
            # mlog.debug("base_term_pre: {}".format(base_term_pre))
            mlog.debug("term_invs: {}".format(term_invs))
            term_traces = []
            for term_inp in term_inps:
                term_traces.append(itraces[term_inp])
            self.tCexs.append((term_invs, term_traces))
            # term_cond = z3.Or(base_term_pre.expr(), term_invs.expr())
            term_cond = term_invs.expr()
            simplified_term_cond = Z3.simplify(term_cond)
            cnf_term_cond = Z3.to_cnf(simplified_term_cond)
            mlog.debug("simplified_term_cond: {}".format(simplified_term_cond))
            mlog.debug("cnf_term_cond: {}".format(cnf_term_cond))
            dnf_neg_term_cond = Z3.to_nnf(z3.Not(cnf_term_cond))
            mlog.debug("dnf_neg_term_cond: {}".format(dnf_neg_term_cond))
            nrcs = copy.deepcopy(rcs)
            if invalid_rc is not None:
                nrcs.remove(invalid_rc)
            mlog.debug("rcs: {}".format(rcs))
            mlog.debug("invalid_rc: {}".format(invalid_rc))
            mlog.debug("nrcs: {}".format(nrcs))
            nrcs.add(dnf_neg_term_cond)
            return nrcs

    def prove(self, precond):
        _config = self._config
        validRCS = []

        if self.stem is None or self.loop is None:
            return []
        else:
            # candidate rcs, depth, ancestors
            candidateRCS = [(None, 0, [])]
            while candidateRCS:
                mlog.debug("candidateRCS: {}".format(candidateRCS))
                rcs, depth, ancestors = candidateRCS.pop()
                mlog.debug("PROVE_NT DEPTH {}: {}".format(depth, rcs))
                if depth < _config.refinement_depth:
                    chk, sCexs = self.verify(rcs, precond)
                    # mlog.debug("sCexs: {}".format(sCexs))
                    if chk and not rcs.is_unsat():
                        validRCS.append((rcs, ancestors))
                    elif sCexs is not None:
                        for invalid_rc, cexs in sCexs:
                            nrcs = self.strengthen(rcs, invalid_rc, cexs)
                            assert nrcs is not None, nrcs
                            nancestors = copy.deepcopy(ancestors)
                            nancestors.append((depth, rcs))
                            candidateRCS.append((nrcs, depth+1, nancestors))
            for (tInvs, tTraces) in self.tCexs:
                mlog.debug("tCex: {}".format(tInvs))
            return validRCS

class Term(object):
    def __init__(self, config):
        self._config = config
        self.ntCexs = []

    def prove(self):
        _config = self._config
        itraces = _config.rand_itraces
        preloop_term_invs = None
        while preloop_term_invs is None:
            base_term_inps, term_inps, mayloop_inps = _config.cl.classify_inps(itraces)
            mlog.debug("base_term_inps: {}".format(len(base_term_inps)))
            mlog.debug("term_inps: {}".format(len(term_inps)))
            mlog.debug("mayloop_inps: {}".format(len(mayloop_inps)))

            preloop_term_invs = _config.dig.infer_from_traces(
                                    itraces, _config.preloop_loc, term_inps, maxdeg=2)
            if preloop_term_invs is None:
                rand_inps = _config.exe.gen_rand_inps(_config.nInps)
                rand_itraces = _config.exe.get_traces(rand_inps)
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

        # Generate ranking function template
        vs = _config.inv_decls[_config.inloop_loc].names
        terms = Miscs.get_terms([sage.all.var(v) for v in vs], 1)
        rnk_template, uks = Miscs.mk_template(terms, None, retCoefVars=True)
        mlog.debug("rnk_template: {}".format(rnk_template))
        mlog.debug("uks: {}".format(uks))

        for term_inp in term_inps:
            mlog.debug("term_inp: {}".format(term_inp))
            term_traces = itraces[term_inp]
            inloop_term_traces = term_traces[_config.inloop_loc]
            postloop_term_traces = term_traces[_config.postloop_loc]
            inloop_rnk_terms = [rnk_template.subs(t.mydict) for t in inloop_term_traces]
            postloop_rnk_terms = [rnk_template.subs(t.mydict) for t in postloop_term_traces]
            rnk_trans = zip(inloop_rnk_terms, inloop_rnk_terms[1:] + postloop_rnk_terms[:1])
            for (r1, r2) in rnk_trans:
                desc_cond = sage.all.operator.gt(r1, r2)
                bnd_cond = sage.all.operator.ge(r1, 0)
                # mlog.debug("desc_cond: {}".format(desc_cond))
                # mlog.debug("bnd_cond: {}".format(bnd_cond))

        
