import tempfile
import copy
import bin
from utils import settings
from utils.logic import *
from lib import *
from pathlib import Path

import settings as dig_settings
import helpers.vcommon as dig_common_helpers
import helpers.src as dig_src
import data.prog as dig_prog
from data.prog import Symb, Symbs
from helpers.miscs import Z3, Miscs
from bin import Bin

mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

class Setup(object):
    def __init__(self, seed, inp):
        is_java_inp = inp.endswith(".java") or inp.endswith(".class")
        is_c_inp = inp.endswith(".c")
        is_binary_inp = self.is_binary(inp)
        assert (is_java_inp or is_c_inp or is_binary_inp), inp

        self.nInps = 100
        self.preloop_loc = dig_settings.TRACE_INDICATOR + '1' # vtrace1
        self.inloop_loc = dig_settings.TRACE_INDICATOR + '2' # vtrace2
        self.postloop_loc = dig_settings.TRACE_INDICATOR + '3' # vtrace3
        self.transrel_loc = dig_settings.TRACE_INDICATOR + '4' # vtrace4
        self.refinement_depth = 5
        self.tmpdir = Path(tempfile.mkdtemp(dir=dig_settings.tmpdir, prefix="Dig_"))
        self.symstates = None
        
        if is_binary_inp:
            prog = Bin(self.inloop_loc, inp)
            inp_decls, inv_decls, mainQ_name = prog.parse()
        else:
            if is_java_inp:
                from helpers.src import Java as java_src
                src = java_src(Path(inp), self.tmpdir)
                exe_cmd = dig_settings.Java.JAVA_RUN(tracedir=src.tracedir, funname=src.funname)
            else:
                from helpers.src import C as c_src
                src = c_src(Path(inp), self.tmpdir)
                exe_cmd = dig_settings.C.C_RUN(exe=src.traceexe)
                import alg
                dig = alg.DigSymStatesC(inp)
                ss = dig.symstates.ss
                # mlog.debug("SymStates ({}): {}".format(type(ss), ss))
                # for loc, depthss in ss.items():
                #     for depth, states in depthss.items():
                #         for s in states.lst:
                #             mlog.debug("SymState ({}, {}):\n{}\n{}".format(type(s), s in states, s, s.expr))
                self.symstates = ss

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
        self.dig = Inference(self.inv_decls, seed)
        self.cl = Classification(self.preloop_loc, self.inloop_loc, self.postloop_loc)

        rand_inps = self.exe.gen_rand_inps(self.nInps)
        self.rand_itraces = self.exe.get_traces(rand_inps)  # itraces: input to dtraces

        self.transrel_pre_inv_decls, self.transrel_pre_sst, self.transrel_post_sst = \
            self.gen_transrel_sst()
        mlog.debug("transrel_pre_inv_decls: {}".format(self.transrel_pre_inv_decls))
        mlog.debug("transrel_pre_sst: {}".format(self.transrel_pre_sst))
        mlog.debug("transrel_post_sst: {}".format(self.transrel_post_sst))

    def _infer_transrel_symstates(self):
        ss = self.symstates
        if self.inloop_loc in ss:
            inloop_symstates = ss[self.inloop_loc]
            inloop_ss_depths = sorted(inloop_symstates.keys())
            inloop_fst_symstate = None
            inloop_snd_symstate = None
            for depth in inloop_ss_depths:
                symstates = inloop_symstates[depth].lst
                if len(symstates) >= 2:
                    inloop_fst_symstate = symstates[0]
                    inloop_snd_symstate = symstates[1]
            if inloop_fst_symstate and inloop_snd_symstate:
                inloop_vars = Z3.get_vars(inloop_fst_symstate.slocal).union(Z3.get_vars(inloop_snd_symstate.slocal))
                inloop_inv_vars = self.inv_decls[self.inloop_loc].exprs(settings.use_reals)
                inloop_ex_vars = inloop_vars.difference(inloop_inv_vars)
                mlog.debug("inloop_ex_vars: {}".format(inloop_ex_vars))
                inloop_fst_symstate = z3.substitute(inloop_fst_symstate.slocal, self.transrel_pre_sst)
                inloop_snd_symstate = z3.substitute(inloop_snd_symstate.slocal, self.transrel_post_sst)
                mlog.debug("inloop_fst_symstate: {}".format(inloop_fst_symstate))
                mlog.debug("inloop_snd_symstate: {}".format(inloop_snd_symstate))
                inloop_trans_f = z3.Exists(list(inloop_ex_vars), z3.And(inloop_fst_symstate, inloop_snd_symstate))
                transrel_expr = Z3.qe(inloop_trans_f)
                mlog.debug("inloop_trans_f: {}".format(transrel_expr))
                return transrel_expr
        return None

    def _infer_transrel_traces(self):
        old_do_ieqs = dig_settings.DO_IEQS
        # dig_settings.DO_IEQS = False
        transrel_itraces = {}
        inloop_loc = self.inloop_loc
        postloop_loc = self.postloop_loc
        for inp, dtraces in self.rand_itraces.items():
            if inloop_loc in dtraces:
                inloop_traces = dtraces[inloop_loc]
                transrel_traces = []
                if len(inloop_traces) >= 1:
                    if postloop_loc in dtraces:
                        inloop_zip_traces = zip(inloop_traces, inloop_traces[1:] + [dtraces[postloop_loc][0]])
                    else:
                        inloop_zip_traces = zip(inloop_traces[:-1], inloop_traces[1:])
                else:
                    inloop_zip_traces = []
                for transrel_pre, transrel_post in inloop_zip_traces:
                    ss = tuple(list(map(lambda s: s + '0', transrel_pre.ss)) + 
                               list(map(lambda s: s + '1', transrel_post.ss)))
                    vs = transrel_pre.vs + transrel_post.vs
                    transrel_traces.append(Trace.parse(ss, vs))
                transrel_itraces[inp] = {self.transrel_loc: transrel_traces}
        # mlog.debug("transrel_itraces: {}".format(transrel_itraces))
        transrel_invs = self.dig.infer_from_traces(transrel_itraces, self.transrel_loc)
        # transrel_invs = self.dig.infer_from_traces(self.rand_itraces, self.transrel_loc)
        mlog.debug("transrel_invs: {}".format(transrel_invs))
        dig_settings.DO_IEQS = old_do_ieqs

        transrel_invs = ZInvs(transrel_invs)
        if transrel_invs.is_unsat():
            return None
        transrel_expr = transrel_invs.expr()
        return transrel_expr

    def infer_transrel(self):
        if self.symstates:
            transrel_expr = self._infer_transrel_symstates()
            if transrel_expr is None:
                transrel_expr = self._infer_transrel_traces()
        else:
            transrel_expr = self._infer_transrel_traces()
        return transrel_expr

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

        self.transrel_expr = config.infer_transrel()
        self.tCexs = []

    def verify(self, rcs, precond):
        assert rcs is None or isinstance(rcs, ZInvs), rcs
        _config = self._config

        def _mk_cex_inps(models, inv_decls):
            assert isinstance(models, list) and models, models
            if all(isinstance(m, z3.ModelRef) for m in models):
                cexs, _ = Z3.extract(models)
            else:
                cexs = [{x: sage.all.sage_eval(str(v)) for (x, v) in model}
                        for model in models]
            icexs = set()
            for cex in cexs:
                # mlog.debug("cex: {}".format(cex))
                icexs.add(tuple([cex[v.__str__()] for v in inv_decls]))
            inps = Inps()
            inps = inps.merge(icexs, _config.inp_decls)
            return inps

        if rcs is None:
            sCexs = []
            if precond is None:
                mlog.debug("verify: Using random inps")
                rand_itraces = _config.rand_itraces
            else:
                rs, _ = Solver.get_models(precond, _config.nInps, _config.tmpdir, 
                                          settings.use_random_seed)
                if isinstance(rs, list) and rs:
                    mlog.debug("verify: Using random inps from precond")
                    rs = _mk_cex_inps(rs, _config.inv_decls[_config.preloop_loc].exprs((settings.use_reals)))
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
            mlog.debug("rcs_l: {}".format(rcs_l))
            mlog.debug("transrel_expr: {}".format(self.transrel_expr))

            def _check(rc):
                rc_r = z3.substitute(rc, _config.transrel_post_sst)
                # f = z3.Not(z3.Implies(z3.And(rcs_l, transrel_expr), rc_r))
                f = z3.And(z3.And(rcs_l, self.transrel_expr), z3.Not(rc_r))
                mlog.debug("_check: f = {}".format(f))
                # using_random_seed = True
                rs, _ = Solver.get_models(f, _config.nInps, _config.tmpdir, 
                                          settings.use_random_seed)
                if rs is None:
                    mlog.debug("rs: unknown")
                elif rs is False:
                    mlog.debug("rs: unsat")
                else:
                    mlog.debug("rs: sat ({} models)".format(len(rs)))
                    if isinstance(rs, list) and rs:
                        rs = _mk_cex_inps(rs, _config.transrel_pre_inv_decls)
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

        mayloop_invs = ZInvs(_config.dig.infer_from_traces(
            itraces, _config.inloop_loc, mayloop_inps))
        if rcs is None:
            return mayloop_invs
        elif mayloop_invs and rcs.implies(mayloop_invs):
            return mayloop_invs
        else:
            base_term_pre = ZInvs(_config.dig.infer_from_traces(
                itraces, _config.preloop_loc, base_term_inps))
            term_invs = ZInvs(_config.dig.infer_from_traces(
                itraces, _config.inloop_loc, term_inps))
            mlog.debug("base_term_pre: {}".format(base_term_pre))
            mlog.debug("term_invs: {}".format(term_invs))
            term_traces = []
            for term_inp in term_inps:
                term_traces.append(itraces[term_inp])
            self.tCexs.append((term_invs, term_traces))
            term_cond = z3.Or(base_term_pre.expr(), term_invs.expr())
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
        mlog.debug("refinement_depth: {}".format(_config.refinement_depth))
        candidateRCS = [(None, 0, [])]
        validRCS = []
        mlog.debug("precond: {}".format(precond))

        if self.transrel_expr is None:
            return validRCS
        else:
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
            for tCex in self.tCexs:
                mlog.debug("tCex: {}".format(tCex))
            return validRCS
