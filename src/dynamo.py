from __future__ import absolute_import
import os
import sys
import time
import datetime
import itertools
import functools
import z3
import random
import sage.all
import copy

dynamo_path = os.path.realpath(os.path.dirname(__file__))
dig_path = os.path.realpath(os.path.join(dynamo_path, '../deps/dig/src'))
sys.path.insert(0, dig_path)

import helpers.vcommon as dig_common_helpers
from helpers.miscs import Z3, Miscs
import alg as dig_alg
from core import Execution, Classification, Inference
from utils import settings
from data.traces import Inps
from data.inv.invs import Invs
from utils.logic import *

mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

def run_dig(inp, seed, maxdeg, do_rmtmp):

    mlog.info("{}".format("get invs from DIG"))

    if inp.endswith(".java") or inp.endswith(".class"):
        dig = dig_alg.DigSymStates(inp)
    else:
        dig = dig_alg.DigTraces.from_tracefiles(inp)
    invs, traces, tmpdir = dig.start(seed, maxdeg)

    if do_rmtmp:
        import shutil
        print("clean up: rm -rf {}".format(tmpdir))
        shutil.rmtree(tmpdir)
    else:
        print("tmpdir: {}".format(tmpdir))


if __name__ == "__main__":
    import settings as dig_settings
    from helpers import src_java as dig_src_java
    from data import miscs as dig_miscs
    import argparse

    aparser = argparse.ArgumentParser("Dynamo")
    ag = aparser.add_argument
    ag("inp", help="inp")

    # Dynamo settings
    ag("--log_level", "-log_level",
       type=int,
       choices=range(5),
       default=3,
       help="set logger info")

    ag("--run_dig", "-run_dig",
        action="store_true",
        help="run DIG on the input")

    ag("--no_random_seed", "-no_random_seed",
        action="store_true",
        help="generate models without random_seed")

    # DIG settings
    ag("--dig_log_level", "-dig_log_level",
       type=int,
       choices=range(5),
       default=2,
       help="DIG: set logger info")
    ag("--dig_seed", "-dig_seed",
       type=float,
       help="DIG: use this seed in DIG")
    ag("--dig_nomp", "-dig_nomp",
       action="store_true",
       help="DIG: don't use multiprocessing")

    args = aparser.parse_args()

    settings.run_dig = args.run_dig
    settings.use_random_seed = not args.no_random_seed

    dig_settings.DO_MP = not args.dig_nomp

    # Set DIG's log level
    if 0 <= args.dig_log_level <= 4 and args.dig_log_level != dig_settings.logger_level:
        dig_settings.logger_level = args.dig_log_level
    dig_settings.logger_level = dig_common_helpers.getLogLevel(dig_settings.logger_level)

    if 0 <= args.log_level <= 4 and args.log_level != settings.logger_level:
        settings.logger_level = args.log_level
    settings.logger_level = dig_common_helpers.getLogLevel(settings.logger_level)

    # mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

    mlog.info("{}: {}".format(datetime.datetime.now(), ' '.join(sys.argv)))

    inp = os.path.realpath(os.path.expanduser(args.inp))
    seed = round(time.time(), 2) if args.dig_seed is None else float(args.dig_seed)

    if settings.run_dig:
        run_dig(inp, seed, maxdeg=2, do_rmtmp=False)
    else:
        import analysis
        assert(inp.endswith(".java") or inp.endswith(".class"))
        import tempfile

        nInps = 100
        preloop_loc = 'vtrace1'
        inloop_loc = 'vtrace2'
        postloop_loc = 'vtrace3'
        transrel_loc = 'vtrace4'
        refinement_depth = 5

        tmpdir = tempfile.mkdtemp(dir=dig_settings.tmpdir, prefix="Dig_")
        (inp_decls, inv_decls, clsname, mainQ_name, jpfdir, jpffile,
         tracedir, traceFile) = dig_src_java.parse(inp, tmpdir)
        exe_cmd = dig_settings.JAVA_RUN(tracedir=tracedir, clsname=clsname)
        prog = dig_miscs.Prog(exe_cmd, inp_decls, inv_decls)
        exe = Execution(prog)
        dig = Inference(inv_decls, seed)
        cl = Classification(preloop_loc, inloop_loc, postloop_loc)

        rand_inps = exe.gen_rand_inps(nInps)
        rand_itraces = exe.get_traces(rand_inps)  # itraces: input to dtraces

        def infer_transrel():
            old_do_ieqs = dig_settings.DO_IEQS
            # dig_settings.DO_IEQS = False
            transrel_invs = dig.infer_from_traces(rand_itraces, transrel_loc)
            dig_settings.DO_IEQS = old_do_ieqs
            return transrel_invs

        def gen_transrel_sst(transrel_inv_decls, inloop_inv_decls):
            assert len(transrel_inv_decls) % 2 == 0
            assert len(inloop_inv_decls) * 2 == len(transrel_inv_decls)

            transrel_pre_inv_decls = transrel_inv_decls[:len(transrel_inv_decls)//2]
            transrel_post_inv_decls = transrel_inv_decls[len(transrel_inv_decls)//2:]
            return transrel_pre_inv_decls, \
                   zip(inloop_inv_decls, transrel_pre_inv_decls), \
                   zip(inloop_inv_decls, transrel_post_inv_decls)

        transrel_inv_decls = inv_decls[transrel_loc].exprs(settings.use_reals)
        inloop_inv_decls = inv_decls[inloop_loc].exprs(settings.use_reals)
        transrel_pre_inv_decls, transrel_pre_sst, transrel_post_sst = \
            gen_transrel_sst(transrel_inv_decls, inloop_inv_decls)
        mlog.debug("transrel_pre_inv_decls: {}".format(transrel_pre_inv_decls))
        mlog.debug("transrel_pre_sst: {}".format(transrel_pre_sst))
        mlog.debug("transrel_post_sst: {}".format(transrel_post_sst))

        transrel_invs = ZInvs(infer_transrel())
        assert not transrel_invs.is_unsat(), transrel_invs
        mlog.debug("transrel_invs: {}".format(transrel_invs))
        transrel_expr = transrel_invs.expr()

        # dig_settings.DO_EQTS = False

        from parsers import Z3OutputHandler
        z3_output_handler = Z3OutputHandler()

        def check_sat_and_get_rand_model(solver):
            myseed = random.randint(0, 1000000)
            smt2_str = [
                '(set-option :smt.arith.random_initial_value true)',
                solver.to_smt2().replace('(check-sat)', ''),
                '(check-sat-using (using-params qflra :random-seed {}))'.format(myseed),
                '(get-model)']
            smt2_str = '\n'.join(smt2_str)
            # mlog.debug("smt2_str: {}".format(smt2_str))
            filename = tmpdir + 't.smt2'
            dig_common_helpers.vwrite(filename, smt2_str)
            cmd = 'z3 {}'.format(filename)
            rmsg, errmsg = dig_common_helpers.vcmd(cmd)
            assert not errmsg, "'{}': {}".format(cmd, errmsg)
            z3_output_ast = z3_output_handler.parser.parse(rmsg)
            chk, model = z3_output_handler.transform(z3_output_ast)
            # mlog.debug("model: {}".format(model))
            return chk, model

        def get_models(f, k, using_random_seed=False):
            if not using_random_seed:
                return Z3.get_models(f, k)

            assert z3.is_expr(f), f
            assert k >= 1, k

            solver = Z3.create_solver()
            solver.add(f)

            models = []
            i = 0
            # while solver.check() == z3.sat and i < k:
            while i < k:
                chk, m = check_sat_and_get_rand_model(solver)
                if chk != z3.sat:
                    break
                i = i + 1
                if not m:  # if m == []
                    break
                models.append(m)
                mlog.debug("model {}: {}".format(i, m))
                # create new constraint to block the current model
                block = z3.Not(z3.And([z3.Int(x) == v for (x, v) in m]))
                solver.add(block)

            stat = solver.check()

            if stat == z3.unknown:
                rs = None
            elif stat == z3.unsat and i == 0:
                rs = False
            else:
                rs = models

            assert not (isinstance(rs, list) and not rs), rs
            return rs, stat

        def verify(rcs):
            assert rcs is None or isinstance(rcs, ZInvs), rcs
            if rcs is None:
                sCexs = []
                sCexs.append(rand_inps)
                return False, sCexs
            else:
                assert rcs, rcs
                rcs_l = z3.substitute(rcs.expr(), transrel_pre_sst)
                mlog.debug("rcs_l: {}".format(rcs_l))
                mlog.debug("transrel_expr: {}".format(transrel_expr))

                def _mk_cex_inps(models):
                    assert isinstance(models, list) and models, models
                    if all(isinstance(m, z3.ModelRef) for m in models):
                        cexs, _ = Z3.extract(models)
                    else:
                        cexs = [{x: sage.all.sage_eval(str(v)) for (x, v) in model}
                                for model in models]
                    icexs = set()
                    for cex in cexs:
                        icexs.add(tuple([cex[v.__str__()]
                                         for v in transrel_pre_inv_decls]))
                    inps = Inps()
                    inps = inps.merge(icexs, inp_decls)
                    return inps

                def _check(rc):
                    rc_r = z3.substitute(rc, transrel_post_sst)
                    # f = z3.Not(z3.Implies(z3.And(rcs_l, transrel_expr), rc_r))
                    f = z3.And(z3.And(rcs_l, transrel_expr), z3.Not(rc_r))
                    mlog.debug("_check: f = {}".format(f))
                    # using_random_seed = True
                    rs, _ = get_models(f, nInps, settings.use_random_seed)
                    if rs is None:
                        mlog.debug("rs: unknown")
                    elif rs is False:
                        mlog.debug("rs: unsat")
                    else:
                        mlog.debug("rs: sat ({} models)".format(len(rs)))
                        if isinstance(rs, list) and rs:
                            rs = _mk_cex_inps(rs)
                    return rs

                chks = [_check(rc) for rc in rcs]
                if all(rs is False for rs in chks):
                    return True, None  # valid
                else:
                    sCexs = []
                    for rs in chks:
                        if rs is None:
                            return False, None  # unknown
                        elif rs:  # sat
                            sCexs.append(rs)
                    return False, sCexs  # invalid with a set of new Inps

        def strengthen(rcs, inps):
            assert isinstance(inps, Inps), inps
            assert len(inps) > 0
            if rcs is None:
                itraces = rand_itraces
            else:
                itraces = exe.get_traces(inps)
            base_term_inps, term_inps, mayloop_inps = cl.classify_inps(itraces)
            mlog.debug("base_term_inps: {}".format(len(base_term_inps)))
            mlog.debug("term_inps: {}".format(len(term_inps)))
            mlog.debug("mayloop_inps: {}".format(len(mayloop_inps)))

            mayloop_invs = ZInvs(dig.infer_from_traces(
                itraces, inloop_loc, mayloop_inps))
            if rcs is None:
                return mayloop_invs
            elif mayloop_invs and mayloop_invs.implies(rcs):
                return mayloop_invs
            else:
                base_term_pre = ZInvs(dig.infer_from_traces(
                    itraces, preloop_loc, base_term_inps))
                term_invs = ZInvs(dig.infer_from_traces(
                    itraces, inloop_loc, term_inps))
                mlog.debug("base_term_pre: {}".format(base_term_pre))
                mlog.debug("term_invs: {}".format(term_invs))
                term_cond = z3.Or(base_term_pre.expr(), term_invs.expr())
                simplified_term_cond = Z3.simplify(term_cond)
                cnf_term_cond = Z3.to_cnf(simplified_term_cond)
                mlog.debug("simplified_term_cond: {}".format(simplified_term_cond))
                mlog.debug("cnf_term_cond: {}".format(cnf_term_cond))
                dnf_neg_term_cond = Z3.to_nnf(z3.Not(cnf_term_cond))
                mlog.debug("dnf_neg_term_cond: {}".format(dnf_neg_term_cond))
                nrcs = copy.deepcopy(rcs)
                nrcs.add(dnf_neg_term_cond)
                return nrcs

        def prove_NonTerm():
            candidateRCS = [(None, 0, [])]
            validRCS = []
            while candidateRCS:
                mlog.debug("candidateRCS: {}".format(candidateRCS))
                rcs, depth, ancestors = candidateRCS.pop()
                mlog.debug("PROVE_NT DEPTH {}: {}".format(depth, rcs))
                if depth < refinement_depth:
                    chk, sCexs = verify(rcs)
                    if chk and not rcs.is_unsat():
                        validRCS.append((rcs, ancestors))
                    elif sCexs is not None:
                        for cexs in sCexs:
                            nrcs = strengthen(rcs, cexs)
                            assert nrcs is not None, nrcs
                            nancestors = copy.deepcopy(ancestors)
                            nancestors.append((depth, rcs))
                            candidateRCS.append((nrcs, depth+1, nancestors))
            return validRCS

        validRCS = prove_NonTerm()
        for rcs, ancestors in validRCS:
            f = Z3.to_dnf(rcs.simplify())
            mlog.debug("rcs: {}".format(f))
            for depth, ancestor in ancestors:
                if ancestor is None:
                    ancestor_ = None
                else:
                    ancestor_ = Z3.to_dnf(ancestor.simplify())
                mlog.debug("ancestor {}: {}".format(depth, ancestor_))
