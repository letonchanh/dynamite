from __future__ import absolute_import
import os
import sys
import time
import datetime
import itertools
import functools
import z3

dynamo_path = os.path.realpath(os.path.dirname(__file__))
dig_path = os.path.realpath(os.path.join(dynamo_path, '../deps/dig/src'))
sys.path.insert(0, dig_path)

import helpers.vcommon as dig_common_helpers
from helpers.miscs import Z3, Miscs
import alg as dig_alg
from core import Execution, Classification, Inference
from utils import settings

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

    dig_settings.DO_MP = not args.dig_nomp

    # Set DIG's log level
    if 0 <= args.dig_log_level <= 4 and args.dig_log_level != dig_settings.logger_level:
        dig_settings.logger_level = args.dig_log_level
    dig_settings.logger_level = dig_common_helpers.getLogLevel(
        dig_settings.logger_level)

    if 0 <= args.log_level <= 4 and args.log_level != settings.logger_level:
        settings.logger_level = args.log_level
    settings.logger_level = dig_common_helpers.getLogLevel(
        settings.logger_level)

    mlog.info("{}: {}".format(datetime.datetime.now(), ' '.join(sys.argv)))

    inp = os.path.realpath(os.path.expanduser(args.inp))
    seed = round(time.time(), 2) if args.dig_seed is None else float(args.dig_seed)

    if settings.run_dig:
        run_dig(inp, seed, maxdeg=2, do_rmtmp=False)
    else:
        assert(inp.endswith(".java") or inp.endswith(".class"))
        import tempfile
        tmpdir = tempfile.mkdtemp(dir=dig_settings.tmpdir, prefix="Dig_")
        (inp_decls, inv_decls, clsname, mainQ_name, jpfdir, jpffile,
         tracedir, traceFile) = dig_src_java.parse(inp, tmpdir)
        exe_cmd = dig_settings.JAVA_RUN(tracedir=tracedir, clsname=clsname)
        prog = dig_miscs.Prog(exe_cmd, inp_decls, inv_decls)
        exe = Execution(prog)
        nInps = 500
        inps = exe.gen_rand_inps(nInps)
        itraces = exe.get_traces(inps) # itraces: input to dtraces
        preloop = 'vtrace1'
        inloop = 'vtrace2'
        postloop = 'vtrace3'
        transrel = 'vtrace4'
        cl = Classification(preloop, inloop, postloop)
        base_term_inps, term_inps, mayloop_inps = cl.classify_inps(itraces)

        inference = Inference(inv_decls, seed)
        # BASE/LOOP CONDITION
        # term_pre = inference.infer_from_traces(itraces, preloop, term_inps)
        term_invs = inference.infer_from_traces(itraces, inloop, term_inps)
        
        # mayloop_pre = inference.infer_from_traces(itraces, preloop, mayloop_inps)
        mayloop_invs = inference.infer_from_traces(itraces, inloop, mayloop_inps)

        # mlog.debug("term_pre: {}".format(term_pre))
        mlog.debug("term_invs: {}".format(term_invs))
        # mlog.debug("mayloop_pre: {}".format(mayloop_pre))
        mlog.debug("mayloop_invs: {}".format(mayloop_invs))

        def infer_transrel():
            old_do_ieqs = dig_settings.DO_IEQS
            dig_settings.DO_IEQS = False
            transrel_invs = inference.infer_from_traces(itraces, transrel)
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

        transrel_inv_decls = inv_decls[transrel].exprs(settings.use_reals)
        inloop_inv_decls = inv_decls[inloop].exprs(settings.use_reals)
        transrel_pre_inv_decls, transrel_pre_sst, transrel_post_sst = gen_transrel_sst(transrel_inv_decls, inloop_inv_decls)
        mlog.debug("transrel_pre_inv_decls: {}".format(transrel_pre_inv_decls))
        mlog.debug("transrel_pre_sst: {}".format(transrel_pre_sst))
        mlog.debug("transrel_post_sst: {}".format(transrel_post_sst))

        transrel_invs = functools.reduce(z3.And, [inv.expr(settings.use_reals) for inv in infer_transrel()])
        mlog.debug("transrel_invs: {}".format(transrel_invs))

        candidate_recurrent_set = map(lambda inv: inv.expr(settings.use_reals), mayloop_invs)
        mlog.debug("candidate_recurrent_set: {}".format(candidate_recurrent_set))

        rs = z3.substitute(functools.reduce(z3.And, candidate_recurrent_set), transrel_pre_sst)
        mlog.debug("rs: {}".format(rs))

        def get_cexs(r):
            f = z3.Not(z3.Implies(z3.And(rs, transrel_invs), z3.substitute(r, transrel_post_sst)))
            models, stat = Z3.get_models(f, nInps)
            cexs, isSucc = Z3.extract(models)
            sCexs = set()
            for cex in cexs:
                sCexs.add(tuple([cex[v.__str__()] for v in transrel_pre_inv_decls]))
            return sCexs

        # def f(tasks):
        #     return [(rstr, get_cexs(r)) for rstr, r in tasks]
        # tasks = [(r.__str__(), r) for r in candidate_recurrent_set]
        # wrs = Miscs.run_mp('get_cexs', tasks, f)
        # print wrs

        from data.traces import Inps
        for r in candidate_recurrent_set:
            print r
            cexs = get_cexs(r)
            if cexs:
                inps = Inps()
                print inp_decls
                inps = inps.merge(cexs, inp_decls)
                itraces = exe.get_traces(inps)
                base_term_inps, term_inps, mayloop_inps = cl.classify_inps(itraces)
                term_pre = inference.infer_from_traces(itraces, preloop, term_inps)
                mlog.debug("term_pre: {}".format(term_pre))
                mayloop_pre = inference.infer_from_traces(itraces, preloop, mayloop_inps)
                mlog.debug("mayloop_pre: {}".format(mayloop_pre))

