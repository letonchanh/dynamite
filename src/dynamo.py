from __future__ import absolute_import
import os
import sys
import time
import datetime
import itertools

dynamo_path = os.path.realpath(os.path.dirname(__file__))
dig_path = os.path.realpath(os.path.join(dynamo_path, '../deps/dig/src'))
sys.path.insert(0, dig_path)

import helpers.vcommon as dig_common_helpers
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
        itraces = exe.get_rand_traces() # itraces: input to dtraces
        preloop = 'vtrace1'
        inloop = 'vtrace2'
        postloop = 'vtrace3'
        cl = Classification(preloop, inloop, postloop)
        base_term_inps, term_inps, mayloop_inps = cl.classify_inps(itraces)

        inference = Inference(inv_decls, seed)
        # BASE/LOOP CONDITION
        term_pre = inference.infer_from_traces(preloop, term_inps, itraces)
        term_invs = inference.infer_from_traces(inloop, term_inps, itraces)
        
        mayloop_pre = inference.infer_from_traces(preloop, mayloop_inps, itraces)
        mayloop_invs = inference.infer_from_traces(inloop, mayloop_inps, itraces)
        
        mlog.debug("term_pre: {}".format(term_pre))
        mlog.debug("term_invs: {}".format(term_invs))
        mlog.debug("mayloop_pre: {}".format(mayloop_pre))
        mlog.debug("mayloop_invs: {}".format(type(mayloop_invs)))

