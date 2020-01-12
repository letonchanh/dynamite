from __future__ import absolute_import
import os
import sys
import time
import datetime
import itertools
import functools
import z3
import random
import copy

dynamo_path = os.path.realpath(os.path.dirname(__file__))
dig_path = os.path.realpath(os.path.join(dynamo_path, '../deps/dig/src'))
sys.path.insert(0, dig_path)

import helpers.vcommon as dig_common_helpers
from helpers.miscs import Z3, Miscs
import alg as dig_alg
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
       default=2,
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
    mlog.debug("settings.logger_level: {}".format(settings.logger_level))
    # settings.logger_level = dig_common_helpers.getLogLevel(settings.logger_level)
    # mlog.debug("settings.logger_level: {}".format(settings.logger_level))

    mlog.info("{}: {}".format(datetime.datetime.now(), ' '.join(sys.argv)))

    inp = os.path.realpath(os.path.expanduser(args.inp))
    seed = round(time.time(), 2) if args.dig_seed is None else float(args.dig_seed)

    if settings.run_dig:
        run_dig(inp, seed, maxdeg=2, do_rmtmp=False)
    else:
        from analysis import Setup, NonTerm
 
        config = Setup(seed, inp)
        nt_prover = NonTerm(config)       
        validRCS = nt_prover.prove()
        mlog.debug("validRCS: {}".format(validRCS))
        for rcs, ancestors in validRCS:
            f = Z3.to_dnf(rcs.simplify())
            mlog.debug("rcs: {}".format(f))
            for depth, ancestor in ancestors:
                if ancestor is None:
                    ancestor_ = None
                else:
                    ancestor_ = Z3.to_dnf(ancestor.simplify())
                mlog.debug("ancestor {}: {}".format(depth, ancestor_))
