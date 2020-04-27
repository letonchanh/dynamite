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
import logging

dynamo_path = os.path.realpath(os.path.dirname(__file__))
dig_path = os.path.realpath(os.path.join(dynamo_path, '../deps/dig/src'))
sys.path.insert(0, dig_path)

if __name__ == "__main__":
    import argparse

    aparser = argparse.ArgumentParser("Dynamo")
    ag = aparser.add_argument
    ag("inp", help="inp")

    # Dynamo settings
    ag("--log_level", "-log_level",
       type=int,
       choices=range(5),
       default=4,
       help="set logger info")

    ag("--run_dig", "-run_dig",
        action="store_true",
        help="run DIG on the input")

    ag("--no_random_seed", "-no_random_seed",
        action="store_true",
        help="generate models without random_seed")

    ag("--term", "-t",
        action="store_true",
        help="run termination analysis")
    
    ag("--nonterm", "-nt",
        action="store_true",
        help="run non-termination analysis")

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
    
    ag("--dig_normtmp", "--dig_normtmp",
       action="store_true",
       help="DIG: don't remove tmp folder")
    
    args = aparser.parse_args()

    from utils import settings
    import settings as dig_settings
    import helpers.vcommon as dig_common_helpers

    settings.run_dig = args.run_dig
    settings.use_random_seed = not args.no_random_seed
    settings.prove_term = args.term
    settings.prove_nonterm = args.nonterm

    dig_settings.DO_MP = not args.dig_nomp

    dig_settings.DO_RMTMP = not args.dig_normtmp

    # Set DIG's log level
    if 0 <= args.dig_log_level <= 4 and args.dig_log_level != dig_settings.logger_level:
        dig_settings.logger_level = args.dig_log_level
    dig_settings.logger_level = dig_common_helpers.getLogLevel(dig_settings.logger_level)

    if 0 <= args.log_level <= 4 and args.log_level != settings.logger_level:
        settings.logger_level = args.log_level
    settings.logger_level = dig_common_helpers.getLogLevel(settings.logger_level)
    
    mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

    mlog.info("Dynamite's logger_level: {}".format(logging.getLevelName(settings.logger_level)))
    mlog.info("Dig's logger_level: {}".format(logging.getLevelName(dig_settings.logger_level)))

    mlog.info("{}: {}".format(datetime.datetime.now(), ' '.join(sys.argv)))

    inp = os.path.realpath(os.path.expanduser(args.inp))
    seed = round(time.time(), 2) if args.dig_seed is None else float(args.dig_seed)

    if settings.run_dig:
        import alg as dig_alg
        mlog.info("{}".format("get invs from DIG"))

        if inp.endswith(".java") or inp.endswith(".class"):
            dig = dig_alg.DigSymStatesJava(inp)
        elif inp.endswith(".c"):
            dig = dig_alg.DigSymStatesC(inp)
        else:
            dig = dig_alg.DigTraces.from_tracefiles(inp)
        maxdeg = 2
        invs, traces = dig.start(seed, maxdeg)
    else:
        from helpers.miscs import Z3
        from analysis import Setup, NonTerm, Term
    
        if settings.prove_term or settings.prove_nonterm:
            config = Setup(seed, inp)
        
        if settings.prove_nonterm:
            nt_prover = NonTerm(config) 
            validRCS = nt_prover.prove()
            mlog.info("validRCS: {}".format(validRCS))
            for rcs, ancestors in validRCS:
                f = Z3.to_dnf(rcs.simplify())
                mlog.info("(simplified) rcs: {}".format(f))
                for depth, ancestor in ancestors:
                    if ancestor is None:
                        ancestor_ = None
                    else:
                        ancestor_ = Z3.to_dnf(ancestor.simplify())
                    mlog.info("ancestor {}: {}".format(depth, ancestor_))

        if settings.prove_term:
            t_prover = Term(config)
            t_prover.prove()


    

