from __future__ import absolute_import
import os
import signal
import sys
import multiprocessing
import psutil
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

    ag("--timeout", "-timeout",
       type=int,
       default=300,
       help="set timeout")

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

    ag("--dfs", "-dfs",
        action="store_true",
        help="use DFS in non-termination analysis")

    # ag("--bfs", "-bfs",
    #     action="store_true",
    #     help="use BFS in non-termination analysis")

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
    settings.use_dfs = args.dfs
    # settings.use_bfs = args.bfs
    
    if args.timeout:
        settings.timeout = int(args.timeout)

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
    mlog.info("Timeout: {}s".format(settings.timeout))

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
        from analysis import Setup, NonTerm, Term, TNT
        import utils.profiling
        from utils.profiling import timeit
    
        config = Setup(seed, inp)

        @timeit
        def prove():
            if settings.prove_nonterm:
                nt_prover = NonTerm(config) 
                nt_prover.prove()

            elif settings.prove_term:
                t_prover = Term(config)
                t_prover.prove()

            else:
                tnt_prover = TNT(config)
                tnt_prover.prove()

            print('Time log:')
            for meth, time in utils.profiling.time_log.items():
                print('{}: {:.3f}s'.format(meth, time / 1000))


        prove_process = multiprocessing.Process(target=prove)
        prove_process.start()
        mlog.debug('prove_process: {}'.format(prove_process.pid))
        prove_process.join(timeout=settings.timeout)

        # def on_terminate(proc):
        #     print("process {} terminated with exit code {}".format(proc, proc.returncode))

        # dynamite_process = psutil.Process(pid=prove_process.pid)
        # dynamite_children = dynamite_process.children(recursive=True)
        # for child in dynamite_children:
        #     print('Child pid is {}, {}'.format(child.pid, child.name()))
        #     child.terminate()
        # gone, alive = psutil.wait_procs(dynamite_children, timeout=1, callback=on_terminate)
        # for p in alive:
        #     print('{} alive'.format(p))
        #     p.kill()
        
        # prove_process.terminate()
        # if prove_process.exitcode is None:
        #     pgrp = os.getpgid(prove_process.pid)
        #     os.killpg(pgrp, signal.SIGINT)
        # pgrp = os.getpgid(os.getpid())
        # mlog.debug('pgrp: {}'.format(pgrp))
        # os.killpg(pgrp, signal.SIGTERM)

    

