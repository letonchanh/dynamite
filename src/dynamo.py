import os
import sys
import time

cwd = os.getcwd()
os.chdir("../deps/dig/src")
dig_path = os.getcwd()
sys.path.append(dig_path)
os.chdir(cwd)

def run(inp, seed, maxdeg, do_rmtmp):
    import alg
    if inp.endswith(".java") or inp.endswith(".class"):
        dig = alg.DigSymStates(inp)
    else:
        dig = alg.DigTraces(inp)
    invs, traces, tmpdir = dig.start(seed, maxdeg)

    if do_rmtmp:
        import shutil
        print("clean up: rm -rf {}".format(tmpdir))
        shutil.rmtree(tmpdir)
    else:
        print("tmpdir: {}".format(tmpdir))

if __name__ == "__main__":
    import alg as dig_alg
    import settings as dig_settings
    import argparse

    aparser = argparse.ArgumentParser("Dynamo")
    ag = aparser.add_argument
    ag("inp", help="inp")
    ag("--log_level", "-log_level",
       type=int,
       choices=range(5),
       default=2,
       help="set logger info")
    ag("--seed", "-seed",
       type=float,
       help="use this seed")
    ag("--nomp", "-nomp",
       action="store_true",
       help="don't use multiprocessing")

    args = aparser.parse_args()

    import settings
    settings.DO_MP = not args.nomp

    inp = os.path.realpath(os.path.expanduser(args.inp))
    seed = round(time.time(), 2) if args.seed is None else float(args.seed)

    run(inp, seed, maxdeg=1, do_rmtmp=True)