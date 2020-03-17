#! /usr/bin/env python3

"""
Example: f=/path/to/results.txt ; rm -rf $f; /path/to/benchmark.py 2>&1 | tee $f
"""
from pathlib import Path
import pdb
import os
import time
from datetime import datetime

DBG = pdb.set_trace


TIMEOUT = 900  # seconds
EXE = Path("/path/to/dynamo").resolve()
TRANSFORM_EXE = ""
TRANSFORM_CMD = TRANSFORM_EXE + " {filename}"
CMD = "timeout {} python3 {}".format(TIMEOUT, EXE)
CMD = CMD + " {filename}"
BENCHDIR = Path("../benchmarks").resolve()
NTIMES = 2  # run each program how many times?


def run(benchdir, ntimes):
    assert benchdir.is_dir(), benchdir

    print("# Benchmark dir '{}' {} times ({})".format(
        benchdir, ntimes, datetime.now()), flush=True)
    fs = sorted(f for f in benchdir.iterdir()
                if len(f.suffixes) == 2 and
                f.suffixes[0] == ".expected" and
                f.suffixes[1] == '.c')

    for i, f in enumerate(fs):
        for j in range(ntimes):
            print("## {}/{}, run {}/{}. {}".format(
                i+1, len(fs), j+1, ntimes,
                time.strftime("%c")), flush=True)

            transform_cmd = TRANSFORM_CMD.format(filename=f)
            print("{}".format(transform_cmd), flush=True)
            os.system(transform_cmd)

            run_cmd = CMD.format(filename=f)
            print("{}".format(run_cmd), flush=True)
            os.system(run_cmd)


run(BENCHDIR.resolve(), NTIMES)
