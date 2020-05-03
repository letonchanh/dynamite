from pathlib import Path
from functools import partial

logger_level = 2
run_dig = False
use_reals = False
use_random_seed = False
prove_term = False
prove_nonterm = False
max_nonterm_refinement_depth = 3
n_inps = 100
inps_threshold = 2
test_ratio = 0.2
SOLVER_TIMEOUT = 5 * 1000 # 5s
LOOP_ITER_BND = 500
VLOOP_FUN = "vloop"

DYNAMITE_DIR = Path(__file__).parent.parent.parent

class C:
    PTR_VARS_PREFIX = 'PTR_'

    CIL_TRANSFORM_DIR = DYNAMITE_DIR / "deps" / "dynamo-instr"
    assert CIL_TRANSFORM_DIR.is_dir(), CIL_TRANSFORM_DIR

    CIL_EXE = CIL_TRANSFORM_DIR / "src" / "cil" / "bin" / "cilly"
    CIL_OPTS = "--gcc=/usr/bin/gcc-5 --save-temps -D HAPPY_MOOD"
    CIL_CMD = partial("{cil_exe} {cil_opts} {ext} {inf} --out={outf} {opts}".format,
                      cil_exe=CIL_EXE, cil_opts=CIL_OPTS)

    TRANSFORM_OPTS = partial("--bnd={bnd}".format)
    TRANSFORM = lambda bnd, inf, outf: C.CIL_CMD(ext="--dotransform", 
            inf=inf, outf=outf, opts=(C.TRANSFORM_OPTS(bnd=bnd)))

    RANK_VALIDATE_OPTS = partial("--pos={pos} --ranks={ranks}".format)
    RANK_VALIDATE = lambda pos, ranks, inf, outf: C.CIL_CMD(ext="--dovalidate", 
            inf=inf, outf=outf, opts=(C.TRANSFORM_OPTS(pos=pos, ranks=ranks)))