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

DYNAMITE_DIR = Path(__file__).parent.parent.parent

class C:
    PTR_VARS_PREFIX = 'PTR_'

    CIL_TRANSFORM_DIR = DYNAMITE_DIR / "deps/dynamo-instr"
    assert CIL_TRANSFORM_DIR.is_dir(), CIL_TRANSFORM_DIR

    TRANSFORM_EXE = CIL_TRANSFORM_DIR / "instr.pl"
    TRANSFORM_CMD = "{transform_exe} vtrace {inf} {outf} {bnd}"
    TRANSFORM = partial(TRANSFORM_CMD.format, transform_exe=TRANSFORM_EXE)