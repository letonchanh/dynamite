from pathlib import Path
from functools import partial
import os

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

class CIL:
    PTR_VARS_PREFIX = 'PTR_'

    CIL_TRANSFORM_DIR = DYNAMITE_DIR / "deps" / "dynamo-instr"
    assert CIL_TRANSFORM_DIR.is_dir(), CIL_TRANSFORM_DIR

    CIL_EXE = CIL_TRANSFORM_DIR / "src" / "cil" / "bin" / "cilly"
    CIL_OPTS = "--gcc=/usr/bin/gcc-5 --save-temps -D HAPPY_MOOD"
    CIL_CMD = partial("{cil_exe} {cil_opts} {ext} {inf} --out={outf} {opts}".format,
                      cil_exe=CIL_EXE, cil_opts=CIL_OPTS)

    TRANSFORM_OPTS = partial("--bnd={bnd}".format)
    TRANSFORM = lambda bnd, inf, outf: CIL.CIL_CMD(ext="--dotransform", 
            inf=inf, outf=outf, opts=(CIL.TRANSFORM_OPTS(bnd=bnd)))

    RANK_VALIDATE_OPTS = partial("--pos={pos} --ranks={ranks}".format)
    RANK_VALIDATE = lambda pos, ranks, inf, outf: CIL.CIL_CMD(ext="--dovalidate", 
            inf=inf, outf=outf, opts=(CIL.RANK_VALIDATE_OPTS(pos=pos, ranks=('"' + ranks + '"'))))

class REACHABILITY:
    ARCH = 32
    SPEC = Path('/tools/reachability.prp')
    assert SPEC.is_file(), SPEC

class CPAchecker:
    CPA_HOME = Path(os.path.expandvars("$CPA_HOME"))
    CPA_EXE = CPA_HOME / 'scripts' / 'cpa.sh'
    
    CPA_COMMON_OPTS = "-spec {spec}".format(spec=REACHABILITY.SPEC)
    CPA_REACH_OPTS = "-predicateAnalysis -setprop counterexample.export.compressWitness=false"
    CPA_VALIDATE_OPTS = partial("-witnessValidation -witness {witness}".format)
    
    CPA_CMD = partial("{cpa_exe} {cpa_opts} {cpa_task_opts} {input}".format,
                      cpa_exe=CPA_EXE, cpa_opts=CPA_COMMON_OPTS)

class Ultimate:
    ULT_HOME = Path(os.path.expandvars("$ULT_HOME"))
    ULT_EXE = lambda variant: Ultimate.ULT_HOME / 'releaseScripts' / 'default' / ('{variant}-linux'.format(variant=variant)) / 'Ultimate.py'

    ULT_COMMON_OPTS = partial("--spec {spec} --architecture {arch}bit --witness-dir {witness_dir} --witness-name {witness_name}".format, spec=REACHABILITY.SPEC, arch=REACHABILITY.ARCH)
    
    ULT_CMD = lambda variant, witness_dir, witness_name, input: "{ult_exe} {ult_opts} --file {input}".format(
                                        ult_exe=Ultimate.ULT_EXE(variant=variant), 
                                        ult_opts=Ultimate.ULT_COMMON_OPTS(witness_dir=witness_dir, witness_name=witness_name),
                                        input=input)
