from pathlib import Path
from functools import partial
import os

logger_level = 2
run_dig = False
use_reals = False
use_random_seed = False
prove_term = False
prove_nonterm = False
max_nonterm_refinement_depth = 5
n_inps = 100
inps_threshold = 2
test_ratio = 0.2
SOLVER_TIMEOUT = 5 * 1000 # 5s
LOOP_ITER_BND = 500
VLOOP_FUN = "vloop"

DYNAMITE_DIR = Path(__file__).parent.parent.parent

class VTRACE:
    PRELOOP_LABEL = 1
    INLOOP_LABEL = 2
    POSTLOOP_LABEL = 3

class CIL:
    PTR_VARS_PREFIX = 'PTR_'

    CIL_TRANSFORM_DIR = DYNAMITE_DIR / "deps" / "dynamo-instr"
    assert CIL_TRANSFORM_DIR.is_dir(), CIL_TRANSFORM_DIR

    CIL_EXE = CIL_TRANSFORM_DIR / "src" / "cil" / "bin" / "cilly"
    CIL_OPTS = "--save-temps -D HAPPY_MOOD" # --gcc=/usr/bin/gcc-5
    CIL_CMD = partial("{cil_exe} {cil_opts} {ext} {inf} --out={outf} {opts}".format,
                      cil_exe=CIL_EXE, cil_opts=CIL_OPTS)

    TRANSFORM_OPTS = partial("--bnd={bnd}".format)
    TRANSFORM = lambda bnd, inf, outf: CIL.CIL_CMD(ext="--dotransform", 
            inf=inf, outf=outf, opts=(CIL.TRANSFORM_OPTS(bnd=bnd)))

    RANK_VALIDATE_OPTS = partial("--pos={pos} --ranks={ranks}".format)
    RANK_VALIDATE = lambda pos, ranks, inf, outf: CIL.CIL_CMD(ext="--dovalidate", 
            inf=inf, outf=outf, opts=(CIL.RANK_VALIDATE_OPTS(pos=pos, ranks=('"' + ranks + '"'))))

class REACHABILITY:
    TOOLS_HOME = Path(os.path.expandvars("$DYNAMITE_DEPS"))
    ARCH = 32
    SPEC = TOOLS_HOME / 'reachability.prp'
    assert SPEC.is_file(), SPEC

class CPAchecker:
    CPA_HOME = Path(os.path.expandvars("$CPA_HOME"))
    CPA_EXE = CPA_HOME / 'scripts' / 'cpa.sh'
    
    CPA_COMMON_OPTS = "-spec {spec}".format(spec=REACHABILITY.SPEC) # -setprop cpa.predicate.encodeBitvectorAs=INTEGER
    CPA_REACH_OPTS = "-predicateAnalysis -setprop counterexample.export.compressWitness=false"
    CPA_VALIDATE_OPTS = partial("-witnessValidation -witness {witness}".format)
    
    CPA_CMD = partial("{cpa_exe} {cpa_opts} {cpa_task_opts} {input}".format)
    CPA_RUN = partial(CPA_CMD, cpa_exe=CPA_EXE, cpa_opts=CPA_COMMON_OPTS)

    CPA_SHORT_NAME = 'cpa'
    CPA_OUTPUT_DIR = 'output'
    CPA_CEX_NAME = CPA_OUTPUT_DIR + '/' + 'Counterexample.1.assignment.txt'
    CPA_CEX_SMTLIB_NAME = CPA_OUTPUT_DIR + '/' + 'Counterexample.1.smt2'
    CPA_WITNESS_NAME = CPA_OUTPUT_DIR + '/' + 'Counterexample.1.graphml'
    CPA_RES_KEYWORD = 'Verification result:'

class Ultimate:
    ULT_HOME = Path(os.path.expandvars("$ULT_HOME"))
    ULT_EXE = lambda variant: Ultimate.ULT_HOME / 'releaseScripts' / 'default' / ('{variant}-linux'.format(variant=variant)) / 'Ultimate.py'

    ULT_COMMON_OPTS = "--spec {spec} --architecture {arch}bit".format(spec=REACHABILITY.SPEC, arch=REACHABILITY.ARCH)
    ULT_REACH_OPTS = partial("--witness-dir {witness_dir} --witness-name {witness_name}".format)
    ULT_VALIDATE_OPTS = partial("--validate {witness_dir}/{witness_name}".format)

    ULT_REACH_TASK = 'REACH'
    ULT_VALIDATE_TASK = 'VALIDATE'

    ULT_CMD = partial("{ult_exe} {ult_opts} {ult_task_opts} --file {input}".format)
    ULT_RUN = lambda task, variant, witness_dir, witness_name, input: Ultimate.ULT_CMD(
                    ult_exe=Ultimate.ULT_EXE(variant=variant), 
                    ult_opts=Ultimate.ULT_COMMON_OPTS,
                    ult_task_opts=(Ultimate.ULT_REACH_OPTS(witness_dir=witness_dir, witness_name=witness_name) if task is Ultimate.ULT_REACH_TASK
                                    else Ultimate.ULT_VALIDATE_OPTS(witness_dir=witness_dir, witness_name=witness_name)), 
                    input=input)

    UAUTOMIZER_SHORT_NAME = 'uatm'
    UAUTOMIZER_FULL_NAME = 'UAutomizer'

    UTAIPAN_SHORT_NAME = 'utp'
    UTAIPAN_FULL_NAME = 'UTaipan'
    
    ULT_OUTPUT_DIR = ''
    ULT_CEX_NAME = 'UltimateCounterExample.errorpath'
    ULT_WITNESS_NAME = 'witness.graphml'
    ULT_RES_KEYWORD = 'Result:'
