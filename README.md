# Dynamo

## Installation

1. Install SageMath from conda (http://doc.sagemath.org/html/en/installation/conda.html)
    ```
    conda create -n sage sage=8.8 python=2.7
    ```
1. `conda activate sage`
1. Install Java 8 from conda: 

    `conda install -c anaconda openjdk`
    
    `conda install openjdk=8.0.192`
    
1. `pip install lark-parser`

## Note

1. Remove a conda environment: `conda env remove --name myenv`
1. Search a conda package: `conda search sage --channel conda-forge`
1. Install `pip`: `sudo easy_install pip`
1. LLDB
    ```
    breakpoint set --name main
    breakpoint set --func-regex vtrace*
    run
    expr -i 0 -- mainQ(1, 2)
    frame variable
    ```
    https://www.nesono.com/sites/default/files/lldb%20cheat%20sheet.pdf
    https://opensource.apple.com/source/lldb/lldb-159/www/python-reference.html
    https://lldb.llvm.org/use/python-reference.html#
    https://developer.apple.com/library/archive/documentation/IDEs/Conceptual/gdb_to_lldb_transition_guide/document/lldb-terminal-workflow-tutorial.html
    
    ```
    opt = lldb.SBExpressionOptions()
    opt.SetIgnoreBreakpoints(False)
    v = target.EvaluateExpression('mainQ(1, 2)', opt)
    ```
    https://stackoverflow.com/questions/49532342/lldb-python-callback-on-breakpoint-with-sbtarget-evaluateexpression
