# Dynamo

## Installation

1. Install SageMath from conda (http://doc.sagemath.org/html/en/installation/conda.html)
    ```
    wget https://repo.anaconda.com/miniconda/Miniconda2-latest-Linux-x86_64.sh
    sh Miniconda2-latest-Linux-x86_64.sh
    conda config --add channels conda-forge
    conda create -n sage sage=8.8 python=2.7
    ```
1. `conda activate sage`
1. Install Java 8 from conda: 

    `conda install -c anaconda openjdk`
    
    `conda install openjdk=8.0.192`
    
1. `pip install lark-parser`
1. `pip install z3-solver`
1. JavaPathFinder
    ```
    mkdir jpf
    cd jpf/
    git clone https://github.com/javapathfinder/jpf-core
    git clone https://github.com/SymbolicPathFinder/jpf-symbc
    mkdir /root/.jpf
    echo 'jpf-core = /jpf/jpf-core' >> /root/.jpf/site.properties
    echo 'jpf-symbc = /jpf/jpf-symbc' >> /root/.jpf/site.properties
    echo 'extensions=${jpf-core},${jpf-symbc}' >> /root/.jpf/site.properties
    cp /dynamo/deps/dig/src/java/InvariantListenerVu.java ../jpf-symbc/src/main/gov/nasa/jpf/symbc/
    cd jpf-core/
    git checkout java-8
    ant
    cd ../jpf-symbc/
    ant
    ```
1. ENV
    ```
    export JPF_HOME=/jpf
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$JPF_HOME/jpf-symbc/lib
    ```
1. LLDB
    ```
    conda install -c conda-forge lldb
    ```

## Note

1. Remove a conda environment: `conda env remove --name myenv`
1. Search a conda package: `conda search sage --channel conda-forge`
1. Install `pip`: `sudo easy_install pip`
1. LLDB
    ```
    breakpoint set --name main
    breakpoint set --func-regex vtrace* # BreakpointCreateByRegex('vtrace*', None)
    run
    expr -i 0 -- mainQ(1, 2)
    frame variable
    ```
    - https://www.nesono.com/sites/default/files/lldb%20cheat%20sheet.pdf
    - https://opensource.apple.com/source/lldb/lldb-159/www/python-reference.html
    - https://lldb.llvm.org/use/python-reference.html#
    - https://developer.apple.com/library/archive/documentation/IDEs/Conceptual/gdb_to_lldb_transition_guide/document/lldb-terminal-workflow-tutorial.html
    
    ```
    opt = lldb.SBExpressionOptions()
    opt.SetIgnoreBreakpoints(False)
    v = target.EvaluateExpression('mainQ(1, 2)', opt)
    ```
    - https://stackoverflow.com/questions/49532342/lldb-python-callback-on-breakpoint-with-sbtarget-evaluateexpression
    - To use `lldb` in docker:
    ```
    docker run --cap-add=SYS_PTRACE --security-opt seccomp=unconfined --security-opt apparmor=unconfined --name dynamo-dev -it letonchanh/dynamo-dev bash
    ```
    - LLVM-9 (http://releases.llvm.org/9.0.0/clang+llvm-9.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz) and SageMath are incompatible on the Python `six` package.
    
