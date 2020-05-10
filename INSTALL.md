- Install Ubuntu packages
    ```
    sudo apt-get install python ant binutils make unzip bubblewrap m4
    ```
    
- Install Java JDK 8
    ```
    sudo apt install openjdk-8-jdk
    ```
    
- NOTE: Every following step is started at `~/tools` folder
    
- Clone Dynamo
    ```
    git clone --recurse-submodules https://github.com/letonchanh/dynamo.git
    ```
    
- Install SageMath
    ```
    wget http://mirrors.mit.edu/sage/linux/64bit/sage-9.0-Ubuntu_18.04-x86_64.tar.bz2
    tar xvf sage-9.0-Ubuntu_18.04-x86_64.tar.bz2
    cd SageMath
    ./sage
    ```
    
- Install `lark-parser`
    ```
    pip3 install lark-parser
    ```
    
- Install Z3 with Python3 from source
    ```
    git clone https://github.com/Z3Prover/z3.git
    cd z3
    git checkout z3-4.8.7
    python scripts/mk_make.py --python
    sudo make install
    ```
    
- Install CVC4 (optional)
    ```
    git clone https://github.com/CVC4/CVC4.git
    cd CVC4
    ./contrib/get-antlr-3.4
    CC=/tools/SageMath/local/bin/gcc CXX=/tools/SageMath/local/bin/g++ ./configure.sh --language-bindings=python --python3
    cd build
    make
    ```
    
- Install `pysmt` and solvers (CVC4, Yices):
    ```
    git clone git@github.com:letonchanh/pysmt.git
    pip3 install wheel
    CC=/tools/SageMath/local/bin/gcc CXX=/tools/SageMath/local/bin/g++ python3 install.py --cvc4
    python3 install.py --yices
    ```
    
- Install Ultimate
    ```
    apt-get install maven zip
    git clone https://github.com/ultimate-pa/ultimate.git
    cd ultimate/
    git checkout v0.1.25
    cd releaseScripts/default/
    ./makeFresh.sh
    ```
    If the build fails, try
    ```
    mv ../../trunk/examples/Automata/regression/nwa/operations/buchiComplement/ba/LowNondeterminismBüchiInterpolantAutomaton.ats ../../trunk/examples/Automata/regression/nwa/operations/buchiComplement/ba/LowNondeterminismBuchiInterpolantAutomaton.ats
    ```
    
- Install CPAchecker
    ```
    wget https://gitlab.com/sosy-lab/sv-comp/archives-2020/-/raw/master/2020/cpa-seq.zip
    unzip cpa-seq.zip
    ```
    
- Install JavaPathFinder (optional)
    ```
    mkdir jpf; cd jpf
    git clone https://github.com/javapathfinder/jpf-core
    git clone https://github.com/SymbolicPathFinder/jpf-symbc
    mkdir ~/jpf
    echo 'jpf-core = ~/tools/jpf/jpf-core' >> ~/jpf/site.properties
    echo 'jpf-symbc = ~/tools/jpf/jpf-symbc' >> ~/jpf/site.properties
    echo 'extensions=${jpf-core},${jpf-symbc}' >> ~/jpf/site.properties
    cp ../dig/src/java/InvariantListenerVu.java jpf-symbc/src/main/gov/nasa/jpf/symbc/
    cd jpf-core/
    git checkout java-8
    ant
    cd ../jpf-symbc/
    ant
    ```
    
- Install CIVL
    ```
    wget http://vsl.cis.udel.edu:8080/lib/sw/civl/1.20/r5259/release/CIVL-1.20_5259.tgz
    tar xvf CIVL-1.20_5259.tgz
    java -jar lib/civl-1.20_5259.jar config
    ```
    
- Install LLDB (optional)
    ```
    sudo apt-get install cmake ninja-build build-essential subversion swig libedit-dev libncurses5-dev
    git clone https://github.com/llvm/llvm-project.git
    git checkout llvmorg-9.0.1
    cd llvm-project
    mkdir build
    cd build
    cmake -G Ninja -DLLVM_ENABLE_PROJECTS="clang;lldb" -DPYTHON_EXECUTABLE="~/tools/SageMath/local/bin/python3" -DLLDB_CAN_USE_LLDB_SERVER=True -DCMAKE_INSTALL_PREFIX=~/tools/llvm -DCMAKE_BUILD_TYPE=Release ../llvm
    ninja lldb
    ninja lldb-server
    ```
    
- Install Omega (optional, https://github.com/davewathaverford/the-omega-project, http://www.cs.umd.edu/projects/omega/)
    ```
    apt install g++-5 gcc-5
    update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-5 50
    update-alternatives --config g++
    update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-5 50
    update-alternatives --config gcc
    PATH=/usr/bin:$PATH make (oc|all)
    ```
    
- Install OCaml and build instrumentation tools
    ```
    sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
    opam init
    opam switch create 4.05.0
    opam install oasis cil camlp4
    ```
    
    ```
    cd dynamo/deps/dig/src/ocaml
    oasis setup
    make
    ```
    
    ```
    cd dynamo/deps/dynamo-instr/src/cil
    ./configure
    make
    ```
    
- Config in `bashrc`
    ```
    export SAGE_ROOT=/tools/SageMath
    export Z3=/tools/z3
    export LLVM=/tools/llvm-project/build
    export JPF_HOME=/tools/jpf
    export CIVL_HOME=/tools/civl
    export CPA_HOME=/tools/CPAchecker-1.9-unix
    export ULT_HOME=/tools/ultimate
    export PYSMT=/tools/pysmt
    export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
    export PATH=$SAGE_ROOT/local/bin:$LLVM/bin:$Z3/build:$PATH
    export PYTHONPATH=$SAGE_ROOT/local/lib/python3.7/site-packages:$LLVM/lib/python3.7/site-packages:$Z3/build/python:$PYSMT:$PYTHONPATH
    export LD_LIBRARY_PATH=$SAGE_ROOT/local/lib:$JPF_HOME/jpf-symbc/lib:$Z3/build:$LD_LIBRARY_PATH
    ```
    
- Run Dynamo
    ```
    cd dynamo/src
    python3 dynamo.py path_to_C_Java_or_Binary_example
    ```
