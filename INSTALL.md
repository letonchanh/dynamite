- Install Ubuntu packages
    ```
    sudo apt-get install python ant binutils make unzip bubblewrap m4
    ```
    
- Install Java JDK 8
    ```
    sudo apt install openjdk-8-jdk
    ```
    
- NOTE: Every following step is started at `~/tools` folder
    
- Clone Dig
    ```
    git clone https://gitlab.com/nguyenthanhvuh/dig.git
    cd dig/
    git checkout dev
    ```
    
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
    
- Install Z3 with Python3 from source
    ```
    git clone https://github.com/Z3Prover/z3.git
    git checkout z3-4.8.3
    python scripts/mk_make.py --python
    sudo make install
    ```
    
- Install JavaPathFinder
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
    ```
    
- Install LLDB
    ```
    sudo apt-get install cmake ninja-build build-essential subversion swig libedit-dev libncurses5-dev
    cd llvm-project
    mkdir build
    cd build
    cmake -G Ninja -DLLVM_ENABLE_PROJECTS="clang;lldb" -DPYTHON_EXECUTABLE="~/tools/SageMath/local/bin/python3" -DLLDB_CAN_USE_LLDB_SERVER=True -DCMAKE_INSTALL_PREFIX=~/tools/llvm -DCMAKE_BUILD_TYPE=Release ../llvm
    ninja lldb
    ninja lldb-server
    ```
    
- Install OCaml
    ```
    sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
    opam init
    opam switch create 4.05.0
    opam install oasis cil camlp4
    cd dynamo/deps/dig/src/ocaml
    oasis setup
    make
    mv instr.native instr.exe
    ```
    
- Config in `bashrc`
    ```
    export SAGE_ROOT=~/tools/SageMath
    export Z3=~/tools/z3
    export LLVM=~/tools/llvm-project/build
    export JPF_HOME=~/tools/jpf
    export CIVL_HOME=/tools/civl
    export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
    export PATH=$SAGE_ROOT/local/bin:$LLVM/bin:$Z3/build:$PATH
    export PYTHONPATH=$SAGE_ROOT/local/lib/python3.7/site-packages:$LLVM/lib/python3.7/site-packages:$Z3/build/python:$PYTHONPATH
    export LD_LIBRARY_PATH=$SAGE_ROOT/local/lib:$JPF_HOME/jpf-symbc/lib:$Z3/build:$LD_LIBRARY_PATH
    ```
    
- Run Dynamo
    ```
    cd dynamo/src
    python3 dynamo.py path_to_C_Java_or_Binary_example
    ```
