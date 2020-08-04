# Instructions to setup Dynamite on Debian/Ubuntu

## Setup Prerequisite Packages

1. Install Java JDK 8 and its build systems
    ```
    sudo apt-get install -y openjdk-8-jdk maven ant
    ```
    If the package `openjdk-8-jdk` is not available, you can download its prebuilt binaries from https://github.com/AdoptOpenJDK/openjdk8-binaries/releases/download/jdk8u252-b09/OpenJDK8U-jdk_x64_linux_hotspot_8u252b09.tar.gz and extract the file to a folder (e.g `/usr/lib/jvm/java-8-openjdk-amd64`).

2. Set Java JDK 8 main folder (e.g `/usr/lib/jvm/java-8-openjdk-amd64`) to `PATH`
    ```
    export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
    export PATH=$JAVA_HOME/bin:$PATH
    ```
    
3. Install other packages
    ```
    sudo apt-get install -y curl python git zip make cmake binutils build-essential opam m4 swig psmisc
    sudo apt-get install -y libpng-dev libfreetype6 libgmp-dev
    ```

## Setup Dependencies
    
- We recommend to install the following dependencies in the same folder (e.g `/tools`) and use an environment variable (e.g `TOOLSDIR`) to refer to it.
    ```
    export TOOLSDIR=/tools
    ```

1. SageMath 9.0
    ```
    curl -O http://mirrors.mit.edu/sage/linux/64bit/sage-9.0-Ubuntu_18.04-x86_64.tar.bz2
    tar xvf sage-9.0-Ubuntu_18.04-x86_64.tar.bz2
    SageMath/sage
    
    export SAGE_ROOT=$TOOLSDIR/SageMath
    export PATH=$SAGE_ROOT/local/bin:$PATH
    export PYTHONPATH=$SAGE_ROOT/local/lib/python3.7/site-packages:$PYTHONPATH
    export LD_LIBRARY_PATH=$SAGE_ROOT/local/lib:$LD_LIBRARY_PATH
    ```
 
2. Z3 4.8.7
    ```
    git clone https://github.com/Z3Prover/z3.git
    cd z3
    git checkout z3-4.8.7
    python scripts/mk_make.py --python
    cd build; make
    
    export Z3=$TOOLSDIR/z3
    export PATH=$SAGE_ROOT/local/bin:$Z3/build:$PATH
    export PYTHONPATH=$SAGE_ROOT/local/lib/python3.7/site-packages:$Z3/build/python:$PYTHONPATH
    export LD_LIBRARY_PATH=$SAGE_ROOT/local/lib:$Z3/build:$LD_LIBRARY_PATH
    ```
    
3. PySMT and other SMT provers (CVC4, Yices)
    ```
    cp $TOOLSDIR/dynamite/deps/pysmt $TOOLSDIR/pysmt
    cd $TOOLSDIR/pysmt
    pip3 install wheel
    python3 install.py --confirm-agreement --cvc4
    python3 install.py --confirm-agreement --yices

    export PYSMT=$TOOLSDIR/pysmt
    export PYTHONPATH=$PYTHONPATH:$PYSMT
    ```
    
4. Ultimate 0.1.25
    ```
    git clone https://github.com/ultimate-pa/ultimate.git
    cd ultimate
    git checkout v0.1.25
    mv trunk/examples/Automata/regression/nwa/operations/buchiComplement/ba/LowNondeterminismBüchiInterpolantAutomaton.ats trunk/examples/Automata/regression/nwa/operations/buchiComplement/ba/LowNondeterminismBuchiInterpolantAutomaton.ats
    cd releaseScripts/default/
    ./makeFresh.sh
    
    cp $TOOLSDIR/dynamite/reachability.prp $TOOLSDIR
    
    export ULT_HOME=$TOOLSDIR/ultimate
    ```
    
5. CPAchecker 1.9 (the SV-COMP 2020 pre-built version)
    ```
    curl -O https://gitlab.com/sosy-lab/sv-comp/archives-2020/-/raw/master/2020/cpa-seq.zip
    unzip cpa-seq.zip

    export CPA_HOME=$TOOLSDIR/CPAchecker-1.9-unix
    ```
  
6. CIVL 1.20.5259
    ```
    curl -O http://vsl.cis.udel.edu:8080/lib/sw/civl/1.20/r5259/release/CIVL-1.20_5259.tgz
    tar xvf CIVL-1.20_5259.tgz
    java -jar CIVL-1.20_5259/lib/civl-1.20_5259.jar config
    
    export CIVL_HOME=$TOOLSDIR/CIVL-1.20_5259
    ```
    
 7. Java Pathfinder (JPF)
    ```
    mkdir $TOOLSDIR/jpf
    cd $TOOLSDIR/jpf
    git clone https://github.com/javapathfinder/jpf-core
    git clone https://github.com/SymbolicPathFinder/jpf-symbc
    mkdir ~/jpf
    echo 'jpf-core = /tools/jpf/jpf-core' >> ~/jpf/site.properties
    echo 'jpf-symbc = /tools/jpf/jpf-symbc' >> ~/jpf/site.properties
    echo 'extensions=${jpf-core},${jpf-symbc}' >> ~/jpf/site.properties
    cp $TOOLSDIR/dynamite/deps/dig/src/java/InvariantListenerVu.java $TOOLSDIR/jpf/jpf-symbc/src/main/gov/nasa/jpf/symbc/
    
    cd $TOOLSDIR/jpf/jpf-core
    git checkout java-8
    ant
    
    cd $TOOLSDIR/jpf/jpf-symbc
    ant
    
    export JPF_HOME=$TOOLSDIR/jpf
    ```
    
8. OCaml 4.05.0 and prerequisite libraries via Opam
    ```
    curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh | sh /dev/stdin
    opam init -y
    opam switch -y 4.05.0
    opam install -y oasis cil camlp4
    ```
    
9. Instrumentation tools
    ```
    cd $TOOLSDIR/dynamite/deps/dynamite-instr/src/cil
    eval `opam config env`
    ./configure
    make
    ```

    ```
    cd $TOOLSDIR/dynamite/deps/dig/src/ocaml
    eval `opam config env`
    oasis setup
    make
    ```
    
10. Other Python and Perl packages
    ```
    pip3 install lark-parser
    
    cpan install local::lib
    cpan install Time::Out
    cpan install YAML::Tiny
    cpan install Statistics::Basic
    ```
