- Install Ubuntu packages
    ```
    sudo apt-get install python ant binutils make
    ```
    
- Install Java JDK 8
    ```
    sudo apt install openjdk-8-jdk
    echo "export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64" >> ~/.bashrc
    ```
    
- NOTE: Every following step is started at `~/tools` folder

- Install SageMath
    ```
    wget http://mirrors.mit.edu/sage/linux/64bit/sage-9.0-Ubuntu_18.04-x86_64.tar.bz2
    tar xvf sage-9.0-Ubuntu_18.04-x86_64.tar.bz2
    cd SageMath
    ./sage
    echo "export SAGE_ROOT=~/tools/SageMath" >> ~/.bashrc
    echo "export PATH=$PATH:$SAGE_ROOT/local/bin" >> ~/.bashrc
    echo "export PYTHONPATH=$PYTHONPATH:$SAGE_ROOT/local/lib/python3.7/site-packages" >> ~/.bashrc
    echo "export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$SAGE_ROOT/local/lib" >> ~/.bashrc
    ```
    
- Clone Dig
    ```
    git clone https://gitlab.com/nguyenthanhvuh/dig.git
    cd dig/
    git checkout dev
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
    echo "export JPF_HOME=~/tools/jpf" >> ~/.bashrc
    echo "export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$JPF_HOME/jpf-symbc/lib" >> ~/.bashrc
    ```
    
- Install Z3 with Python3 from source
    ```
    git clone https://github.com/Z3Prover/z3.git
    git checkout z3-4.8.3
    python scripts/mk_make.py --python
    ```
