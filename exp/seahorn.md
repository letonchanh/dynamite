# Seahorn (Ubuntu 16.04 with LLVM 3.6.0)

0. `docker run -v ~/tools/sv-benchmarks/:/sv-benchmarks -it ubuntu:16.04 bash`
1. `apt-get update`
2. `apt-get upgrade`
3. 
    ```
    apt-get install bridge-utils && \
    apt-get install -qq build-essential clang-3.6 && \
    apt-get install -qq software-properties-common && \
    apt-get install -qq curl git ninja-build man subversion vim wget cmake && \
    apt-get install -qq libboost-program-options-dev && \
    apt-get install -y python2.7 python2.7-dev && \
    apt-get install -y libboost-all-dev && \
    apt-get install -y libgmp-dev libncurses5-dev libboost-all-dev libz-dev && \
    apt-get install -y python-pip
    ```
3. `sudo apt install g++-5 gcc-5` for a newer version of Ubuntu
3. Build LLVM-3.6 (optional, it will be built together with seahorn)
    ```
    git clone https://github.com/llvm/llvm-project.git
    cd llvm-project/
    git checkout llvmorg-3.6.2
    
    (cp -r clang llvm/tools)
    
    mkdir build
    cd build/
    
    (../llvm/configure --disable-bindings --prefix=/tools/llvm)
    (make)
    (sudo make install)
    
    cmake -G Ninja -DLLVM_TARGETS_TO_BUILD:STRING=X86 -DWITH_POLLY:BOOL=OFF -DLLVM_ENABLE_PEDANTIC=OFF -DLLVM_ENABLE_PIC=ON -DLLVM_REQUIRES_RTTI:BOOL=TRUE -DLLVM_EXTERNAL_CLANG_SOURCE_DIR:PATH=/home/chanhle/repo/llvm-project/clang ../llvm
    ninja
    
    sudo update-alternatives --install /usr/bin/clang++ clang++ /tools/llvm/bin/clang++ 100
    sudo update-alternatives --install /usr/bin/clang clang /tools/llvm/bin/clang 100
    ```
4. `git clone https://github.com/seahorn/seahorn`
5. `cd seahorn/`
6. `git checkout d48cfe8`
7. `mkdir build && cd build`
8. `/usr/bin/cmake -DCMAKE_C_COMPILER=/usr/bin/gcc-5 -DCMAKE_CXX_COMPILER=/usr/bin/g++-5 -DCMAKE_BUILD_TYPE=Release -DCMAKE_PROGRAM_PATH=/usr/bin  -DCMAKE_INSTALL_PREFIX=run ../`
9. `/usr/bin/cmake --build . --target extra`
10. `cmake --build .  && cmake /home/chanhle/repo/seahorn`
10. `cmake --build .`
11. `/usr/bin/cmake --build . --target install`
12. `/seahorn/build/run/bin/sea_svcomp --cex=error-witness.graphml -m64 --spec=/sv-benchmarks/c/termination-restricted-15/ALL.prp /sv-benchmarks/c/termination-restricted-15/c.01-no-inv_true-termination.c`


