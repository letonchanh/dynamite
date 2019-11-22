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
    apt-get install python2.7 python2.7-dev -y && \
    apt-get install -y libboost1.55-all-dev && \
    apt-get install -y libgmp-dev libncurses5-dev libboost-all-dev libz-dev && \
    apt-get install -y python-pip
    ```
4. `git clone https://github.com/seahorn/seahorn`
5. `cd seahorn/`
6. `git checkout d48cfe8`
7. `mkdir build && cd build`
8. `/usr/bin/cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_PROGRAM_PATH=/usr/bin  -DCMAKE_INSTALL_PREFIX=run ../`
9. `/usr/bin/cmake --build . --target extra`
10. `cmake --build .`
11. `/usr/bin/cmake --build . --target install`
12. `/seahorn/build/run/bin/sea_svcomp --cex=error-witness.graphml -m64 --spec=/sv-benchmarks/c/termination-restricted-15/ALL.prp /sv-benchmarks/c/termination-restricted-15/c.01-no-inv_true-termination.c`


