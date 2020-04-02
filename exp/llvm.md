1. Install LLVM and Clang from LLVM APT:
    ```
    wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key | sudo apt-key add -
    sudo apt-add-repository "deb http://apt.llvm.org/bionic/ llvm-toolchain-bionic-6.0 main"
    sudo apt-get update
    sudo apt-get install -y clang-6.0
    ```
- Available packages:
    ```
    llvm-toolchain-bionic-10/                          24-Mar-2020 02:21                   -
    llvm-toolchain-bionic-5.0/                         09-May-2018 14:53                   -
    llvm-toolchain-bionic-6.0/                         09-Mar-2019 06:41                   -
    llvm-toolchain-bionic-7/                           06-Apr-2019 17:25                   -
    llvm-toolchain-bionic-8/                           14-Jan-2020 22:25                   -
    llvm-toolchain-bionic-9/                           12-Dec-2019 10:07                   -
    ```
    
2. Compile from source:
    ```
    build$ cmake -G Ninja ../llvm
    build$ ninja
    ```
