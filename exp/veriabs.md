1. Install dependencies
    ```
    apt install openjdk-8-jre libc6-dev-i386 clang perl
    add-apt-repository ppa:mhier/libboost-latest
    apt update
    apt install libboost1.68-dev
    perl -MCPAN -e install Getopt::Std
    ```
2. `scripts/veriabs --property-file /tools/loops/reach.prp /tools/loops/while_infinite_loop_1.c`