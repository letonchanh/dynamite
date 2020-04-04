1. Verification
    ```
    JAVA=/usr/lib/jvm/java-11-openjdk-amd64/bin/java \
    scripts/cpa.sh \
        -predicateAnalysis \
        -spec /tools/reachability.prp \
        -setprop counterexample.export.compressWitness=false \
        -setprop cpa.predicate.encodeBitvectorAs=INTEGER \
        /home/chanhle/repo/dynamo/benchmarks/svcomp-termination-crafted-lit/validate/Masse-VMCAI2014-Fig1a-taipan.c
    ```
    
2. Validation
  - CPAchecker
    ```
    JAVA=/usr/lib/jvm/java-11-openjdk-amd64/bin/java \
    scripts/cpa.sh \
        -witnessValidation \
        -spec /tools/reachability.prp \
        -setprop cpa.predicate.encodeBitvectorAs=INTEGER \
        -witness output/Counterexample.1.graphml \
        /home/chanhle/repo/dynamo/benchmarks/svcomp-termination-crafted-lit/validate/Masse-VMCAI2014-Fig1a-taipan.c
    ```

  - Ultimate Automizer
    ```
    ./Ultimate.py \
        --file /home/chanhle/repo/dynamo/benchmarks/svcomp-termination-crafted-lit/validate/Masse-VMCAI2014-Fig1a-taipan.c \
        --spec /tools/reachability.prp --architecture 32bit \
        --validate ~/tools/cpachecker/CPAchecker-1.9-unix/output/Counterexample.1.graphml 

    ```
