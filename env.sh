# Set up the environment for using Dynamo
export TOOL_ROOT=/tools

export SAGE_ROOT=$TOOL_ROOT/SageMath
export Z3=$TOOL_ROOT/z3
export LLVM=$TOOL_ROOT/llvm-project/build
export JPF_HOME=$TOOL_ROOT/jpf
export CIVL_HOME=$TOOL_ROOT/civl

export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH=$SAGE_ROOT/local/bin:$LLVM/bin:$Z3/build:$PATH
export PYTHONPATH=$SAGE_ROOT/local/lib/python3.7/site-packages:$LLVM/lib/python3.7/site-packages:$Z3/build/python:$PYTHONPATH
export LD_LIBRARY_PATH=$SAGE_ROOT/local/lib:$JPF_HOME/jpf-symbc/lib:$Z3/build:$LD_LIBRARY_PATH
