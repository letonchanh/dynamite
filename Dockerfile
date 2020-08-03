FROM ubuntu:18.04

RUN apt-get update -y
RUN apt-get upgrade -y
RUN apt-get install -y openjdk-8-jdk maven ant
RUN apt-get install -y curl python git zip make cmake binutils build-essential opam m4 swig psmisc
RUN apt-get install -y libpng-dev libfreetype6 libgmp-dev
  
RUN mkdir /tools
ENV TOOLSDIR=/tools

ENV JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
ENV PATH=$JAVA_HOME/bin:$PATH

# RUN java -version

# Install SageMath
WORKDIR $TOOLSDIR
RUN curl -O http://mirrors.mit.edu/sage/linux/64bit/sage-9.0-Ubuntu_18.04-x86_64.tar.bz2
RUN tar xvf sage-9.0-Ubuntu_18.04-x86_64.tar.bz2
RUN SageMath/sage
  
ENV SAGE_ROOT=$TOOLSDIR/SageMath
ENV PATH=$SAGE_ROOT/local/bin:$PATH
ENV PYTHONPATH=$SAGE_ROOT/local/lib/python3.7/site-packages:$PYTHONPATH
ENV LD_LIBRARY_PATH=$SAGE_ROOT/local/lib:$LD_LIBRARY_PATH

# Install Z3
WORKDIR $TOOLSDIR
RUN git clone https://github.com/Z3Prover/z3.git
RUN \
  cd z3; git checkout z3-4.8.7 && \
  python scripts/mk_make.py --python && \
  cd build; make

ENV Z3=/tools/z3
ENV PATH=$SAGE_ROOT/local/bin:$Z3/build:$PATH
ENV PYTHONPATH=$SAGE_ROOT/local/lib/python3.7/site-packages:$Z3/build/python:$PYTHONPATH
ENV LD_LIBRARY_PATH=$SAGE_ROOT/local/lib:$Z3/build:$LD_LIBRARY_PATH
  
# Install Ultimate
WORKDIR $TOOLSDIR
RUN git clone https://github.com/ultimate-pa/ultimate.git
RUN \
  java -version && \
  cd ultimate; git checkout v0.1.25 && \
  mv trunk/examples/Automata/regression/nwa/operations/buchiComplement/ba/LowNondeterminismBüchiInterpolantAutomaton.ats trunk/examples/Automata/regression/nwa/operations/buchiComplement/ba/LowNondeterminismBuchiInterpolantAutomaton.ats && \
  cd releaseScripts/default/ && \
  ./makeFresh.sh
ENV ULT_HOME=$TOOLSDIR/ultimate
  
# Install CPAchecker
WORKDIR $TOOLSDIR
RUN curl -O https://gitlab.com/sosy-lab/sv-comp/archives-2020/-/raw/master/2020/cpa-seq.zip
RUN unzip cpa-seq.zip
ENV CPA_HOME=$TOOLSDIR/CPAchecker-1.9-unix

# Install CIVL
WORKDIR $TOOLSDIR
RUN curl -O http://vsl.cis.udel.edu:8080/lib/sw/civl/1.20/r5259/release/CIVL-1.20_5259.tgz
RUN tar xvf CIVL-1.20_5259.tgz
RUN java -jar CIVL-1.20_5259/lib/civl-1.20_5259.jar config
ENV CIVL_HOME=$TOOLSDIR/CIVL-1.20_5259

# Install opam
# RUN curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh | sh /dev/stdin
RUN opam init -y
RUN opam switch -y 4.05.0
RUN opam install -y oasis cil camlp4

# Install PySMT and provers
COPY ./deps/pysmt $TOOLSDIR/pysmt
WORKDIR $TOOLSDIR/pysmt
RUN pip3 install wheel
RUN \
  python3 install.py --cvc4 && \
  python3 install.py --yices

ENV PYSMT=$TOOLSDIR/pysmt
ENV PYTHONPATH=$SAGE_ROOT/local/lib/python3.7/site-packages:$Z3/build/python:$PYSMT:$PYTHONPATH

COPY . $TOOLSDIR/dynamite

# Install JPF
WORKDIR $TOOLSDIR
RUN mkdir jpf
WORKDIR $TOOLSDIR/jpf
RUN git clone https://github.com/javapathfinder/jpf-core
RUN git clone https://github.com/SymbolicPathFinder/jpf-symbc
RUN mkdir ~/jpf
RUN echo 'jpf-core = /tools/jpf/jpf-core' >> ~/jpf/site.properties
RUN echo 'jpf-symbc = /tools/jpf/jpf-symbc' >> ~/jpf/site.properties
RUN echo 'extensions=${jpf-core},${jpf-symbc}' >> ~/jpf/site.properties
RUN cp $TOOLSDIR/dynamite/deps/dig/src/java/InvariantListenerVu.java $TOOLSDIR/jpf/jpf-symbc/src/main/gov/nasa/jpf/symbc/
WORKDIR $TOOLSDIR/jpf/jpf-core
RUN git checkout java-8
RUN ant
WORKDIR $TOOLSDIR/jpf/jpf-symbc
RUN ant
ENV JPF_HOME=$TOOLSDIR/jpf

WORKDIR $TOOLSDIR/dynamite/deps/dynamo-instr/src/cil
RUN \
  eval `opam config env` && \
  ./configure && \
  make

WORKDIR $TOOLSDIR/dynamite/deps/dig/src/ocaml
RUN \
  eval `opam config env` && \
  oasis setup && \
  make

RUN pip3 install lark-parser

ENV DYNAMITE_DEPS=$TOOLSDIR
RUN cp $TOOLSDIR/dynamite/reachability.prp $TOOLSDIR

RUN cpan install local::lib
RUN cpan install Time::Out
RUN cpan install YAML::Tiny
RUN cpan install Statistics::Basic

WORKDIR $TOOLSDIR/dynamite/benchmarks
