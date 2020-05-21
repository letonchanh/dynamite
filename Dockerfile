FROM ubuntu:18.04

RUN \
  apt-get update -y \
  apt-get upgrade -y \
  apt-get install -y curl python git maven zip \
  apt-get install -y libpng-dev libfreetype6
  
RUN mkdir /tools
ENV WORKDIR=/tools

# Install SageMath
WORKDIR $WORKDIR
RUN \
  curl -O http://mirrors.mit.edu/sage/linux/64bit/sage-9.0-Ubuntu_18.04-x86_64.tar.bz2 \
  tar xvf sage-9.0-Ubuntu_18.04-x86_64.tar.bz2 \
  SageMath/sage
  
ENV SAGE_ROOT=/tools/SageMath
ENV PATH=$SAGE_ROOT/local/bin:$PATH
ENV PYTHONPATH=$SAGE_ROOT/local/lib/python3.7/site-packages:$PYTHONPATH

# Install Z3
WORKDIR $WORKDIR
RUN \
  git clone https://github.com/Z3Prover/z3.git \
  cd z3 \
  git checkout z3-4.8.7 \
  python scripts/mk_make.py --python \
  cd build; make
  
WORKDIR $WORKDIR
RUN \
  git clone https://github.com/ultimate-pa/ultimate.git \
  cd ultimate/ \
  git checkout v0.1.25 \
  mv trunk/examples/Automata/regression/nwa/operations/buchiComplement/ba/LowNondeterminismBüchiInterpolantAutomaton.ats trunk/examples/Automata/regression/nwa/operations/buchiComplement/ba/LowNondeterminismBuchiInterpolantAutomaton.ats \
  cd releaseScripts/default/ \
  ./makeFresh.sh
  
WORKDIR $WORKDIR
RUN \
  curl -O https://gitlab.com/sosy-lab/sv-comp/archives-2020/-/raw/master/2020/cpa-seq.zip
  unzip cpa-seq.zip
