FROM ubuntu:18.04

RUN \
  apt-get update -y \
  apt-get upgrade -y \
  apt-get install -y curl python git \
  apt-get install -y libpng-dev libfreetype6
  
RUN mkdir /tools
WORKDIR /tools

# Install SageMath
RUN \
  curl -O http://mirrors.mit.edu/sage/linux/64bit/sage-9.0-Ubuntu_18.04-x86_64.tar.bz2 \
  tar xvf sage-9.0-Ubuntu_18.04-x86_64.tar.bz2 \
  SageMath/sage
  
ENV SAGE_ROOT=/tools/SageMath
ENV PATH=$SAGE_ROOT/local/bin:$PATH
ENV PYTHONPATH=$SAGE_ROOT/local/lib/python3.7/site-packages:$PYTHONPATH

# Install Z3
RUN \
  git clone https://github.com/Z3Prover/z3.git \
  cd z3 \
  git checkout z3-4.8.7 \
  python scripts/mk_make.py --python \
  cd build; make
