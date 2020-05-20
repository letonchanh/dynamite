FROM ubuntu:18.04

RUN \
  apt-get update -y \
  apt-get upgrade -y \
  apt-get install curl python libpng-dev libfreetype6
  
RUN mkdir /tools
WORKDIR /tools

# Install SageMath
RUN \
  curl -O http://mirrors.mit.edu/sage/linux/64bit/sage-9.0-Ubuntu_18.04-x86_64.tar.bz2 \
  tar xvf sage-9.0-Ubuntu_18.04-x86_64.tar.bz2 \
  SageMath/sage
