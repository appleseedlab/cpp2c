FROM ubuntu:21.04
RUN apt-get -y update && \
    # add repo for python3.8
    sudo add-apt-repository ppa:deadsnakes/ppa -y && \
    # install packages
    DEBIAN_FRONTEND="noninteractive" apt-get -y install \
    # for cpp2c
    llvm-11 clang-11 libclang-11-dev build-essential cmake \
    # for evaluation
    software-properties-common python3.8 \
    # for bc
    makeinfo \
    # for zsh
    autoconf \
    # for m4 and gnuchess
    help2man \
    # for gv and xfig
    xaw3dg-dev \
    # for plan and mosiac
    libmotif-dev \
    # for mosiac
    libpng-dev libjpeg62-dev libxmu-headers libxpm-dev libxmu-dev \
    # for workman
    xview-clients \
    # for RasMol
    libcqrlib-dev