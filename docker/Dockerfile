FROM ubuntu:21.04
RUN apt-get -y update && \
    DEBIAN_FRONTEND="noninteractive" apt-get -y install \
    # for cpp2c
    llvm-11 clang-11 libclang-11-dev build-essential cmake \
    # for m4
    help2man \
    # for xfig
    xaw3dg-dev \
    # for plan and mosiac
    libmotif-dev \
    # for mosiac
    libjpeg62-dev libxmu-headers libxpm-dev libxmu-dev \
    # for workman
    xview-clients
