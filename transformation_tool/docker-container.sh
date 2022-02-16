#!/bin/sh

docker build -t cpp-to-c docker/
docker run -v $PWD:/mnt -w /mnt --env CT_LLVM_INSTALL_DIR=/usr  -it cpp-to-c  /bin/bash
