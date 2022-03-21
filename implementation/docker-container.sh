#!/bin/sh

docker build -t cpp2c docker/
docker run -v $PWD:/mnt -w /mnt --env CT_LLVM_INSTALL_DIR=/usr  -it cpp2c  /bin/bash
