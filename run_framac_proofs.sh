#! /usr/bin/env bash
set -e

docker run -v ${PWD}:/HARDENS -it \
    framac/frama-c:dev \
    make -C /HARDENS/src -f frama_c.mk
