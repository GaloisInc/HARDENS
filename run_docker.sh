#! /usr/bin/env bash
set -e

sudo docker run --network host --privileged -v ${PWD}:/HARDENS -it \
    artifactory.galois.com:5015/hardens:latest \
    $@
