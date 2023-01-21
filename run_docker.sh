#! /usr/bin/env bash
set -e

docker run --network host --privileged -v ${PWD}:/HARDENS --name hardens -d -it galoisinc/hardens $@
