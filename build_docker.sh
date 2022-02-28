#! /usr/bin/env bash

set -e
printf "Building docker container for HARDENS\n"
# Check usage -- naive for simplicity
Usage="Usage: ./build-docker.sh [-p|--push]"
doTest=1
doPush=0
while [[ $# -gt 0 ]]; do
  key="$1"
  case $key in
    -p|--push)
        doPush=1
        shift # past argument
        ;;
    *)    # unknown option
        echo "ERROR: ${Usage}"; exit 1
        ;;
  esac
done

# Env and settings
DOCKER_JFROG_PATH=artifactory.galois.com:5015
IMAGE_TAG=${DOCKER_JFROG_PATH}/hardens:latest

# clone cryptol-verilog and update its submodules prior to building the docker image
if [ -d "cryptol-verilog" ];
then echo "cryptol-verilog directory exists!"
else git clone git@gitlab-ext.galois.com:cryptol/cryptol-verilog.git
fi
# Make sure the right version checked out
cd cryptol-verilog
# Default Cryptol_verilog revision
CRYPTOL_VERILOG_REV=signed-compare
echo "Current Cryptol_verilog revision is ${CRYPTOL_VERILOG_REV}!"
git checkout ${CRYPTOL_VERILOG_REV}
git submodule update --init
cd -

# clone crymp and update submodules prior to building the docker image
if [ -d "cryptol-codegen" ];
then echo "cryptol-codegen directory exists!"
else git clone git@gitlab-ext.galois.com:cryptol/cryptol-codegen.git
fi
# Make sure the right version checked out
cd cryptol-codegen
# Default Cryptol_verilog revision
CRYPTOL_CODEGEN_REV=hardens-tweaks
echo "Current Cryptol_codegen revision is ${CRYPTOL_CODEGEN_REV}!"
git checkout ${CRYPTOL_CODEGEN_REV}
git submodule update --init
cd -

# Build the container
echo "INFO: Building the container..."
DOCKER_BUILDKIT=1 sudo docker build \
    --progress=plain \
    --tag ${IMAGE_TAG} \
    .

# once the build is complete, then remove the introduced directories and files
rm -rf cryptol-verilog cryptol-codegen

if [ $doPush -eq 1 ]; then
    echo "Logging in to the docker repository"
    docker login ${DOCKER_JFROG_PATH}
    echo "INFO: Pushing the image..."
    docker push ${IMAGE_TAG}
    echo "INFO: Logout from the docker repo"
    docker logout ${DOCKER_JFROG_PATH}
fi
