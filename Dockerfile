FROM ubuntu:21.04

ARG DEBIAN_FRONTEND=noninteractive
RUN mkdir /tools
ARG VERSION_LOG=/tools/log.txt
RUN echo "Installed tools:" >> ${VERSION_LOG}

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y wget git python pip \
    python3-dev software-properties-common \
    iproute2 usbutils srecord \
    build-essential clang bison flex \
    libreadline-dev gawk tcl-dev libffi-dev git \
    graphviz xdot pkg-config python3 libboost-system-dev \
    libboost-python-dev libboost-filesystem-dev zlib1g-dev \
    libboost-all-dev python3 python3-pip \
    cmake openocd \
    libeigen3-dev qtbase5-dev qtchooser qt5-qmake qtbase5-dev-tools \
    autoconf automake autotools-dev curl libmpc-dev \
    libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf \
    libtool patchutils bc zlib1g-dev libexpat-dev \
    libftdi-dev unzip \
    cabal-install libffi7 \
    libftdi1-2 libftdi1-dev libhidapi-libusb0 libhidapi-dev libudev-dev make g++ \
    clang libc++-dev libc++abi-dev nodejs python2 npm \
    iverilog verilator \
    vim

# Yosys
ARG TOOL=yosys
ARG TAG=yosys-0.13
ARG REPO=https://github.com/YosysHQ/yosys.git
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN \
    git checkout ${TAG} \
    && make -j$(nproc) \
    && make install PREFIX=/opt
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Trellis
ARG TOOL=prjtrellis
ARG TAG=1.1
ARG REPO=https://github.com/YosysHQ/prjtrellis.git
RUN git clone --recursive ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}/libtrellis
RUN \
    git checkout ${TAG} \
    && cmake -DCMAKE_INSTALL_PREFIX=/opt . \
    && make -j$(nproc) \
    && make install
ENV TRELLIS="/opt/share/trellis"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# nextpnr
ARG TOOL=nextpnr
ARG TAG=nextpnr-0.1
ARG REPO=https://github.com/YosysHQ/nextpnr.git
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN \
    git checkout ${TAG} \
    && cmake . -DARCH=ecp5 -DTRELLIS_INSTALL_PREFIX=/opt \
    && make -j$(nproc) \
    && make install
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# RISCV toolchain
ARG TOOL=riscv-gnu-toolchain
ARG TAG=2022.01.17
ARG REPO=https://github.com/riscv/riscv-gnu-toolchain
RUN git clone --recursive ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN \
    git checkout ${TAG} \
    &&  ./configure --prefix=/opt/riscv --enable-multilib \
    && export MAKEFLAGS="-j$(nproc)" \
    && make \
    && make linux
ENV PATH="/opt/riscv/bin:/opt/bin:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# ecpprog
ARG TOOL=ecpprog
ARG TAG=7212b56a9d2fc6de534e06636a1c6d8b0c6f80ab
ARG REPO=https://github.com/gregdavill/ecpprog
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}/ecpprog
RUN \
    git checkout ${TAG} \
    && make -j$(nproc) \
    && make install
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Iverilog
RUN echo "`iverilog -v | head -1`" >> ${VERSION_LOG}

# Bluespec compiler
ARG TOOL=bluespec-compiler
ARG TAG=bsc-2021.07-ubuntu-20.04
ARG REPO=https://github.com/B-Lang-org/bsc
WORKDIR /tmp
RUN \
    wget ${REPO}/releases/download/2021.07/${TAG}.tar.gz \
    && tar xvzf ${TAG}.tar.gz \
    && mv ${TAG} /tools/${TAG} \
    && rm ${TAG}.tar.gz
ENV PATH="/tools/${TAG}/bin:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Verilator
RUN echo "`verilator --version`" >> ${VERSION_LOG}

# OpenFPGAloader
ARG TOOL=openFPGALoader
ARG TAG=v0.7.0
ARG REPO=https://github.com/trabucayre/openFPGALoader.git
RUN \
    git clone ${REPO} /tmp/${TOOL} \
    && cd /tmp/${TOOL} \
    && git checkout ${TAG}
RUN mkdir /tmp/${TOOL}/build
WORKDIR /tmp/${TOOL}/build
RUN \
    cmake ../ \
    && cmake --build . \
    && make install
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# NOTE: these might be necessary for properly connecting USB devices
#WORKDIR /tools/${TOOL}
#RUN cp 99-openfpgaloader.rules /etc/udev/rules.d/
#RUN udevadm control --reload-rules && sudo udevadm trigger
#RUN usermod -a $USER -G plugdev

# elf2hex
ARG TOOL=elf2hex
ARG TAG=v20.08.00.00
ARG REPO=https://github.com/sifive/elf2hex.git
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN \
    git checkout ${TAG} \
    && autoreconf -i \
    && ./configure --target=riscv64-unknown-elf \
    && make \
    && make install
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Bluespec libraries
ARG TOOL=bsc-contrib
ARG TAG=aa205330885f6955e24fd99a0319e2733b5353f1
ARG REPO=https://github.com/B-Lang-org/bsc-contrib.git
RUN git clone ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}
RUN \
    git checkout ${TAG} \
    && make PREFIX=/tools/bsc-2021.07-ubuntu-20.04/
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# GHC and Cabal
RUN cabal update

# cryptol 2.11
ARG TOOL=cryptol
ARG TAG=dfae4580e322584185235f301bc8a03b6bc19a65
ARG REPO=https://github.com/GaloisInc/cryptol.git
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN \
    git checkout ${TAG} \
    && git submodule update --init \
    && ./cry build \
    && cabal v2-install --installdir=/tools
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Z3 solver
ARG TOOL=z3
ARG TAG=4.8.14-x64-glibc-2.31
ARG REPO=https://github.com/Z3Prover/z3/releases/download/z3-4.8.14
WORKDIR /tmp
RUN wget ${REPO}/${TOOL}-${TAG}.zip
RUN unzip ${TOOL}-${TAG}.zip
RUN    mv ${TOOL}-${TAG} /tools/${TOOL}
ENV PATH="/tools/${TOOL}/bin:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# SAW
ARG TOOL=saw
ARG TAG=e2fef66d7cf4c67ecb86b0fe096977cd7e925183
ARG REPO=https://github.com/GaloisInc/saw-script.git
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN git checkout ${TAG} \
    && git submodule update --init \
    && ./build.sh \
    && cp bin/saw /usr/local/bin
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# cryptol-verilog
ARG TOOL=cryptol-verilog
COPY ${TOOL} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN \
    cabal v2-build \
    && cabal v2-install --installdir=/tools

# Crymp
ARG TOOL=cryptol-codegen
COPY ${TOOL} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN \
    cabal build \
    && cabal install --installdir=/tools

ENV PATH="/tools/:${PATH}"

# Fret
# ARG TOOL=fret
# ARG TAG=7dbfbf65d8b7f96e9f1fdca2dd19a2a2387d2674
# ARG REPO=https://github.com/NASA-SW-VnV/fret.git
# RUN git clone ${REPO} /tools/${TOOL}
# WORKDIR /tools/${TOOL}
# RUN git checkout ${TAG} \
#     && git submodule update --init
# WORKDIR /tools/${TOOL}/fret-electron
# # Change https://github.com/NASA-SW-VnV/fret/blob/master/fret-electron/package.json#L249 to "redux-thunk": "^2.4.1" and
# # https://github.com/NASA-SW-VnV/fret/blob/master/fret-electron/package.json#L248 to "redux": :^4"
# RUN npm run fret-install
# # NOTE: npm run start still fails, likely because it requires X server which is not availale in Docker
# RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Lando/Lobot
ARG TOOL=Lando
ARG TAG=428ea1174de2bed7c069a6ef8edb30ca75ed441a
ARG REPO=https://github.com/GaloisInc/BESSPIN-Lando.git
RUN git clone ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}
RUN apt-get install -y maven
RUN ./lando.sh -r
ENV PATH="/tools/${TOOL}:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Clean tmp files
RUN rm -rf /tmp/*

RUN cat ${VERSION_LOG}

WORKDIR /
