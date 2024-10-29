#    Copyright 2021, 2022, 2023, 2024 Galois, Inc.
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.

# Base
FROM ubuntu:22.04 as base
ARG DEBIAN_FRONTEND=noninteractive
RUN mkdir /tools
WORKDIR /

RUN apt-get update --allow-insecure-repositories \
    && apt-get upgrade -y
RUN apt-get install -y \
    autoconf \
    automake \
    autotools-dev \
    bc \
    bison \
    build-essential \
    clang \
    cmake \
    curl \
    default-jre \
    flex \
    g++ \
    gawk \
    git \
    git \
    gperf \
    graphviz \
    iproute2 \
    iverilog \
    libboost-all-dev \
    libboost-filesystem-dev \
    libboost-program-options-dev \
    libboost-python-dev \
    libboost-system-dev \
    libc++-dev \
    libc++abi-dev \
    libeigen3-dev \
    libexpat-dev \
    libffi-dev \
    libffi7 \
    libftdi-dev \
    libftdi1-2 \
    libftdi1-dev \
    libgmp-dev \
    libhidapi-dev \
    libhidapi-libusb0 \
    libmpc-dev \
    libmpfr-dev \
    libreadline-dev \
    librsvg2-bin \
    libtinfo-dev \
    libtool \
    libudev-dev \
    make \
    mercurial \
    nodejs \
    npm \
    openocd \
    pandoc \
    patchutils \
    pip \
    pkg-config \
    python2 \
    python3 \
    python3-dev \
    python3-pip \
    qt5-qmake \
    qtbase5-dev \
    qtbase5-dev-tools \
    qtchooser \
    software-properties-common \
    srecord \
    tcl-dev \
    texinfo \
    texlive-full \
    unzip \
    usbutils \
    verilator \
    vim \
    wget \
    xdot \
    zlib1g-dev

# Builder
FROM base as builder
ARG VERSION_LOG=/tools/log.txt
RUN echo "Installed tools:" >> ${VERSION_LOG}

# Yosys
ARG TOOL=yosys
ARG TAG=yosys-0.17
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
ARG TAG=1.2.1
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

# NextPNR
ARG TOOL=nextpnr
ARG TAG=nextpnr-0.3
ARG REPO=https://github.com/YosysHQ/nextpnr.git
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN \
    git checkout ${TAG} \
    && cmake . -DARCH=ecp5 -DTRELLIS_INSTALL_PREFIX=/opt \
    && make -j$(nproc) \
    && make install
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# RISC-V GCC Toolchain
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

# ECPProg
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

# IVerilog
RUN echo "`iverilog -v | head -1`" >> ${VERSION_LOG}

# Bluespec Compiler
# We have to bump to at least 2023.01 in order to support Ubuntu 22.04.
ARG TOOL=bluespec-compiler
ARG TAG=bsc-2023.01-ubuntu-22.04
ARG REPO=https://github.com/B-Lang-org/bsc
WORKDIR /tmp
RUN \
    wget ${REPO}/releases/download/2023.01/${TAG}.tar.gz \
    && tar xzf ${TAG}.tar.gz \
    && chown -R root:root ${TAG} \
    && mv ${TAG} /tools/${TAG} \
    && rm ${TAG}.tar.gz
ENV PATH="/tools/${TAG}/bin:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Verilator
RUN echo "`verilator --version`" >> ${VERSION_LOG}

# OpenFPGALoader
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

# ELF2HEX
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
# These are not building for the version of BSC we have installed in
# Ubuntu 22.x for now, so this is being commented out.
# ARG TOOL=bsc-contrib
# ARG TAG=c9d4f1b7415e4b1053b6934614e91bceafeacf04
# ARG REPO=https://github.com/B-Lang-org/bsc-contrib.git
# RUN git clone ${REPO} /tools/${TOOL}
# WORKDIR /tools/${TOOL}
# RUN \
#     git checkout ${TAG} \
#     && make PREFIX=/tools/bsc-2023.01-ubuntu-22.04/
# RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# GHC and Cabal
RUN \
    wget https://downloads.haskell.org/~ghcup/x86_64-linux-ghcup -O /usr/local/bin/ghcup \
    && chmod +x /usr/local/bin/ghcup
ENV PATH="/root/.ghcup/bin:${PATH}"
RUN \
    ghcup install ghc 8.10.7 \
    && ghcup set ghc 8.10.7 \
    && ghcup install cabal
RUN cabal update

# Cryptol
# This pinned commit is the version that is known to work with the
# HARDENS assurance case.
ARG TOOL=cryptol
ARG TAG=dfae4580e322584185235f301bc8a03b6bc19a65
ARG REPO=https://github.com/GaloisInc/cryptol.git
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
# Build fix for LTS GHC.
RUN echo "constraints:" > cabal.project.local
RUN echo "  parameterized-utils < 2.1.6" >> cabal.project.local
RUN \
    git checkout ${TAG} \
    && git submodule update --init \
    && ./cry build \
    && cabal v2-install --installdir=/tools
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# SAW
# The latest version of SAW as of this commit (v1.2) works just
# fine with the HARDENS assurance case.
ARG TOOL=saw
ARG TAG=v1.2
ARG REPO=https://github.com/GaloisInc/saw-script/releases/download/${TAG}
WORKDIR /tmp
RUN wget ${REPO}/${TOOL}-1.2-ubuntu-20.04-X64-with-solvers.tar.gz
RUN \
    tar xzf ${TOOL}-1.2-ubuntu-20.04-X64-with-solvers.tar.gz \
    && chown -R root:root ${TOOL}-1.2-ubuntu-20.04-X64-with-solvers \
    && mv ${TOOL}-1.2-ubuntu-20.04-X64-with-solvers /tools/${TOOL}
ENV PATH="/tools/${TOOL}/bin:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

########################################
# RISCV-Formal
#######################################
ARG TOOL=SymbiYosys
ARG TAG=419ef76f82b3973e356815f63fc919218b2860bb
ARG REPO=https://github.com/YosysHQ/SymbiYosys.git
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN make install
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

ARG TOOL=boolector
ARG TAG=3.2.2
ARG REPO=https://github.com/boolector/boolector
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN ./contrib/setup-btor2tools.sh
RUN ./contrib/setup-lingeling.sh
RUN ./configure.sh
RUN make -C build -j$(nproc)
RUN cp build/bin/boolector /usr/local/bin/
RUN cp build/bin/btor* /usr/local/bin/
#RUN cp deps/btor2tools/bin/btorsim /usr/local/bin/
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# NuSMV
# wget https://nusmv.fbk.eu/distrib/NuSMV-2.6.0-linux64.tar.gz
# tar xzf NuSMV-2.6.0-linux64.tar.gz
# cp NuSMV-2.6.0-Linux/bin/* /usr/local/bin/

# JKind-1
# wget https://github.com/andreaskatis/jkind-1/releases/download/v2.0/jkind
# wget https://github.com/andreaskatis/jkind-1/releases/download/v2.0/jkind.jar
# wget https://github.com/andreaskatis/jkind-1/releases/download/v2.0/jlustre2kind
# wget https://github.com/andreaskatis/jkind-1/releases/download/v2.0/jrealizability
# chmod 755 jkind jlustre2kind jrealizability
# cp * /usr/local/bin/

# Kind 2
# wget https://github.com/kind2-mc/kind2/releases/download/v1.6.0/kind2-v1.6.0-linux-x86_64.tar.gz
# wget https://github.com/kind2-mc/kind2/releases/download/v1.6.0/user_documentation.pdf
# tar xzf kind2-v1.6.0-linux-x86_64.tar.gz
# mv kind2 /usr/local/bin/

# FRET
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

# Lando
ARG TOOL=lando
ARG TAG=428ea1174de2bed7c069a6ef8edb30ca75ed441a
ARG REPO=https://github.com/GaloisInc/BESSPIN-Lando.git
RUN git clone ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}
RUN apt-get install -y maven
RUN ./lando.sh -r
# We do not use Lobot.
# RUN cd /tools/${TOOL}/source/lobot/ && cabal v2-build
ENV PATH="/tools/${TOOL}:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# RDE Refinement Finder (aka the DocumentationEnricher)
ARG TOOL=der
ARG TAG=0.1.5
ARG REPO=https://github.com/GaloisInc/RDE_RF
WORKDIR /tmp
RUN wget ${REPO}/releases/download/v.${TAG}/${TOOL}-${TAG}.zip
RUN unzip ${TOOL}-${TAG}.zip
RUN mv ${TOOL}-${TAG} /tools/${TOOL} && rm ${TOOL}-${TAG}.zip
ENV PATH="/tools/${TOOL}:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Cryptol-Verilog
ARG TOOL=cryptol-verilog
COPY ${TOOL} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
# Build fix for LTS GHC.
RUN echo "constraints:" > cabal.project.local
RUN echo "  parameterized-utils < 2.1.6" >> cabal.project.local
RUN \
    cabal v2-build \
    && cabal v2-install --installdir=/tools

# Cryptol-C (crymp)
ARG TOOL=cryptol-codegen
COPY ${TOOL} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
# Build fix for LTS GHC.
RUN echo "constraints:" > cabal.project.local
RUN echo "  parameterized-utils < 2.1.6" >> cabal.project.local
RUN \
    cabal build \
    && cabal install --installdir=/tools

ENV PATH="/tools/:${PATH}"

# Runner
FROM base as runner
COPY --from=builder /opt/ /opt/
COPY --from=builder /tools/ /tools/
COPY --from=builder /root/.local/ /root/.local/
COPY --from=builder /root/.ghcup/ /root/.ghcup/
COPY --from=builder /usr/local/bin/ /usr/local/bin/
COPY --from=builder /usr/local/lib/python2.7/dist-packages/ /usr/local/lib/python2.7/dist-packages/
COPY --from=builder /usr/local/share/ /usr/local/share/
RUN cat ${VERSION_LOG}
WORKDIR /HARDENS

ENV PATH="/tools/der/bin:/tools/lando:/tools:/tools/saw/bin:/tools/bsc-2023.01-ubuntu-22.04/bin:/opt/riscv/bin:/opt/bin:/root/.ghcup/bin:${PATH}"
