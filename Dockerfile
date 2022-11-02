# Base
FROM ubuntu:22.04 as base
ARG DEBIAN_FRONTEND=noninteractive
RUN mkdir /tools
WORKDIR /

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y wget git python3 pip \
    python3-dev software-properties-common \
    iproute2 usbutils srecord \
    build-essential clang bison flex \
    libreadline-dev gawk tcl-dev libffi-dev git \
    graphviz xdot pkg-config python3 libboost-system-dev \
    libboost-python-dev libboost-filesystem-dev zlib1g-dev \
    libboost-all-dev python3-pip \
    cmake openocd \
    libeigen3-dev qtbase5-dev qtchooser qt5-qmake qtbase5-dev-tools \
    autoconf automake autotools-dev curl libmpc-dev \
    libmpfr-dev libgmp-dev texinfo gperf \
    libtool patchutils bc zlib1g-dev libexpat-dev \
    libftdi-dev unzip \
    cabal-install libffi7 \
    libftdi1-2 libftdi1-dev libhidapi-libusb0 libhidapi-dev libudev-dev make g++ \
    libc++-dev libc++abi-dev nodejs python2 npm \
    iverilog verilator \
    vim mercurial libboost-program-options-dev \
    texlive-full

# To run test suite
RUN pip install pexpect

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

# nextpnr
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

########################################
# Riscv-formal
#######################################
ARG TOOL=SymbiYosys
ARG TAG=419ef76f82b3973e356815f63fc919218b2860bb
ARG REPO=https://github.com/YosysHQ/SymbiYosys.git
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN make install
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

ARG TOOL=yices2
ARG TAG=Yices-2.6.4
ARG REPO=https://github.com/SRI-CSL/yices2.git
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN autoconf
RUN ./configure
RUN make -j$(nproc)
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
RUN cp deps/btor2tools/bin/btorsim /usr/local/bin/
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
ARG TOOL=lando
ARG TAG=428ea1174de2bed7c069a6ef8edb30ca75ed441a
ARG REPO=https://github.com/GaloisInc/BESSPIN-Lando.git
RUN git clone ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}
RUN apt-get install -y maven
RUN ./lando.sh -r
RUN cd /tools/${TOOL}/source/lobot/ && cabal v2-build
ENV PATH="/tools/${TOOL}:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# DocumentationEnricher
ARG TOOL=der
ARG TAG=0.1.4
ARG REPO=https://github.com/SimplisticCode/DER/releases/download/v1.1.4/
WORKDIR /tmp
RUN wget ${REPO}/${TOOL}-${TAG}.zip
RUN unzip ${TOOL}-${TAG}.zip
RUN    mv ${TOOL}-${TAG} /tools/${TOOL}
ENV PATH="/tools/${TOOL}/bin:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Runner
FROM base as runner
COPY --from=builder /opt/ /opt/
COPY --from=builder /tools/ /tools/
COPY --from=builder /root/.cabal/ /root/.cabal/
COPY --from=builder /usr/local/bin/ /usr/local/bin/
COPY --from=builder /usr/local/lib/python2.7/dist-packages/ /usr/local/lib/python2.7/dist-packages/
COPY --from=builder /usr/local/share/ /usr/local/share/
RUN cat ${VERSION_LOG}
WORKDIR /HARDENS

# Install java so we can run lando
RUN apt-get install -y default-jre

ENV PATH="/tools/der/bin:/tools/lando:/tools:/tools/z3/bin:/tools/bsc-2021.07-ubuntu-20.04/bin:/opt/riscv/bin:/opt/bin:${PATH}"
