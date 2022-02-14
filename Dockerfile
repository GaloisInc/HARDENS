FROM ubuntu:21.04

ARG DEBIAN_FRONTEND=noninteractive
RUN mkdir /tools
ARG VERSION_LOG=/tools/log.txt
RUN echo "Installed tools:" >> ${VERSION_LOG}

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y wget git vim python pip\
    python3-dev software-properties-common \
    iproute2 usbutils srecord

# Yosys
ARG TOOL=yosys
ARG TAG=yosys-0.13
ARG REPO=https://github.com/YosysHQ/yosys.git
RUN apt-get install -y build-essential clang bison flex \
	libreadline-dev gawk tcl-dev libffi-dev git \
	graphviz xdot pkg-config python3 libboost-system-dev \
	libboost-python-dev libboost-filesystem-dev zlib1g-dev
RUN git clone ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}
RUN git checkout ${TAG}
RUN make -j$(nproc)
RUN make install PREFIX=/opt
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Trellis
ARG TOOL=prjtrellis
ARG TAG=1.1
ARG REPO=https://github.com/YosysHQ/prjtrellis.git
RUN apt-get install -y libboost-all-dev python3 python3-pip \
    cmake openocd
RUN git clone --recursive ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}/libtrellis
RUN git checkout ${TAG}
RUN cmake -DCMAKE_INSTALL_PREFIX=/opt .
RUN make -j$(nproc)
RUN make install
ENV TRELLIS="/opt/share/trellis"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# nextpnr
ARG TOOL=nextpnr
ARG TAG=nextpnr-0.1
ARG REPO=https://github.com/YosysHQ/nextpnr.git
RUN apt-get install -y python3-dev libboost-all-dev \
    libeigen3-dev qtbase5-dev qtchooser qt5-qmake qtbase5-dev-tools
RUN git clone ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}
RUN git checkout ${TAG}
RUN cmake . -DARCH=ecp5 -DTRELLIS_INSTALL_PREFIX=/opt
RUN make -j$(nproc)
RUN make install
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# RISCV toolchain
ARG TOOL=riscv-gnu-toolchain
ARG TAG=2022.01.17
ARG REPO=https://github.com/riscv/riscv-gnu-toolchain
RUN apt-get install -y autoconf automake autotools-dev curl libmpc-dev \
    libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf \
    libtool patchutils bc zlib1g-dev libexpat-dev
RUN git clone --recursive ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}
RUN git checkout ${TAG}
RUN  ./configure --prefix=/opt/riscv --enable-multilib
RUN export MAKEFLAGS="-j$(nproc)"
RUN make
RUN make linux
ENV PATH="/opt/riscv/bin:/opt/bin:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# ecpprog
ARG TOOL=ecpprog
ARG TAG=7212b56a9d2fc6de534e06636a1c6d8b0c6f80ab
ARG REPO=https://github.com/gregdavill/ecpprog
RUN apt-get install -y libftdi-dev
RUN git clone ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}/ecpprog
RUN git checkout ${TAG}
RUN make -j$(nproc)
RUN make install
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Iverilog
RUN apt-get install -y iverilog
RUN echo "`iverilog -v | head -1`" >> ${VERSION_LOG}

# Bluespec compiler
ARG TOOL=bluespec-compiler
ARG TAG=bsc-2021.07-ubuntu-20.04
ARG REPO=https://github.com/B-Lang-org/bsc/releases/download/2021.07/${TAG}.tar.gz
RUN apt-get install -y libffi7
WORKDIR /tmp
RUN wget https://github.com/B-Lang-org/bsc/releases/download/2021.07/${TAG}.tar.gz
RUN tar xvzf ${TAG}.tar.gz
RUN mv ${TAG} /tools/${TAG}
ENV PATH="/tools/${TAG}/bin:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Verilator
RUN apt-get install -y verilator
RUN echo "`verilator --version`" >> ${VERSION_LOG}

# OpenFPGAloader
ARG TOOL=openFPGALoader
ARG TAG=v0.7.0
ARG REPO=https://github.com/trabucayre/openFPGALoader.git
RUN apt-get install -y libftdi1-2 libftdi1-dev libhidapi-libusb0 libhidapi-dev libudev-dev cmake pkg-config make g++
RUN git clone ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}
RUN git checkout ${TAG}
RUN mkdir build
WORKDIR /tools/${TOOL}/build
RUN cmake ../
RUN cmake --build .
RUN make install
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
RUN git clone ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}
RUN git checkout ${TAG}
RUN autoreconf -i
RUN ./configure --target=riscv64-unknown-elf
RUN make
RUN make install
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Bluespec libraries
ARG TOOL=bsc-contrib
ARG TAG=aa205330885f6955e24fd99a0319e2733b5353f1
ARG REPO=https://github.com/B-Lang-org/bsc-contrib.git
RUN git clone ${REPO} /tools/${TOOL}
WORKDIR /tools/${TOOL}
RUN git checkout ${TAG}
RUN make PREFIX=/tools/bsc-2021.07-ubuntu-20.04/
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# GHC and Cabal
RUN apt-get update -y
RUN apt-get install -y cabal-install
RUN cabal update

# cryptol 2.11
ARG TOOL=cryptol
ARG TAG=dfae4580e322584185235f301bc8a03b6bc19a65
ARG REPO=https://github.com/GaloisInc/cryptol.git
RUN git clone ${REPO} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN git checkout ${TAG} \
    && git submodule update --init
RUN ./cry build
RUN cabal v2-install --installdir=/tools/${TOOL}/bin
RUN rm -rf /tmp/${TOOL}
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# cryptol-verilog
ARG TOOL=cryptol-verilog
ARG TAG=${CRYPTOL_VERILOG_REV}
ADD ${TOOL} /tmp/${TOOL}
WORKDIR /tmp/${TOOL}
RUN cabal v2-build
RUN cabal v2-install --installdir=/tools/${TOOL}/bin
RUN rm -rf /tmp/${TOOL}
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

# Crymp
ARG TOOL=cryptol-codegen
ARG TAG=${CRYPTOL_CODEGEN_REV}
ADD ${TOOL} /tools/${TOOL}
WORKDIR /tools/${TOOL}
RUN cabal build
ENV PATH="/tools/${TOOL}:${PATH}"
RUN echo "${TOOL} ${REPO} ${TAG}" >> ${VERSION_LOG}

RUN cat ${VERSION_LOG}

WORKDIR /
