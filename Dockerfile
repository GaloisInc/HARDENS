FROM ubuntu:21.04

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get upgrade
RUN apt-get install -y wget git vim python pip\
    python3-dev software-properties-common \
    iproute2 usbutils srecord

# Yosys
RUN apt-get install -y build-essential clang bison flex \
	libreadline-dev gawk tcl-dev libffi-dev git \
	graphviz xdot pkg-config python3 libboost-system-dev \
	libboost-python-dev libboost-filesystem-dev zlib1g-dev
RUN git clone https://github.com/YosysHQ/yosys.git /tools/yosys
WORKDIR /tools/yosys
RUN make -j$(nproc)
RUN make install PREFIX=/opt

# Trellis
RUN apt-get install -y libboost-all-dev python3 python3-pip \
    cmake openocd
RUN git clone --recursive https://github.com/SymbiFlow/prjtrellis /tools/prjtrellis
WORKDIR /tools/prjtrellis/libtrellis
RUN cmake -DCMAKE_INSTALL_PREFIX=/opt .
RUN make -j$(nproc)
RUN make install
ENV TRELLIS="/opt/share/trellis"

# nextpnr
RUN apt-get install -y python3-dev libboost-all-dev \
    libeigen3-dev qtbase5-dev qtchooser qt5-qmake qtbase5-dev-tools
RUN git clone https://github.com/YosysHQ/nextpnr.git /tools/nextpnr
WORKDIR /tools/nextpnr
RUN cmake . -DARCH=ecp5 -DTRELLIS_INSTALL_PREFIX=/opt
RUN make -j$(nproc)
RUN make install

# RISCV toolchain
RUN apt-get install -y autoconf automake autotools-dev curl libmpc-dev \
    libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf \
    libtool patchutils bc zlib1g-dev libexpat-dev
RUN git clone --recursive https://github.com/riscv/riscv-gnu-toolchain /tools/riscv-gnu-toolchain
WORKDIR /tools/riscv-gnu-toolchain
RUN  ./configure --prefix=/opt/riscv --enable-multilib
RUN export MAKEFLAGS="-j$(nproc)"
RUN make
RUN make linux
ENV PATH="/opt/riscv/bin:/opt/bin:${PATH}"

# ecpprog
RUN apt-get install -y libftdi-dev
RUN git clone https://github.com/gregdavill/ecpprog /tools/ecpprog
WORKDIR /tools/ecpprog/ecpprog
RUN make -j$(nproc)
RUN make install

# Iverilog
RUN apt-get install -y iverilog

# Bluespec compiler
RUN apt-get install -y libffi7
WORKDIR /tmp
RUN wget https://github.com/B-Lang-org/bsc/releases/download/2021.07/bsc-2021.07-ubuntu-20.04.tar.gz
RUN tar xvzf bsc-2021.07-ubuntu-20.04.tar.gz
RUN mv bsc-2021.07-ubuntu-20.04 /tools/bsc-2021.07-ubuntu-20.04
ENV PATH="/tools/bsc-2021.07-ubuntu-20.04/bin:${PATH}"

# Verilator
RUN apt-get install -y verilator

WORKDIR /