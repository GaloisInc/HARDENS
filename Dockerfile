FROM ubuntu:21.04

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get upgrade
RUN apt-get install -y wget git vim python pip\
    python3-dev software-properties-common

# Yosys dependencies
RUN apt-get install -y build-essential clang bison flex \
	libreadline-dev gawk tcl-dev libffi-dev git \
	graphviz xdot pkg-config python3 libboost-system-dev \
	libboost-python-dev libboost-filesystem-dev zlib1g-dev
RUN git clone https://github.com/YosysHQ/yosys.git /tools/yosys
WORKDIR /tools/yosys
RUN make -j$(nproc)
RUN make install PREFIX=/opt

# Trellis dependencies
RUN apt-get install -y libboost-all-dev python3 python3-pip \
    cmake openocd
RUN git clone --recursive https://github.com/SymbiFlow/prjtrellis /tools/prjtrellis
WORKDIR /tools/prjtrellis/libtrellis
RUN cmake -DCMAKE_INSTALL_PREFIX=/opt .
RUN make -j$(nproc)
RUN make install

# nextpnr dependencies
# qt5-default
RUN apt-get install -y python3-dev libboost-all-dev \
    libeigen3-dev
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
ENV PATH="/opt/riscv/bin:${PATH}"

# Install qt5
# Qt5-default is no longer in Ubuntu 21.04
# See a workaround at https://stackoverflow.com/a/67415291
RUN apt-get install -y qtbase5-dev qtchooser qt5-qmake qtbase5-dev-tools

# ecpprog
RUN apt-get install -y libftdi-dev
RUN git clone https://github.com/gregdavill/ecpprog /tools/ecpprog
WORKDIR /tools/ecpprog/ecpprog
RUN make -j$(nproc)
RUN make install

# Iverilog
RUN git clone https://github.com/steveicarus/iverilog.git /tools/iverilog
WORKDIR /tools/iverilog
RUN autoconf
RUN ./configure
RUN make -j$(nproc)
RUN make install

ENV PATH="/opt/bin:${PATH}"

# Additional tools
RUN apt-get install -y iproute2 usbutils srecord
ENV TRELLIS="/opt/share/trellis"
WORKDIR /