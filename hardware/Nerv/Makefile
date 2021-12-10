default: compile  link
all:	 compile  link  simulate

# ----------------------------------------------------------------

TOPFILE   ?= src_BSV/Top.bsv
#TOPFILE   ?= src_BSV/Top2.bsv

TOPMODULE ?= mkTop
EXEFILE_BSIM ?= exe_HW_bsim
EXEFILE_VSIM ?= exe_HW_vsim

BSCFLAGS = -keep-fires \
	-aggressive-conditions \
	-no-warn-action-shadowing \
	-show-range-conflict \
        -opt-undetermined-vals \
	-unspecified-to X \


#	-show-schedule \
#	-no-inline-rwire \

BSC_C_FLAGS += \
	-Xc++  -D_GLIBCXX_USE_CXX11_ABI=0 \
	-Xl -v \
	-Xc -O3 -Xc++ -O3

# ----------------------------------------------------------------
# For RISCY-OOO

BSCPATH = src_BSV:+

# ----------------------------------------------------------------
# FOR BLUESIM

BSCDIRS_BSIM  = -simdir build_bsim -bdir build -info-dir build
BSCPATH_BSIM  = $(BSCPATH)

build_bsim:
	mkdir -p $@

build:
	mkdir -p $@

.PHONY: compile
compile: build_bsim build
	@echo Compiling...
	bsc -u -sim $(BSCDIRS_BSIM)  $(BSCFLAGS)  -p $(BSCPATH_BSIM)  $(TOPFILE)
	@echo Compilation finished

.PHONY: link
link: compile
	@echo Linking...
	bsc  -sim  -parallel-sim-link 8\
		$(BSCDIRS_BSIM)  -p $(BSCPATH_BSIM) \
		-e $(TOPMODULE) -o ./$(EXEFILE_BSIM) \
		-keep-fires \
		$(BSC_C_FLAGS)
	@echo Linking finished

.PHONY: simulate
simulate: link
	@echo Simulation...
	./$(EXEFILE_BSIM)
	@echo Simulation finished

# ----------------------------------------------------------------
# FOR VERILOG

BSCDIRS_V = -vdir verilog  -bdir build_v  -info-dir build_v
BSCPATH_V = src_BSV:+

VSIM ?= iverilog

build_v:
	mkdir -p $@

verilog:
	mkdir -p $@

.PHONY: rtl
rtl: build_v verilog firmware.hex
	@echo Verilog generation ...
	bsc -u -elab -verilog  $(BSCDIRS_V)  $(BSCFLAGS)  -p $(BSCPATH_V)  $(TOPFILE)
	@echo Verilog generation finished

.PHONY: vlink
vlink: rtl
	bsc -verilog  -vsim $(VSIM)  $(BSCDIRS_V) \
		-e $(TOPMODULE) -o ./$(EXEFILE_VSIM) \
		-keep-fires lib/nerv.v
	@echo Verilog linking finished

testbench: rtl
	iverilog -o testbench -I verilog ../../nerv/nerv.sv -I lib

#  -Wno-UNOPTFLAT
#  -Wno-STMTDLY

VERILATOR_FLAGS = --prof-cfuncs -Wno-lint  -CFLAGS -DVL_DEBUG -O3 --report-unoptflat --x-assign fast --x-initial fast --noassert --stats --build -j
veribench: rtl firmware.hex
	verilator --cc -o veribench $(VERILATOR_FLAGS) -I./lib -I./verilog verilog/mkNervSoC.v
	cp firmware.hex obj_dir/.
	verilator --cc -o veribench $(VERILATOR_FLAGS) --exe -I./lib -I./verilog verilog/mkNervSoC.v main.cpp

test:
	vvp -N testbench +vcd

.PHONY: vsim
vsim: vlink
	@echo Simulation...
	./$(EXEFILE_VSIM)
	@echo Simulation finished

# ----------------------------------------------------------------
# FIRMWARE BUILD
TOOLCHAIN_PREFIX?=riscv64-unknown-elf-
firmware.elf: firmware.s firmware.c
	$(TOOLCHAIN_PREFIX)gcc -march=rv32i -mabi=ilp32 -Os -Wall -Wextra -Wl,-Bstatic,-T,sections.lds,--strip-debug -ffreestanding -nostdlib -o $@ $^

firmware.hex: firmware.elf
	$(TOOLCHAIN_PREFIX)objcopy -O verilog $< $@
	cp $@ tmp.hex
	cat $@ | sed -r 's,(..) (..) (..) (..),\4\3\2\1,g' > tmp
	cp tmp verilog/$@
	cp tmp $@
	rm tmp

# ----------------------------------------------------------------

.PHONY: clean
clean:
	rm -f  *~   src_BSV/*~  build/*  build_bsim/*

.PHONY: full_clean
full_clean: clean
	rm -r -f  exe_*  build*  verilog  exe_HW_* firmware.hex firmware.elf obj_dir

# ----------------------------------------------------------------
