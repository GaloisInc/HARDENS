# ================================================================
# Dependencies on other directories

# Example: NERV_REPO ?= $(HOME)/Git/nerv
NERV_REPO ?= ../../nerv

ifndef NERV_REPO
  $(error ERROR: please define NERV_REPO, i.e., path to clone of https://github.com/YosysHQ/nerv)
else
  $(info  INFO: NERV_REPO is $(NERV_REPO))
endif

# Example: BLUESPEC_HOME ?= $(HOME)/NoBak/bsc-2021.07-ubuntu-20.04
BLUESPEC_HOME ?= /tools/bsc-2021.07-ubuntu-20.04

ifndef BLUESPEC_HOME
  $(error ERROR: please define BLUESPEC_HOME, i.e., path to B-Lang installation bsc/inst)
else
  $(info  INFO: BLUESPEC_HOME is $(BLUESPEC_HOME))
endif

MEMORY_SIZE ?= 0x40000

# ================================================================

TOPFILE   ?= src_BSV/Top.bsv
TOPMODULE ?= mkTop

BSCFLAGS += -keep-fires
BSCFLAGS += -aggressive-conditions
BSCFLAGS += -no-warn-action-shadowing
BSCFLAGS += -show-range-conflict
BSCFLAGS += -opt-undetermined-vals
BSCFLAGS += -unspecified-to 0
BSCFLAGS += -parallel-sim-link 8
# BSCFLAGS += -show-schedule
# BSCFLAGS += -no-inline-rwire

BSC_C_FLAGS += -Xc++  -D_GLIBCXX_USE_CXX11_ABI=0
BSC_C_FLAGS += -Xl -v
BSC_C_FLAGS += -Xc -O3 -Xc++ -O3

# ================================================================
# Search path for .bsv files

BSCPATH = src_BSV

# Path for standard bsc libs
BSCPATH := $(BSCPATH):+

# ================================================================
# Verilog generation (common for all verilog simulator targets)

BSCDIRS_V = -vdir verilog  -bdir build_v  -info-dir build_v
BSCPATH_V = $(BSCPATH)

build_v:
	mkdir -p $@

verilog:
	mkdir -p $@

FIRMWARE_DIR = firmware
imem_contents.memhex32:
	@make -C $(FIRMWARE_DIR) clean
	@make -C $(FIRMWARE_DIR) firmware.elf
	@riscv64-unknown-elf-elf2hex --bit-width 32 --input $(FIRMWARE_DIR)/firmware.elf --output $(FIRMWARE_DIR)/intermediate.hex
#	@riscv64-unknown-elf-objcopy -O ihex $(FIRMWARE_DIR)/firmware.elf $(FIRMWARE_DIR)/intermediate.hex
	@./pyhex2memhex.py --input $(FIRMWARE_DIR)/intermediate.hex --output $(FIRMWARE_DIR)/firmware.memhex32 --maxlen $(MEMORY_SIZE)
	@mv $(FIRMWARE_DIR)/firmware.memhex32 $@
	@mv $(FIRMWARE_DIR)/firmware.asm .
	@rm $(FIRMWARE_DIR)/intermediate.hex

.PHONY: compile_verilog
compile_verilog: build_v verilog imem_contents.memhex32
	@echo INFO: Verilog generation ...
	bsc -u -elab -verilog  $(BSCDIRS_V)  $(BSCFLAGS) -p +:%/Libraries/FPGA/Misc -p $(BSCPATH_V) $(TOPFILE)
	@echo INFO: Finished Verilog generation

# ================================================================
# FOR VERILATOR


EXEFILE_VERILATOR  ?= exe_verilator

.PHONY: all_verilator
all_verilator:  compile_verilog  link_verilator  exe_verilator

# Boilerplate stuff
VERILATOR_RESOURCES = Verilator_Resources

# Directory containing all the RTL (we copy all RTL here, for simplicity,
# giving Verilator a single -I flag for this.
VERILATOR_RTL_DIR = Verilator_RTL

# Directory in which Verilator should do its build
VERILATOR_MAKE_DIR  = Verilator_Make

VERILATOR_FLAGS += -DTOPMODULE=$(TOPMODULE)
VERILATOR_FLAGS += -DTOPMODULE_V=\"$(TOPMODULE).v\"
VERILATOR_FLAGS += -Mdir $(VERILATOR_MAKE_DIR)
VERILATOR_FLAGS += -O3 --x-assign fast --x-initial fast --noassert --stats
VERILATOR_FLAGS += -CFLAGS -O3
VERILATOR_FLAGS += -CFLAGS -DVL_DEBUG
VERILATOR_FLAGS += -LDFLAGS -static

.PHONY: link_verilator
link_verilator: compile_verilog
	@echo INFO: Link for Verilator ...
	@echo "INFO: For convenience (single -I flag to verilator) copy all Verilog files into $(VERILATOR_RTL_DIR)/"
	mkdir -p $(VERILATOR_RTL_DIR)
	cp -p  $(VERILATOR_RESOURCES)/verilator_wrapper.v    $(VERILATOR_RTL_DIR)/
	cp -p  verilog/*.v                                   $(VERILATOR_RTL_DIR)/
	cp -p  $(NERV_REPO)/nerv.sv                          $(VERILATOR_RTL_DIR)/
	cp -p  $(BLUESPEC_HOME)/lib/Verilog/*.v  $(VERILATOR_RTL_DIR)/
	@echo "INFO: Generating sim_main.cpp for TOPMODULE = $(TOPMODULE)"
	sed  's/TOPMODULE/mkTop/g' \
		$(VERILATOR_RESOURCES)/sim_main_template.cpp \
		> $(VERILATOR_RESOURCES)/sim_main.cpp
	@echo "INFO: Verilating Verilog files (in $(VERILATOR_MAKE_DIR))"
	verilator \
		-I$(VERILATOR_RTL_DIR) \
		$(VERILATOR_FLAGS) \
		--cc  --exe --build -j 4 -o $(EXEFILE_VERILATOR)  verilator_wrapper.v \
		--top-module $(TOPMODULE) \
		$(VERILATOR_RESOURCES)/sim_main.cpp
	mv  $(VERILATOR_MAKE_DIR)/$(EXEFILE_VERILATOR)  .
	@echo INFO: Finished Link for Verilator

.PHONY: exe_verilator
exe_verilator: link_verilator
	@echo INFO: Verilator Simulation ...
	./$(EXEFILE_VERILATOR)
	@echo INFO: Finished Verilator Simulation

# ================================================================


.PHONY: clean
clean:
	rm -r -f  *~   */*~  build*  obj_dir \
		$(VERILATOR_RTL_DIR)  $(VERILATOR_MAKE_DIR)  Verilator_Resources/sim_main.cpp imem_contents.memhex32 firmware.asm \
		verilog  exe_*

# ================================================================
