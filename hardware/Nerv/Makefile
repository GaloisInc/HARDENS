default: compile  link
all:	 compile  link  simulate

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

.PHONY: compile_Verilog
compile_Verilog: build_v verilog
	@echo INFO: Verilog generation ...
	bsc -u -elab -verilog  $(BSCDIRS_V)  $(BSCFLAGS)  -p $(BSCPATH_V)  $(TOPFILE)
	@echo INFO: Finished Verilog generation

# ================================================================
# FOR VERILATOR


EXEFILE_VERILATOR  ?= exe_Verilator

.PHONY: all_Verilator
all_Verilator:  compile_Verilog  link_Verilator  exe_Verilator

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

.PHONY: link_Verilator
link_Verilator:
	@echo INFO: Link for Verilator ...
	@echo "INFO: For convenience (single -I flag to verilator) copy all Verilog files into $(VERILATOR_RTL_DIR)/"
	mkdir -p $(VERILATOR_RTL_DIR)
	cp -p  $(VERILATOR_RESOURCES)/verilator_wrapper.v    $(VERILATOR_RTL_DIR)/
	cp -p  verilog/*.v                                   $(VERILATOR_RTL_DIR)/
	cp -p  $(NERV_REPO)/nerv.sv                          $(VERILATOR_RTL_DIR)/
	cp -p  $(BLUESPEC_HOME)/lib/Verilog/RegFile.v        $(VERILATOR_RTL_DIR)/
	cp -p  $(BLUESPEC_HOME)/lib/Verilog/RegFileLoad.v    $(VERILATOR_RTL_DIR)/
	cp -p  $(BLUESPEC_HOME)/lib/Verilog/ResetInverter.v  $(VERILATOR_RTL_DIR)/
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

.PHONY: exe_Verilator
exe_Verilator:
	@echo INFO: Verilator Simulation ...
	./$(EXEFILE_VERILATOR)
	@echo INFO: Finished Verilator Simulation

# ================================================================

.PHONY: clean
clean:
	rm -r -f  *~   */*~  build*  obj_dir \
		$(VERILATOR_RTL_DIR)  $(VERILATOR_MAKE_DIR)  Verilator_Resources/sim_main.cpp

.PHONY: full_clean
full_clean: clean
	rm -r -f  verilog  exe_*

# ================================================================
