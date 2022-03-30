# ================================================================
# Dependencies on other directories

# Example: NERV_REPO ?= $(HOME)/Git/nerv
NERV_REPO ?= ../nerv

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

IMEMORY_SIZE ?= 0x07000
DMEMORY_SIZE ?= 0x03000


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
BUILD_V_DIR = build_v
VERILOG_DIR = verilog
BSCDIRS_V = -vdir $(VERILOG_DIR)  -bdir $(BUILD_V_DIR)  -info-dir $(BUILD_V_DIR)
BSCPATH_V = $(BSCPATH)

FIRMWARE_DIR = firmware
PROG 	?= main

# TODO: properly storing sdata in FLASH could help keep the dmem smaller
dmem_contents.memhex32:
	PROG=$(PROG) make -C $(FIRMWARE_DIR) clean
	PROG=$(PROG) make -C $(FIRMWARE_DIR) firmware.elf
	@riscv64-unknown-elf-elf2hex --bit-width 32 --input $(FIRMWARE_DIR)/firmware.elf --output $(FIRMWARE_DIR)/intermediate.hex
	@./pyhex2memhex.py --input $(FIRMWARE_DIR)/intermediate.hex --output $(FIRMWARE_DIR)/firmware.memhex32 --maxlen $(DMEMORY_SIZE)
	@mv $(FIRMWARE_DIR)/firmware.memhex32 $@
	@cp $(FIRMWARE_DIR)/firmware.asm .
	@rm $(FIRMWARE_DIR)/intermediate.hex

imem_contents.memhex32: dmem_contents.memhex32
	@riscv64-unknown-elf-elf2hex --bit-width 32 --input $(FIRMWARE_DIR)/text.elf --output $(FIRMWARE_DIR)/intermediate.hex
	@./pyhex2memhex.py --input $(FIRMWARE_DIR)/intermediate.hex --output $(FIRMWARE_DIR)/text.memhex32 --maxlen $(IMEMORY_SIZE)
	@mv $(FIRMWARE_DIR)/text.memhex32 $@
	@cp $(FIRMWARE_DIR)/text.asm .
	@rm $(FIRMWARE_DIR)/intermediate.hex

verilog: dmem_contents.memhex32 imem_contents.memhex32
	mkdir -p $(BUILD_V_DIR)
	mkdir -p $(VERILOG_DIR)
	@echo INFO: Verilog generation ...
	bsc -u -elab -verilog  $(BSCDIRS_V)  $(BSCFLAGS) -p +:%/Libraries/FPGA/Misc -p $(BSCPATH_V) $(TOPFILE)
	@echo INFO: Finished Verilog generation

# ================================================================
# FOR VERILATOR

EXEFILE_VERILATOR  ?= exe_verilator

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

verilator: verilog
	@echo "INFO: Link for Verilator ..."
	@echo "INFO: For convenience (single -I flag to verilator) copy all Verilog files into $(VERILATOR_RTL_DIR)/"
	mkdir -p $(VERILATOR_RTL_DIR)
	cp -p  $(VERILATOR_RESOURCES)/verilator_wrapper.v    $(VERILATOR_RTL_DIR)/
	cp -p  $(VERILATOR_RESOURCES)/*.c    $(VERILATOR_RTL_DIR)/
	cp -p  $(VERILATOR_RESOURCES)/*.h    $(VERILATOR_RTL_DIR)/
	cp -p  $(VERILOG_DIR)/*.v                                   $(VERILATOR_RTL_DIR)/
	cp -p  $(NERV_REPO)/nerv.sv                          $(VERILATOR_RTL_DIR)/
	cp -p  $(BLUESPEC_HOME)/lib/Verilog/*.v  $(VERILATOR_RTL_DIR)/
	@echo "Copying over handwritten modules"
	cp -p ../../src/handwritten/SystemVerilog/instrumentation_impl.sv $(VERILATOR_RTL_DIR)/Is_Ch_Tripped.sv
	sed 's/Is_Ch_Tripped/Is_Ch_Tripped_Handwritten/' $(VERILATOR_RTL_DIR)/Is_Ch_Tripped.sv > $(VERILATOR_RTL_DIR)/out.sv
	mv $(VERILATOR_RTL_DIR)/out.sv $(VERILATOR_RTL_DIR)/Is_Ch_Tripped_Handwritten.sv
	sed 's/Generate_Sensor_Trips/Generate_Sensor_Trips_Handwritten/' $(VERILATOR_RTL_DIR)/Is_Ch_Tripped_Handwritten.sv > $(VERILATOR_RTL_DIR)/out.sv
	mv $(VERILATOR_RTL_DIR)/out.sv $(VERILATOR_RTL_DIR)/Is_Ch_Tripped_Handwritten.sv
	@echo "Copying over generated modules"
	cp -p ../../src/generated/SystemVerilog/instrumentation_impl.sv $(VERILATOR_RTL_DIR)/Is_Ch_Tripped.sv
	sed 's/Is_Ch_Tripped/Is_Ch_Tripped_Generated/' $(VERILATOR_RTL_DIR)/Is_Ch_Tripped.sv > $(VERILATOR_RTL_DIR)/out.sv
	mv $(VERILATOR_RTL_DIR)/out.sv $(VERILATOR_RTL_DIR)/Is_Ch_Tripped_Generated.sv
	sed 's/Generate_Sensor_Trips/Generate_Sensor_Trips_Generated/' $(VERILATOR_RTL_DIR)/Is_Ch_Tripped_Generated.sv > $(VERILATOR_RTL_DIR)/out.sv
	mv $(VERILATOR_RTL_DIR)/out.sv $(VERILATOR_RTL_DIR)/Is_Ch_Tripped_Generated.sv
	cp -p ../../src/generated/SystemVerilog/actuation_unit_impl.sv $(VERILATOR_RTL_DIR)/Actuate_D0.sv
	@echo "INFO: Generating sim_main.cpp for TOPMODULE = $(TOPMODULE)"
	sed  's/TOPMODULE/mkTop/g' \
		$(VERILATOR_RESOURCES)/sim_main_template.cpp \
		> $(VERILATOR_RESOURCES)/sim_main.cpp
	@echo "INFO: Generating C interfaces"
	sed  -f $(VERILATOR_RESOURCES)/sed_script.txt  $(VERILATOR_RTL_DIR)/$(TOPMODULE).v > tmp1.v
	cat $(VERILATOR_RESOURCES)/import_DPI_C_decls.v tmp1.v > $(VERILATOR_RTL_DIR)/$(TOPMODULE).v
	rm   -f  tmp1.v
	@echo "INFO: Verilating Verilog files (in $(VERILATOR_MAKE_DIR))"
	verilator \
		-I$(VERILATOR_RTL_DIR) \
		$(VERILATOR_FLAGS) \
		--cc  --exe --build -j 4 -o $(EXEFILE_VERILATOR)  verilator_wrapper.v \
		--top-module $(TOPMODULE) \
		$(VERILATOR_RESOURCES)/sim_main.cpp \
		$(VERILATOR_RESOURCES)/C_Imported_Functions.c
	mv  $(VERILATOR_MAKE_DIR)/$(EXEFILE_VERILATOR)  .
	@echo INFO: Finished Link for Verilator

exe: verilator
	@echo INFO: Verilator Simulation ...
	./$(EXEFILE_VERILATOR)
	@echo INFO: Finished Verilator Simulation

# ================================================================
# TODO @podhrmic Define CORE_FREQ and TICKS_TO_MS_MULTIPLIER for the FPGA

SYNTH_DIR = test
design.json: verilator
	mkdir -p $(SYNTH_DIR)
	cp $(NERV_REPO)/nerv.sv $(SYNTH_DIR)/.
	cp $(BLUESPEC_HOME)/lib/Verilog/ResetInverter.v $(SYNTH_DIR)/.
	cp $(BLUESPEC_HOME)/lib/Verilog/SizedFIFO.v $(SYNTH_DIR)/.
	cp $(BLUESPEC_HOME)/lib/Verilog/Counter.v $(SYNTH_DIR)/.
	cp $(VERILOG_DIR)/*.v $(SYNTH_DIR)/
	cp $(VERILATOR_RTL_DIR)/Actuate_D0.sv $(SYNTH_DIR)/.
	cp $(VERILATOR_RTL_DIR)/Is_Ch_Tripped_Handwritten.sv $(SYNTH_DIR)/.
	cp $(VERILATOR_RTL_DIR)/Is_Ch_Tripped_Generated.sv $(SYNTH_DIR)/.
# Trick to be able to load two different binaries
	sed 's/RegFileLoad #(.file('\"'i/RegFileLoadI #(.file('\"'i/' $(SYNTH_DIR)/mkNervSoC.v > out.v
	sed 's/RegFileLoad #(.file('\"'d/RegFileLoadD #(.file('\"'d/' out.v > $(SYNTH_DIR)/mkNervSoC.v
# Dmem
	sed 's/'\"\"'/'\"imem_contents.memhex32\"'/' $(BLUESPEC_HOME)/lib/Verilog/RegFileLoad.v > $(SYNTH_DIR)/RegFileLoadI.v
	sed 's/module RegFileLoad/module RegFileLoadI/' $(SYNTH_DIR)/RegFileLoadI.v > out.v
	mv out.v $(SYNTH_DIR)/RegFileLoadI.v
# Imem
	sed 's/'\"\"'/'\"dmem_contents.memhex32\"'/' $(BLUESPEC_HOME)/lib/Verilog/RegFileLoad.v > $(SYNTH_DIR)/RegFileLoadD.v
	sed 's/module RegFileLoad/module RegFileLoadD/' $(SYNTH_DIR)/RegFileLoadD.v > out.v
	mv out.v $(SYNTH_DIR)/RegFileLoadD.v
# Run the actual synthesis
	yosys -l design_ys.log -s yosys.txt

#	yosys -l design_ys.log -p "read_verilog verilog/*.v $(VERILATOR_RTL_DIR)/nerv.sv $(VERILATOR_RTL_DIR)/ResetInverter.v $(VERILATOR_RTL_DIR)/SizedFIFO.v $(VERILATOR_RTL_DIR)/RegFileLoad.v $(VERILATOR_RTL_DIR)/Counter.v; proc; synth_ecp5 -json $@ -top mkTop"
#	yosys -l design_ys.log -p "synth_ecp5 -json $@" $(VERILATOR_RTL_DIR)/SizedFIFO.v $(VERILATOR_RTL_DIR)/nerv.sv verilog/*.v $(VERILATOR_RTL_DIR)/ResetInverter.v $(VERILATOR_RTL_DIR)/RegFileLoad.v
#	yosys -l design_ys.log -p "synth_ecp5 -json $@" $(BLUESPEC_HOME)/lib/Verilog/SizedFIFO.v $(NERV_REPO)/nerv.sv verilog/*.v $(BLUESPEC_HOME)/lib/Verilog/ResetInverter.v $(BLUESPEC_HOME)/lib/Verilog/RegFileLoad.v
#yosys -l design_ys.log -p "read_verilog $(BLUESPEC_HOME)/lib/Verilog/SizedFIFO.v; proc; read_verilog $(NERV_REPO)/nerv.sv verilog/*.v $(BLUESPEC_HOME)/lib/Verilog/ResetInverter.v $(BLUESPEC_HOME)/lib/Verilog/RegFileLoad.v; synth_ecp5 -json $@"

design.config: design.json
	nextpnr-ecp5 --json $< --textcfg $@ --um5g-85k --package CABGA381 --lpf ecp5.lpf --lpf-allow-unconstrained
# TODO: constrain pins

design.bit: design.config
	ecppack --svf design.svf $< $@

clean:
	rm -r -f  *~   */*~  build*  obj_dir \
		$(VERILATOR_RTL_DIR)  $(VERILATOR_MAKE_DIR)  Verilator_Resources/sim_main.cpp *.memhex32 *.asm \
		$(VERILOG_DIR)  exe_* *.o *.sft ./*.so \
		design* $(SYNTH_DIR)

# ================================================================
