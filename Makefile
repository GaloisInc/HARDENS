######################################
#
# RTS Makefile
#
######################################

######################################
# General Config
######################################
# Which platform: Posix or RV32_bare_metal
PLATFORM ?= Posix

######################################
# Config for Posix only:
######################################
# Parallel: pthread-based implementation to simulate the concurrency SoC
# Sequential:  a single-threaded implementation
EXECUTION ?= Parallel
# Should hardware be simulated? 
# Use Verilator to simulate hardware implemented modules
HW ?= Simulated
# Should sensors be simulated?
SENSORS ?= NotSimulated

######################################
# Config for RV32_bare_metal only
######################################
# Virtual or LFE5UM5G_85F_EVN
DEV_BOARD ?= Virtual

######################################
#
# Posix definitions
#
######################################
$(info Choosing plaform $(PLATFORM))
ifeq ($(PLATFORM),Posix)

.PHONY: rts test clean

rts:
	mkdir -p src/generated/SystemVerilog
	mkdir -p src/generated/C
	make -C src clean
	SENSORS=$(SENSORS) SELF_TEST=Enabled make -C src rts
	mv src/rts src/rts.self_test
	make -C src clean
	SENSORS=$(SENSORS) SELF_TEST=Disabled make -C src rts
	mv src/rts src/rts.no_self_test

test: rts
	(cd tests && make test)

clean:
	make -C src clean

else # Not PLATFORM=Posix
######################################
#
# RV32_bare_metal definitions
#
######################################
ifeq ($(PLATFORM),RV32_bare_metal)

.PHONY: fw_only fw_clean clean

fw_only:
	PROG=main make -C hardware/SoC/firmware

fw_clean:
	PROG=main make -C hardware/SoC/firmware clean

clean:
	PROG=main make -C hardware/SoC/ clean

$(info Choosing dev board $(DEV_BOARD))
ifeq ($(DEV_BOARD),Virtual)

.PHONY: rts

rts:
	PROG=main make -C hardware/SoC/ verilator

else # DEV_BOARD = LFE5UM5G_85F_EVN ?
ifeq ($(DEV_BOARD),LFE5UM5G_85F_EVN)
# Core freq with 12MHz clock in
# Since we have 5 CPU states, it should be 12MHZ/5 = 2400000
CORE_FREQ=2400000

.PHONY: rts

rts:
	CORE_FREQ=$(CORE_FREQ) PROG=main make -C hardware/SoC/ prog

else
$(info Unsupported dev board!)
endif

endif # DEV_BOARD = Virtual ?

else # Not PLATFORM=RV32_bare_metal
$(info Unsupported platform!)
endif # PLATFORM=RV32_bare_metal ?
endif # PLATFORM=Posix ?

.PHONY: check

check:
	make -C models
	make -C saw
