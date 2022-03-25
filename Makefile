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
SENSORS ?=

######################################
# Config for RV32_bare_metal only
######################################
# Virtual or LFE5UM5G_85F_EVN
DEV_BOARD ?= LFE5UM5G_85F_EVN

######################################
#
# Posix definitions
#
######################################
$(info Choosing plaform $(PLATFORM))
ifeq ($(PLATFORM),Posix)

rts:
	make -C src rts

clean:
	make -C src clean

else # Not PLATFORM=posix
######################################
#
# RV32_bare_metal definitions
#
######################################
ifeq ($(PLATFORM),RV32_bare_metal)
fw_only:
	PROG=main make -C hardware/SoC/firmware

fw_clean:
	PROG=main make -C hardware/SoC/firmware clean

clean:
	PROG=main make -C hardware/SoC/ clean

$(info Choosing dev board $(DEV_BOARD))
ifeq ($(DEV_BOARD),Virtual)

rts:
	PROG=main make -C hardware/SoC/ verilator

else # DEV_BOARD = LFE5UM5G_85F_EVN ?
ifeq ($(DEV_BOARD),LFE5UM5G_85F_EVN)

rts:
	PROG=main make -C hardware/SoC/ design.config

else
$(info Unsupported dev board!)
endif

endif # DEV_BOARD = Virtual ?

else # Not PLATFORM=RV32_bare_metal
$(info Unsupported platform!)
endif # PLATFORM=RV32_bare_metal ?
endif # PLATFORM=posix ?

.PHONY: rts all clean docs_clean

docs:   README.pdf Assurance.pdf Toolchain.pdf

%.pdf: %.md
	pandoc -f markdown -t latex -o `basename $< .md`.pdf $<

docs_clean:
	rm -f README.pdf Assurance.pdf Toolchain.pdf

check:
	make -C models

