######################################
#
# RTS Makefile
#
######################################

#   Copyright 2021, 2022, 2023 Galois, Inc.
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.

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

rts:
	mkdir -p src/generated/SystemVerilog
	mkdir -p src/generated/C
	make -C src clean
	SENSORS=$(SENSORS) SELF_TEST=Enabled make -C src rts
	mv src/rts src/rts.self_test
	make -C src clean
	SENSORS=$(SENSORS) SELF_TEST=Disabled make -C src rts
	mv src/rts src/rts.no_self_test

src_clean:
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

src_clean:
	PROG=main make -C hardware/SoC/ clean

$(info Choosing dev board $(DEV_BOARD))
ifeq ($(DEV_BOARD),Virtual)

rts:
	PROG=main make -C hardware/SoC/ verilator

else # DEV_BOARD = LFE5UM5G_85F_EVN ?
ifeq ($(DEV_BOARD),LFE5UM5G_85F_EVN)
# Core freq with 12MHz clock in
# Since we have 5 CPU states, it should be 12MHZ/5 = 2400000
CORE_FREQ=2400000

rts:
	CORE_FREQ=$(CORE_FREQ) PROG=main make -C hardware/SoC/ prog

else
$(info Unsupported dev board!)
endif

endif # DEV_BOARD = Virtual ?

else # Not PLATFORM=RV32_bare_metal
$(info Unsupported platform!)
endif # PLATFORM=RV32_bare_metal ?
endif # PLATFORM=posix ?

#
# Documentation
#

docs: README.pdf

README.pdf: README.md
	pandoc -o README.pdf README.md

Assurance.pdf: Assurance.md
	pandoc -o Assurance.pdf Assurance.md

Toolchain.pdf: Toolchain.md
	pandoc -o Toolchain.pdf Toolchain.md

clean: src_clean doc_clean

doc_clean:
	rm -f README.pdf Assurance.pdf Toolchain.md

.PHONY: rts all clean src_clean fw_clean doc_clean docs

check:
	make -C models
	make -C saw

