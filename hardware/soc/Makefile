#  NERV -- Naive Educational RISC-V Processor
#
#  Copyright (C) 2020  N. Engelhardt <nak@yosyshq.com>
#  Copyright (C) 2020  Claire Xenia Wolf <claire@yosyshq.com>
#
#  Permission to use, copy, modify, and/or distribute this software for any
#  purpose with or without fee is hereby granted, provided that the above
#  copyright notice and this permission notice appear in all copies.
#
#  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
#  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
#  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
#  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
#  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
#  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
#  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

TRELLIS?=/usr/share/trellis
TOOLCHAIN_PREFIX?=riscv64-unknown-elf-
NERV_SRC?=../../nerv

test: firmware.hex testbench
	vvp -N testbench +vcd

firmware.elf: firmware.s firmware.c
	$(TOOLCHAIN_PREFIX)gcc -march=rv32i -mabi=ilp32 -Os -Wall -Wextra -Wl,-Bstatic,-T,sections.lds,--strip-debug -ffreestanding -nostdlib -o $@ $^

firmware.hex: firmware.elf
	$(TOOLCHAIN_PREFIX)objcopy -O verilog $< $@
	cat $@ | sed -r 's,(..) (..) (..) (..),\4\3\2\1,g' > tmp
	mv tmp $@

veribench: firmware.hex
	verilator --cc -o veribench -Wno-lint -Wno-STMTDLY -O0 -x-assign 0 --build -j top.v $(NERV_SRC)/nerv.sv $(NERV_SRC)/nervsoc.sv
	cp firmware.hex obj_dir/.
	verilator --cc -o veribench -Wno-lint -Wno-STMTDLY --exe -O0 -x-assign 0 --build -j top.v $(NERV_SRC)/nerv.sv $(NERV_SRC)/nervsoc.sv main.cpp

testbench: testbench.sv $(NERV_SRC)/nerv.sv $(NERV_SRC)/nervsoc.sv top.v firmware.hex
	iverilog -o testbench -D STALL -D NERV_DBGREGS testbench.sv $(NERV_SRC)/nerv.sv $(NERV_SRC)/nervsoc.sv top.v

design.json: $(NERV_SRC)/nerv.sv $(NERV_SRC)/nervsoc.sv top.v firmware.hex
	yosys -l design_ys.log -p 'synth_ecp5 -top top -json $@' $(NERV_SRC)/nerv.sv $(NERV_SRC)/nervsoc.sv top.v

design.config: design.json ecp5.lpf
	nextpnr-ecp5 --json $< --textcfg $@ --um5g-85k --package CABGA381 --lpf ecp5.lpf

design.bit: design.config
	ecppack --svf design.svf $< $@

design.svf : design.bit

prog: design.svf
	openocd -f ${TRELLIS}/misc/openocd/ecp5-evn.cfg -c "transport select jtag; init; svf $<; exit"

show:
	gtkwave testbench.vcd testbench.gtkw >> gtkwave.log 2>&1 &

clean:
	rm -rf firmware.elf firmware.hex testbench testbench.vcd gtkwave.log
	rm -rf design.json design.bit design.config design_ys.log design.svf
