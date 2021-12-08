Version: 2021-12-07::19:55

Playing with "nerv" ("Naive Educational RISC-V Processor") at

    https://github.com/YosysHQ/nerv

cf.
    https://github.com/YosysHQ/nerv/blob/main/nerv.sv
    https://github.com/YosysHQ/nerv/blob/main/nervsoc.sv

Source files are in src_BSV/

- Nerv_BVI.bsv is the "raw" import of nerv.sv, giving us a BSV module
    constrctor mkNerv_BVI.

- Nerv.bsv is a thin wrapper that instantiates Nerv.BVI, and collects
    the raw wstrb and wdata into a struct returned by a combined
    method get_dmem(), and also incorporates dmem_valid as an implicit
    method condition.

- NervSoC.bsv is patterned after the original nervsoc.sv,
    instantiating Nerv.bsv

- Top.bsv is testbench that instantiates NervSoC and just prints the
    LED values output from NervSoc.

If you 'make rtl' at the top-level, it should generate RTL in a
'verilog/' directory (should look like verilog_sample/).
