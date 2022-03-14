#!/usr/bin/env python3
"""
This script converts the output of `:dumptests` on the cryptol term
RTS::SelfTestOracleHalf. The output will be included in core.c to form
the built-in self-test data.
"""

import sys
import csv

def expand(testcase):
    result = eval(testcase[0])
    values = eval(testcase[1])
    setpoints = eval(testcase[2])
    i1 = eval(testcase[3])
    off = eval(testcase[4])
    i2 = (i1 + (off % 3) + 1) % 4
    for d in [0, 1]:
        for a in [0, 1]:
            yield [values, setpoints, [i1, i2], a, d, min(1, result & (1 << (1 - d)))]

def render(test):
    if isinstance(test, list):
        vals = ", ".join([ render(v) for v in test ])
        return f"{{{vals}}}"
    else:
        return f"{test}"

with open(sys.argv[1]) as csv_file:
    reader = csv.reader(csv_file,delimiter='\t')
    foos = [render(tc) for testcase in reader for tc in expand(testcase)]
    tests = ",\n".join(foos)
    print(f"// Tests generated from {sys.argv[1]}")
    print(tests)
