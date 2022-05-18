#!/usr/bin/env python3

# Top level driver for end-to-end testing

import subprocess
import glob
import os

# Turn off screen clearing ANSI
os.environ["RTS_NOCLEAR"] = "1"

# These tests should be run with the self-test binary,
# otherwise use the non self-test binary
NEEDS_SELF_TEST=[
    "scenarios/self_test",
    "scenarios/normal_14",
    "scenarios/exceptional_4a",
    "scenarios/exceptional_4b",
    "scenarios/exceptional_4c",
    "scenarios/exceptional_4d",
    "scenarios/exceptional_4e",
    ]

for test in glob.glob("scenarios/*"):
    fn, ext = os.path.splitext(test)
    if ext == ".cases":
        continue
    bin = "../src/rts.no_self_test"
    if fn in NEEDS_SELF_TEST:
        bin = "../src/rts.self_test"
    os.environ["RTS_BIN"] = bin

    print(f"{fn} ({bin})")

    if os.path.exists(fn + ".cases"):
        subprocess.run(["./test.py", fn, fn + ".cases"])
    else:
        subprocess.run(["./test.py", fn])
