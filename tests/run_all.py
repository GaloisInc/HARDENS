#!/usr/bin/env python3

# Top level driver for end-to-end testing

import subprocess
import glob
import sys
import os

# Turn off screen clearing ANSI
os.environ["RTS_NOCLEAR"] = "1"

for test in glob.glob("scenarios/*"):
    fn, ext = os.path.splitext(test)
    if ext == ".cases":
        continue
    print(f"{fn}:")
    if os.path.exists(fn + ".cases"):
        subprocess.run(["./test.py", fn, fn + ".cases"])
    else:
        subprocess.run(["./test.py", fn])
