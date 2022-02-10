#!/usr/bin/env python3

import subprocess
import glob
import sys
import os

for test in glob.glob("scenarios/*"):
    fn, ext = os.path.splitext(test)
    if ext == ".cases":
        continue
    print(f"{fn}:")
    if os.path.exists(fn + ".cases"):
        subprocess.run(["./test.py", fn, fn + ".cases"])
    else:
        subprocess.run(["./test.py", fn])
