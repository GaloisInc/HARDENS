#!/usr/bin/env python3
import sys
import os
from runner import run

QUICK = os.environ.get("QUICK")

def main():
    script = sys.argv[1]
    cases = [(0,"")]
    if len(sys.argv) > 2:
        cases_filename = sys.argv[2]
        with open(cases_filename) as cases_file:
            cases = cases_file.readlines()
            if QUICK is not None and len(cases) > 4:
                cases = cases[0:3]
            cases = enumerate(cases)
    for (i,case) in cases:
        if run(script, case.strip().split(" ")):
            continue
        else:
            print(f"Test {i+1} failed")
            sys.exit(1)
    print("All inputs passed!")

    sys.exit(0)

if __name__ == "__main__":
    main()
