#!/usr/bin/env python3

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

# Runs all of the testcases for a given test script:
# ./test.py scenario
# or
# ./test.py scenario scenario.cases

import sys
import os
from runner import run

# Some tests are quite long. For sanity checking we can just
# run the first few test cases.
QUICK = os.environ.get("QUICK")

def main():
    script = sys.argv[1]
    cases = [(0,"")]
    if len(sys.argv) > 2:
        cases_filename = sys.argv[2]
        with open(cases_filename) as cases_file:
            print(f"Opening {cases_filename}...")
            cases = cases_file.readlines()
            if QUICK is not None and len(cases) > 4:
                cases = cases[0:3]
            cases = enumerate(cases)
    for (i,case) in cases:
        print(f"Running case {i}")
        if run(script, case.strip().split(" ")):
            continue
        else:
            print(f"Test {i+1} failed")
            sys.exit(1)
    print("All inputs passed!")

    sys.exit(0)

if __name__ == "__main__":
    main()
