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

def count_ones(x):
    return sum([int(d) for d in bin(x)[2:]])

def vals(x):
    digits = bin(x)[2:]
    pad = 4 - len(digits)
    padded = ('0'*pad) + digits
    return " ".join(["2" if d == '1' else "0" for d in padded])

for t in range(0,16):
    for p in range(0,16):
        for s in range(0,16):
            # d0 = "ON" if (count_ones(t) + count_ones(p)) >= 2 else "OFF"
            # d1 = "ON" if count_ones(s) >= 2 else "OFF"
            # print(f"{vals(t)} {vals(p)} {vals(s)} {d0} {d1}")

            v00 = "1" if (count_ones(t) + count_ones(p)) >= 2 else "0"
            v10 = "1" if (count_ones(t) + count_ones(p)) >= 2 else "0"
            v01 = "1" if count_ones(s) >= 2 else "0"
            v11 = "1" if count_ones(s) >= 2 else "0"
            print(f"{vals(t)} {vals(p)} {vals(s)} {v00} {v01} {v10} {v11}")
