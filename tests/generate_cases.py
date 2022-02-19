#!/usr/bin/env python3

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
