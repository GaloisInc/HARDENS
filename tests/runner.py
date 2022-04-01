#!/usr/bin/env python3

# Run a test on a single input

import pexpect
import sys
import os


RTS_BIN = os.environ.get("RTS_BIN")
RTS_DEBUG = os.environ.get("RTS_DEBUG") is not None

def try_expect(p,expected,timeout=1,retries=60):
    expected = expected.strip()
    if RTS_DEBUG:
        print(f"CHECKING: {expected}")
    while retries > 0:
        p.sendline('D')
        try:
            p.expect(expected.strip() + "\r\n", timeout)
        except pexpect.TIMEOUT:
            retries = retries - 1
            if RTS_DEBUG:
                print(f"...{retries} retries remaining",end='\r')
            continue
        if RTS_DEBUG:
            print(f"CHECKING: {expected} succeeded")
        return True
    if RTS_DEBUG:
        print(f"CHECKING: {expected} failed")
    return False

def run_script(p, cmds):
    in_block = False
    block = ''
    for i,c in enumerate(cmds):
        if len(c) == 0:
            continue

        if c.strip() == '???':
            if in_block:
                in_block = False
                if try_expect(p, block):
                    block = ''
                    continue
                else:
                    return False
            else:
                in_block = True
            continue

        if in_block:
            if block != '':
                block += "\\r\\n"
            block += c.strip()

        elif c[0] == '?':
            if try_expect(p,c[1:]):
                continue
            else:
                return False
        else:
            if RTS_DEBUG:
                print(f"SENDING: {c.strip()}")
            p.sendline(c.strip())
            p.sendline('')
    return True

def run(script, args):
    p = pexpect.spawn(RTS_BIN)
    with open(script) as f:
        cmds = f.readlines()
        fst = cmds[0].strip()
        params = {}
        if fst[0] == '{' and fst[-1] == '}':
            pnames = [x.strip() for x in fst[1:-1].split(',')]
            if len(args) != len(pnames):
                return False
            for (var, val) in zip(pnames, args):
                params[var] = val
            cmds = cmds[1:]

        formatted = [cmd.format(**params) for cmd in cmds]

        return run_script(p, formatted)

def main():
    script = sys.argv[1]
    args = sys.argv[2:] if len(sys.argv) > 2 else []

    if RTS_BIN is None:
        print("Error: RTS_BIN should be set to rts binary to test")
        sys.exit(1)

    if run(script, args):
        print("PASS")
        sys.exit(0)
    else:
        print("FAIL")
        sys.exit(1)

if __name__ == "__main__":
    main()
