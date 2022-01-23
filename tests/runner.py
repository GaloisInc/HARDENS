#!/usr/bin/env python3
import pexpect
import sys

def try_expect(p,expected,timeout=1,retries=3):
    expected = expected.strip()
    while retries > 0:
        p.sendline('D')
        try:
            p.expect(expected.strip() + "\r\n", timeout)
        except pexpect.TIMEOUT:
            retries = retries - 1
            continue
        return True
    return False

def run_script(p, cmds):
    for c in cmds:
        if c[0] == '?':
            if try_expect(p,c[1:]):
                continue
            else:
                return False
        else:
            p.sendline(c.strip())
            p.sendline('')
    return True

def main():
    script = sys.argv[1]
    p = pexpect.spawn("../src/rts")
    with open(script) as f:
        cmds = f.readlines()
        fst = cmds[0].strip()
        params = {}
        if fst[0] == '{' and fst[-1] == '}':
            pnames = [x.strip() for x in fst[1:-1].split(',')]
            if len(sys.argv) - 2 < len(pnames):
                print(f"Test expects parameters: {pnames}")
                sys.exit(1)
            for (var, val) in zip(pnames, sys.argv[2:]):
                params[var] = val



        formatted = [cmd.format(**params) for cmd in cmds[1:]]

        if run_script(p, formatted):
            print("PASS")
        else:
            print("FAIL")

if __name__ == "__main__":
    main()
