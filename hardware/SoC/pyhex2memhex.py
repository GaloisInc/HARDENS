#!/usr/bin/python3
import argparse

def int2hex(val: int) -> str:
    """
    Convert a decimal number to a hexadecimal one
    in the proper memhex32 format
    """
    hexval = hex(val)[2:]
    desired_len = 8
    retval = ''
    rem = desired_len - len(hexval) 
    while rem > 0:
        retval += '0'
        rem -= 1
    retval += hexval
    return retval

def str2int(val: str) -> int:
    """
    Convert the input string in hexadecimal or decimal
    representation into an integer
    """
    if val[:2] == '0x':
        # hexadecimal number
        return int(val[2:],16)
    else:
        # decimal number
        return int(val)

def mem2memhex(args):
    in_file = args.input
    out_file = args.output
    with open(in_file,'r') as fin:
        with open(out_file, 'w') as fout:
            fout.write('@0\n')
            counter = 0
            for line in fin.readlines():
                line = line.replace('\n','    ')
                fout.write(f"{line}// {int2hex(counter)}\n")
                counter += 4
            fout.write(f"@{int2hex(str2int(args.maxlen))}\n")
            fout.write("0\n")

def main():
    parser = argparse.ArgumentParser(description='Convert hex files to memhex32 format')
    parser.add_argument('--input', help='Input file', required=True)
    parser.add_argument('--output', help='Output file', required=True)
    parser.add_argument('--maxlen', help='Size of the memory region (in hex)', default='3FF')

    args = parser.parse_args()
    mem2memhex(args)

if __name__ == '__main__':
    main()
