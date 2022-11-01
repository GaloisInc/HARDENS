import serial
import time
#Serial takes two parameters: serial device and baudrate
with serial.Serial('/dev/ttyUSB0', 76800, serial.EIGHTBITS, serial.PARITY_NONE, serial.STOPBITS_ONE) as s:
    while(1):
        s.write(bytearray([0xAA]))
        print(s.readline().decode())

print("Done")

