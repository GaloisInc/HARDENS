# HARDENS

Repository for the HARDENS project for the [Nuclear Regulatory Commission](https://www.nrc.gov/about-nrc.html).

## Submodules

Initialize with:

```
$ git submodule init
$ git submodule update --recursive
```

## Docker
Build and run with:

```
$ docker build -t hardens:latest .
$ docker run --network host --privileged -v $PWD:/HARDENS -it hardens:latest
```

## Lattice ECP5 evaluation board

Details [here](https://www.latticesemi.com/products/developmentboardsandkits/ecp5evaluationboard#_C694C444BC684AD48A3ED64C227B6455). The board uses ECP5-5G FPGA ([LFE5UM5G-85F-8BG381](https://www.latticesemi.com/en/Products/FPGAandCPLD/ECP5)) which has:

- 84k LUTs
- On-board Boot Flash – 128 Mbit Serial Peripheral Interface (SPI) Flash, with Quad read featu
- 8 input DIP switches, 3 push buttons and 8 LEDs for demo purposes

![ECP_board](assets/ecp5_top.png)

### GPIO headers

Headers are: J5, J8, J32, J33 and Max I_OUT for 3V3 is 1.35A

J5 Pinout:

* 1, 2 - VCCIO2 (Sensor 1 VIN, Sensor 2 VIN)
* 3, 4 - H20, G19 (Sensor 1 I2C)
* 5, 6 - GND (Sensor 1 GND, Sensor 2 GND)
* 7, 8 - K18, J18 (Sensor 2 I2C)

### LEDs:

![ECP_LED](assets/ecp5_leds.png)

### Switches

![ECP_DIP](assets/ecp5_dip.png)

### Buttons

General purpose button `SW4` is connected to `P4`

## Sensors/Actuators

* MOSFET power control kit: https://www.sparkfun.com/products/12959
* 12 V Latch solenoid: https://www.sparkfun.com/products/15324
* Pressure sensor: https://www.sparkfun.com/products/11084

## Bluespec cheatsheet


```
# Elaborate modules
$ bsc -sim -g mkTestbench Testbench.bsv
```


```
# Create simulation binary
$ bsc -sim -e mkTestbench -o ./mkTestbench_bsim
```

```
# Generate verilog
$ bsc -verilog -g mkTestbench Testbench.bsv
```