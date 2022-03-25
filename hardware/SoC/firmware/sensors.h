#ifndef SENSORS_H_
#define SENSORS_H_

// Defines for sensor simulation
// 7bit sensor address
#define TEMP_0_I2C_ADDR 0x48
#define TEMP_1_I2C_ADDR 0x4A
#define PRESSURE_0_I2C_ADDR 0x60
// TODO: @podhrmic the pressure sensor has a fixed address
// find a solution for having two pressure sensors
#define PRESSURE_1_I2C_ADDR 0x62

#endif