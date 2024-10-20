<!--SCENARIOS-->
## Self-Test Scenarios
<!--ITEM-->
### Normal Self-Test Behavior 1a - Trip on Mock High Pressure Reading from that Pressure Sensor
The user selects 'maintenance' for an instrumentation division, the division's pressure channel is set to 'normal' mode, the pressure setpoint is set to a value v, the user simulates a pressure input to that division exceeding v, the division generates a pressure trip.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 1b - Trip on Environmental High Pressure Reading from that Pressure Sensor
The user selects 'maintenance' for an instrumentation division, the division's pressure channel is set to 'normal' mode, the pressure setpoint is set to a value v, the division reads a pressure sensor value division exceeding v, the division generates a pressure trip.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 2a - Trip on Mock High Temperature Reading from that Temperature Sensor
The user selects 'maintenance' for an instrumentation division, the division's temperature channel is set to 'normal' mode, the temperature setpoint is set to a value v, the user simulates a temperature input to that division exceeding v, the division generates a temperature trip.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 2a - Trip on Environmental High Temperature Reading from that Temperature Sensor
The user selects 'maintenance' for an instrumentation division, the division's temperature channel is set to 'normal' mode, the temperature setpoint is set to a value v, the division reads a temperature sensor value division exceeding v, the division generates a temperature trip.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 3a - Trip on Mock Low Saturation Margin
The user selects 'maintenance' for an instrumentation division, the division's saturation channel is set to 'normal' mode, the saturation margin setpoint is set to a value v, the user simulates pressure and temperature inputs to that division such that the saturation margin is below v, the division generates a saturation margin trip.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 3a - Trip on Environmental Low Saturation Margin
The user selects 'maintenance' for an instrumentation division, the division's saturation channel is set to 'normal' mode, the saturation margin setpoint is set to a value v, the division reads pressure and temperature sensor values in that division such that the saturation margin is below v, the division generates a saturation margin trip.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 4 - Vote on Every Possible Like Trip
The user selects 'maintenance' for each instrumentation division, the user configures a subset of channels to place in active trip output.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 5a - Automatically Actuate All Mock Devices in Sequence
The user selects 'maintenance' for each instrumentation division, the user places enough channels in 'active trip' to actuate a mock device.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 5b - Automatically Actuate All Hardware Devices in Sequence
The user selects 'maintenance' for each instrumentation division, the user places enough channels in 'active trip' to actuate a hardware device.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 6 - Manually Actuate Each Device in Sequence
The user manually actuates each device.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 7a - Select Maintenance Operating Mode for each Division
The user selects 'maintenance' mode for each instrumentation division in sequence.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 7b - Select Normal Operating Mode for each Division
The user exits 'maintenance' mode for each instrumentation division in sequence.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 8 - Perform Each Kind of Setpoint Adjustment
For each instrumentation division, the user provides a setpoint for temperature, then the user provides a setpoint for pressure, then the user provides a setpoint for saturation margin.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 9 - Configure Bypass of Each Instrument Channel in Sequence
For each instrumentation division, the user puts each channel in 'normal' and then 'bypass' mode.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 10 - Configure Active Trip Output State of Each Instrument Channel in Sequence
For each instrumentation division, the user puts each channel in 'trip' and then 'normal' mode.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 11 - Display Pressure Temperature and Saturation Margin
The user provides inputs for an instrumentation division, then the UI displays the updated pressure, temperature and saturation margin.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 12 - Display Every Trip Output Signal State in Sequence
The user configures an instrumentation division in 'maintenance', selects a channel and places it in 'trip', the UI displays the trip state, the user places the channel in 'normal' mode, the UI displays the trip state.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 13 - Display Indication of Every Channel in Bypass in Sequence
The user configures an instrumentation division in 'maintenance', the user selects a channel and places it in bypass, the UI displays the bypass state, the user places the channel in normal mode, the UI displays the updated state.
<!--ITEM/-->
<!--ITEM-->
### Normal Self-Test Behavior 14 - Demonstrate Periodic Continual Self-test of Safety Signal Path
The system starts, eventually the UI displays that self test has run.
<!--ITEM/-->
<!--ITEM-->
### Normal Behavior Full Self-Test
The system selects two instrumentation divisions and a device, the system simulates inputs to the selected instrumentation divisions, the system checks that the correct actuation signal would be sent to the selected device.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 1a - Cause Actuator 1 to Fail
Manually actuate Actuator 1, the actuator fails, an error is indicated.
<!-- Exceptional behaviors are *predictable* system behaviors triggered -->
<!-- by external environment affects.  Examples include a CPU, OS, -->
<!-- device, or network total or partial failure.  E.g., CPU deadlock, -->
<!-- out-of-memory errors, permanent store partial and total failures, -->
<!-- lack of space in permanent store, partial and total network -->
<!-- failures, device driver partial or total failures, etc. -->
<!-- In our architecture, every part of the RTS system, and particularly -->
<!-- every part of the instrumentation and sensing subsystem and every -->
<!-- part of the actuation subsystem must be able to fail and the system -->
<!-- must respond appropriately. -->
<!-- This is not detectable -->
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 1b - Cause Actuator 2 to Fail
Manually actuate Actuator 2, the actuator fails, an error is indicated.
<!-- This is not detectable -->
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 1c - Non-determinisitically Cause an Actuator to Eventually Fail
Repeatedly manually actuate/unactuate an Actuator, the actuator fails, an error is indicated.
<!-- This is not detectable -->
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 2a - Cause Temperature Sensor 1 to Fail
Instrumentation units 1 and 2 reports temperature readings that are inconsistent with Instrumentation units 3 and 4, the discrepancy is indicated on the UI.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 2b - Cause Temperature Sensor 2 to Fail
Instrumentation units 1 and 2 reports temperature readings that are inconsistent with Instrumentation units 3 and 4, the discrepancy is indicated on the UI.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 2c - Non-deterministically Cause a Temperature Sensor to Eventually Fail
Instrumentation units 1 and 2 reports temperature readings that are inconsistent with Instrumentation units 3 and 4, the discrepancy is indicated on the UI.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 3a - Cause Pressure Sensor 1 to Fail
Instrumentation units 1 and 2 reports pressure readings that are inconsistent with Instrumentation units 3 and 4, the discrepancy is indicated on the UI.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 3b - Cause Pressure Sensor 2 to Fail
Instrumentation units 1 and 2 reports pressure readings that are inconsistent with Instrumentation units 3 and 4, the discrepancy is indicated on the UI.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 3c - Non-deterministically Cause a Pressure Sensor to Eventually Fail
Temperature Sensor 1 or Temperature Sensor 2 report inconsistent values, discrepancy is indicated on the UI.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 4a - Cause Instrumentation Unit 1 to Fail
Instrumentation unit 1 fails, self test indicates that a test has failed.
<!-- Can be further refined, e.g.: -->
<!-- Sensor values are read by Instrumnetation Unit 1, the unit generates the wrong trip signal, -->
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 4b - Cause Instrumentation Unit 2 to Fail
Instrumentation unit 2 fails, self test indicates that a test has failed.
<!-- Can be further refined, e.g.: -->
<!-- Sensor values are read by Instrumnetation Unit 1, the unit generates the wrong trip signal, -->
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 4c - Cause Instrumentation Unit 3 to Fail
Instrumentation unit 3 fails, self test indicates that a test has failed.
<!-- Can be further refined, e.g.: -->
<!-- Sensor values are read by Instrumnetation Unit 1, the unit generates the wrong trip signal, -->
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 4d - Cause Instrumentation Unit 4 to Fail
Instrumentation unit 4 fails, self test indicates that a test has failed.
<!-- Can be further refined, e.g.: -->
<!-- Sensor values are read by Instrumnetation Unit 1, the unit generates the wrong trip signal, -->
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 4e - Non-Deterministically Cause Instrumentation Unit to Eventually Fail
At least one instrumentation unit fails to generate the appropriate trip signal, self test runs, self test indicates that a test has failed.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 5a - Cause Temperature Demultiplexor 1 to Fail
At least one of Instrumentation units 1 or 2 report temperature readings inconsistent with instrumentation units 3 and 4.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 5b - Cause Temperature Demultiplexor 2 to Fail
At least one of Instrumentation units 3 or 4 report temperature readings inconsistent with instrumentation units 1 and 2.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 5c - Cause Pressure Demultiplexor 1 to Fail
At least one of Instrumentation units 1 and 2 report pressure readings inconsistent with instrumentation units 3 and 4.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 5d - Cause Pressure Demultiplexor 2 to Fail
At least one of Instrumentation units 3 and 4 report pressure readings inconsistent with instrumentation units 1 and 2.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 5e - Cause a Temperature Demultiplexor to Eventually Fail
All instrumentation units report consistent temperature readings, a demultiplexor fails, at least one of the instrumentation units reports an inconsistent temperature reading.
<!--ITEM/-->
<!--ITEM-->
### Exceptional Behavior 5f - Cause a Pressure Demultiplexor to Eventually Fail
All instrumentation units report consistent temperature readings, a demultiplexor fails, at least one of the instrumentation units reports an inconsistent pressure reading.
<!--ITEM/-->
<!-- Scenarios are sequences of events.  Scenarios document normal and -->
<!-- abnormal traces of system execution. -->
<!-- Test scenarios are scenarios that validate a system conforms to its -->
<!-- requirements through runtime verification (testing).  Each scenario -->
<!-- is refined to a (possibly parametrized) runtime verification -->
<!-- property.  If a testbench is complete, then every path of a -->
<!-- system's state machine should be covered by the its set of scenarios. -->
<!--SCENARIOS/-->

