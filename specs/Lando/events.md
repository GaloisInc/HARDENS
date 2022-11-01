<!--EVENTS-->
## Demonstrator External Input Actions
<!--ITEM-->
### Manually Actuate Device
The user manually actuates a device.
<!--ITEM/-->
<!--ITEM-->
### Select Operating Mode
The user puts an instrumentation division in or takes a division out of 'maintenance' mode.
<!--ITEM/-->
<!--ITEM-->
### Perform Setpoint Adjustment
The user adjusts the setpoint for a particular channel in a particular division in maintenance mode.
<!--ITEM/-->
<!--ITEM-->
### Configure Bypass of an Instrument Channel
The user sets the mode of the channel of an instrumentation division to either bypass or normal mode.
<!--ITEM/-->
<!--ITEM-->
### Configure Active Trip Output State of an Instrument Channel
The user sets the mode of the channel of an instrumentation division to either trip or normal mode.
<!--ITEM/-->
<!-- Events are (seemingly-atomic, from the point of view of an external -->
<!-- observer) interactions/state-transitions of the system.  The full -->
<!-- set of specified events characterizes every potential externally -->
<!-- visible state change that the system can perform. -->
<!-- External input actions are those that are triggered by external input on UI. -->
<!--EVENTS/-->

<!--EVENTS-->
## Demonstrator External Output Actions
<!--ITEM-->
### Display Pressure
The UI displays the current pressure reading for an instrumentation division.
<!--ITEM/-->
<!--ITEM-->
### Display Temperature
The UI displays the current temperature reading for an instrumentation division.
<!--ITEM/-->
<!--ITEM-->
### Display Saturation Margin
The UI displays the current saturation margin reading for an instrumentation division.
<!--ITEM/-->
<!--ITEM-->
### Display Trip Output Signal State
The UI displays the current trip signal output for a particular channel and instrumentation division.
<!--ITEM/-->
<!--ITEM-->
### Display Indication of Channel in Bypass
The UI displays the current bypass mode for a particular channel and instrumentation division.
<!--ITEM/-->
<!-- External output actions are those that are triggered by internal -->
<!-- state change, which is, in turn, sometimes prompted by external input -->
<!-- actions. -->
<!--EVENTS/-->

<!--EVENTS-->
## Demonstrator Internal Actions
<!--ITEM-->
### Trip on High Pressure
An instrumentation division reads a pressure sensor value that exceeds its setpoint and generates a trip output.
<!--ITEM/-->
<!--ITEM-->
### Trip on High Temperature
An instrumentation division reads a temperature sensor value that exceeds its setpoint and generates a trip output.
<!--ITEM/-->
<!--ITEM-->
### Trip on Low Saturation Margin
An instrumentation division reads temperature and pressure values such that the saturation margin is below its setpoint and generates a trip output.
<!--ITEM/-->
<!--ITEM-->
### Vote on Like Trips using Two-out-of-four Coincidence
An actuation unit reads two like trip inputs and generates the corresponding automatic actuation signal.
<!--ITEM/-->
<!--ITEM-->
### Automatically Actuate Device
An actuation unit generates an automatic actuation signal and sends it to the corresponding device.
<!--ITEM/-->
<!--ITEM-->
### Self-test of Safety Signal Path
The RTS simulates inputs to a pair of instrumentation divisions and checks the corresponding actuation signals.
<!--ITEM/-->
<!-- Internal actions are those that are not triggered by external input on UI. -->
<!--EVENTS/-->

