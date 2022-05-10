<!--SUBSYSTEM RTS System Architecture-->
## <a id ="rts-system-architecture"></a>RTS System Architecture (RTS_System_Arch)
@todo kiniry Add an explanation.

<!--SUBSYSTEM RTS System Architecture/-->
<!--SUBSYSTEM Root-->
## <a id ="root"></a>Root
@todo kiniry Add an explanation.

<!--COMPONENT-->
### <a id ="core-finite-state-machine"></a>Core Finite State Machine (CFSM)
inherit FSM @todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="programming-i/o"></a>Programming I/O (Programming_IO)
inherit IO @todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="ui-i/o"></a>UI I/O (UI_IO)
inherit IO @todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="debugging-i/o"></a>Debugging I/O (Debugging_IO)
inherit IO @todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--SUBSYSTEM Root/-->
<!--SUBSYSTEM Actuation Logic-->
## <a id ="actuation-logic"></a>Actuation Logic
@todo kiniry Add an explanation.

<!--COMPONENT-->
### <a id ="voting-1"></a>Voting 1
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="voting-2"></a>Voting 2
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="actuator-1"></a>Actuator 1
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="actuator-2"></a>Actuator 2
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--SUBSYSTEM Actuation Logic/-->
<!--SUBSYSTEM Computation-->
## <a id ="computation"></a>Computation
@todo kiniry Add an explanation.

<!--COMPONENT-->
### <a id ="risc-v-cpu-1"></a>RISC-V CPU 1
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="risc-v-cpu-2"></a>RISC-V CPU 2
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="risc-v-cpu-3"></a>RISC-V CPU 3
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--SUBSYSTEM Computation/-->
<!--SUBSYSTEM Hardware-->
## <a id ="hardware"></a>Hardware
@todo kiniry Add an explanation.

<!--SUBSYSTEM Hardware/-->
<!--SUBSYSTEM FPGA-->
## <a id ="fpga"></a>FPGA
@todo kiniry Add an explanation.

<!--COMPONENT-->
### <a id ="lattice-ecp-5-fgpa-development-board"></a>Lattice ECP-5 FGPA Development Board
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--SUBSYSTEM FPGA/-->
<!--SUBSYSTEM Actuators-->
## <a id ="actuators"></a>Actuators
@todo kiniry Add an explanation.

<!--COMPONENT-->
### <a id ="actuator-1"></a>Actuator 1
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="actuator-2"></a>Actuator 2
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--SUBSYSTEM Actuators/-->
<!--SUBSYSTEM Sensors-->
## <a id ="sensors"></a>Sensors
@todo kiniry Add an explanation.

<!--COMPONENT-->
### <a id ="temperature-sensor-1"></a>Temperature Sensor 1
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="temperature-sensor-2"></a>Temperature Sensor 2
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="pressure-sensor-1"></a>Pressure Sensor 1
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="pressure-sensor-2"></a>Pressure Sensor 2
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--SUBSYSTEM Sensors/-->
<!--SUBSYSTEM Instrumentation-->
## <a id ="instrumentation"></a>Instrumentation
@todo kiniry Add an explanation.

<!--COMPONENT-->
### <a id ="instrumentation-1"></a>Instrumentation 1
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="instrumentation-2"></a>Instrumentation 2
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="instrumentation-3"></a>Instrumentation 3
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="instrumentation-4"></a>Instrumentation 4
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--RELATION-->
#### relation RTS_System_Arch
* contains [Root](#root)
<!--RELATION/-->
<!--RELATION-->
#### relation RTS_System_Arch
* contains [Actuation Logic](#actuation-logic)
<!--RELATION/-->
<!--RELATION-->
#### relation RTS_System_Arch
* contains [Computation](#computation)
<!--RELATION/-->
<!--RELATION-->
#### relation RTS_System_Arch
* contains [Hardware](#hardware)
<!--RELATION/-->
<!--RELATION-->
#### relation RTS_System_Arch
* contains [Instrumentation](#instrumentation)
<!--RELATION/-->
<!--RELATION-->
#### relation Hardware
* contains [FPGA](#fpga)
<!--RELATION/-->
<!--RELATION-->
#### relation Hardware
* contains [Actuators](#actuators)
<!--RELATION/-->
<!--RELATION-->
#### relation Hardware
* contains [Sensors](#sensors)
<!--RELATION/-->
<!--RELATION-->
#### relation Root
* client of [Actuation Logic](#actuation-logic)
<!--RELATION/-->
<!--RELATION-->
#### relation Root
* client of [Computation](#computation)
<!--RELATION/-->
<!--RELATION-->
#### relation Computation
* client of [Hardware](#hardware)
<!--RELATION/-->
<!--RELATION-->
#### relation Actuation Logic
* client of [Hardware](#hardware)
<!--RELATION/-->
<!--RELATION-->
#### relation Instrumentation
* client of [Hardware](#hardware)
<!--RELATION/-->
<!--RELATION-->
#### relation Instrumentation
* client of [Actuation Logic](#actuation-logic)
<!--RELATION/-->
<!--RELATION-->
#### relation Actuation Logic
* client of [Instrumentation](#instrumentation)
<!--RELATION/-->
<!--SUBSYSTEM Instrumentation/-->
