<!--SUBSYSTEM RTS Instrumentation Architecture-->
## <a id ="rts-instrumentation-architecture"></a>RTS Instrumentation Architecture
The architecture for the instrumentation (sensors and actuators) subsystem of the RTS demonstrator.

<!--SUBSYSTEM RTS Instrumentation Architecture/-->
<!--SUBSYSTEM RTS Instrumentation Systems Architecture-->
## <a id ="rts-instrumentation-systems-architecture"></a>RTS Instrumentation Systems Architecture
The systems architecture for the instrumentation subsystem of the RTS demonstrator. Some of the architecture is implemented in hardware, and some is implementated in software.

<!--COMPONENT-->
### <a id ="instrumentation-implementation"></a>Instrumentation Implementation (InstImpl)
A software or hardware driver that interfaces with a sensor. In the RTS demonstrator there are two kinds of sensors: pressure and temperature.
  * inherits [Driver](#driver)<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="actuator-implementation"></a>Actuator Implementation (ActImpl)
inherit Driver A software or hardware driver that interfaces with an actuator. In the RTS demonstrator there is one kind of actuator: a solenoid.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="voting-implementation"></a>Voting Implementation (VoteImpl)
inherit Voting A software or hardware implemenation of our voting algorithm that provides fault tolerance for decision-making based upon the attached components' inputs.
<!--COMPONENT/-->
<!--SUBSYSTEM RTS Instrumentation Systems Architecture/-->
<!--SUBSYSTEM Instrumentation Software Stack-->
## <a id ="instrumentation-software-stack"></a>Instrumentation Software Stack (SWStack)
inherit Software The software stack associated with the instrumentation subsystem.

<!--COMPONENT-->
### <a id ="instrumentation-implementation-1"></a>Instrumentation Implementation 1 (InstImpl1)
The first of four sensor drivers for the instrumentation subsystem.
  * inherits [Instrumentation Implementation](#instrumentation-implementation)<!--COMPONENT/-->
<!--RELATION-->
#### relation InstImpl1
* inherits [SWImpl](#swimpl)
<!--RELATION/-->
<!--RELATION-->
#### relation InstImpl1
* inherits [High-Assurance](#high-assurance)
<!--RELATION/-->
<!--RELATION-->
#### relation InstImpl1
* inherits [C](#c)
<!--RELATION/-->
<!--COMPONENT-->
### <a id ="instrumentation-implementation-2"></a>Instrumentation Implementation 2 (InstImpl2)
inherit InstImpl The second of four sensor drivers for the instrumentation subsystem. There are multiple sensors in the architecture to provide fault tolerance.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="actuator-implementation-1"></a>Actuator Implementation 1 (ActImpl1)
inherit ActImpl The first of two actuator drivers for the instrumentation subsystem. There are multiple actuators in the architecture to provide fault tolerance.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="voting-implementation-1"></a>Voting Implementation 1 (VoteImpl1)
inherit VoteImpl The first of two implementations of the voting component. Voting is used to implement redundancy of instrumentation and control in the RTS demonstrator.
<!--COMPONENT/-->
<!--RELATION-->
#### relation SWStack
* client of [Binaries](#binaries)
<!--RELATION/-->
<!--RELATION-->
#### relation Binaries
* client of [SWStack](#swstack)
<!--RELATION/-->
<!--SUBSYSTEM Instrumentation Software Stack/-->
<!--SUBSYSTEM Instrumentation Actuation and Voting Hardware Stack-->
## <a id ="instrumentation-actuation-and-voting-hardware-stack"></a>Instrumentation Actuation and Voting Hardware Stack (HWStack)
The hardware implementations driving a redundant subset of sensors, actuators, and voting components.

<!--COMPONENT-->
### <a id ="instrumentation-implementation-3"></a>Instrumentation Implementation 3 (InstImpl3)
inherit InstImpl The third of four sensor drivers for the instrumentation subsystem. There are multiple sensors in the architecture to provide fault tolerance.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="instrumentation-implementation-4"></a>Instrumentation Implementation 4 (InstImpl4)
inherit InstImpl The fourth of four sensor drivers for the instrumentation subsystem. There are multiple sensors in the architecture to provide fault tolerance.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="actuator-implementation-2"></a>Actuator Implementation 2 (ActImpl2)
inherit ActImpl The second of two actuator drivers for the instrumentation subsystem. There are multiple actuators in the architecture to provide fault tolerance.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="voting-implementation-2"></a>Voting Implementation 2 (VoteImpl2)
inherit VoteImpl The second of two implementations of the voting component. Voting is used to implement redundancy of instrumentation and control in the RTS demonstrator.
<!--COMPONENT/-->
<!--RELATION-->
#### relation HWStack
* client of [Bitstream](#bitstream)
<!--RELATION/-->
<!--RELATION-->
#### relation Bitstream
* client of [HWStack](#hwstack)
<!--RELATION/-->
<!--SUBSYSTEM Instrumentation Actuation and Voting Hardware Stack/-->
