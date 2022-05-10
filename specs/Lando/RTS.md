<!--SYSTEM Reactor Trip System-->
# <a id ="reactor-trip-system"></a>Reactor Trip System (RTS)
The overall shape of the Reactor Trip System (RTS) is an archetypal *sense-compute-actuate* architecture. Sensors are in the `Sensors` subsystem. They are read by the `Instrumentation` subsystem, which contains four separate and independent `Instrumentation` components. The "Compute" part of the architecture is spread across the `Actuation Logic` subsystem—which contains the two `Voting` components which perform the actuation logic itself—and the `Root` subsystem which contains the core computation and I/O components, and the two separate and independent devices that drive actuators.

<!--SUBSYSTEM RTS Architecture-->
## <a id ="rts-architecture"></a>RTS Architecture (Architecture)
This RTS architecture specification includes all of the core concepts inherent to NPP Instrumentation and Control systems. A system architecture specification often includes a software, hardware, network, and data architecture specifications.

<!--SUBSYSTEM RTS Architecture/--><!--SUBSYSTEM RTS Hardware Artifacts-->
## <a id ="rts-hardware-artifacts"></a>RTS Hardware Artifacts (Hardware)
The physical hardware components that are a part of the HARDENS RTS demonstrator.

<!--SUBSYSTEM RTS Hardware Artifacts/--><!--SUBSYSTEM RTS Implementation Artifacts-->
## <a id ="rts-implementation-artifacts"></a>RTS Implementation Artifacts (Implementation)
A summary of the tools, technologies, specifications, and implementations relevant to this high-assurance demonstrator's development and assurance.

<!--SUBSYSTEM RTS Implementation Artifacts/--><!--SUBSYSTEM RTS Requirements-->
## <a id ="rts-requirements"></a>RTS Requirements (Requirements)
All requirements that the RTS system must fulfill, as driven by the IEEE 603-2018 standards and the NRC RFP.

<!--SUBSYSTEM RTS Requirements/--><!--SUBSYSTEM RTS Properties-->
## <a id ="rts-properties"></a>RTS Properties (Properties)
All correctness and security properties of the RTS system are specified in this subsystem.

<!--SUBSYSTEM RTS Properties/--><!--SUBSYSTEM IEEE Std 603-2018 Characteristics-->
## <a id ="ieee-std-603-2018-characteristics"></a>IEEE Std 603-2018 Characteristics (Characteristics)
The IEEE 603-2018 requirements (known as "characteristics" in the standard) which the RTS demonstrator system must fulfill.

<!--SUBSYSTEM IEEE Std 603-2018 Characteristics/--><!-- title: Reactor Trip System high-assurance demonstrator. -->
<!-- project: High Assurance Rigorous Digital Engineering for Nuclear Safety (HARDENS) -->
<!-- copyright (C) 2021 Galois -->
<!-- author: Joe Kiniry <kiniry@galois.com> -->
<!--SYSTEM Reactor Trip System/-->
