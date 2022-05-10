<!--REQUIREMENTS-->
## HARDENS Project High-level Requirements
<!--ITEM-->
### NRC Understanding
Provide to the NRC expert technical services in order to develop a better understanding of how Model-Based Systems Engineering (MBSE) methods and tools can support regulatory reviews of adequate design and design assurance.
<!-- The high-level requirements for the project stipulated by the NRC RFP. -->
<!--ITEM/-->
<!--ITEM-->
### Identify Regulatory Gaps
Identify any barriers or gaps associated with MBSE in a regulatory review of Digital Instrumentation and Control Systems for existing Nuclear Power Plants.
<!--ITEM/-->
<!--ITEM-->
### Demonstrate
Galois will demonstrate to the Nuclear Regulatory Commission (NRC) cutting-edge capabilities in the model-based design, validation, and verification of safety-critical, mission-critical, high-assurance systems.
<!--ITEM/-->
<!--ITEM-->
### Demonstrator Parts
Our demonstrator includes high-assurance software and hardware, includes open source RISC-V Central Processing Units.
<!--ITEM/-->
<!--ITEM-->
### Demonstrator Groundwork
Our demonstrator lays the groundwork for a high-assurance reusable product for safety critical Digital Instrumentation and Control Systems systems in Nuclear Power Plants.
<!--ITEM/-->
<!-- All requirements that the RTS system must fulfill, as driven by the -->
<!-- IEEE 603-2018 standards and the NRC RFP. -->
<!--REQUIREMENTS/-->

<!--REQUIREMENTS-->
## NRC Characteristics
<!--ITEM-->
### Requirements Consistency
Requirements must be shown to be consistent.
<!-- The requirements driven by the IEEE 603-2018 standard for NPP I&C -->
<!-- systems. -->
<!-- Both formal and rigorous consistency checks of the requirements -->
<!-- will be accomplished by using false theorem checks and proofs in -->
<!-- the Cryptol model and in software and hardware source code; -->
<!--ITEM/-->
<!--ITEM-->
### Requirements Colloquial Completeness
The system must be shown to fulfill all requirements.
<!-- A rigorous completeness validation of the requirements will be -->
<!-- accomplished by demonstrating traceability from the project -->
<!-- specification (including the RFP text describing the reactor trip -->
<!-- system) to the formal models of the system and its properties. -->
<!--ITEM/-->
<!--ITEM-->
### Requirements Formal Completeness
Requirements must be shown to be formally complete.
<!-- A formal verification of completeness of the requirements will be -->
<!-- accomplished by using the chosen requirements checking tool -->
<!--ITEM/-->
<!--ITEM-->
### Instrumentation Independence
Independence among the four divisions of instrumentation (inability for the behavior of one division to interfere or adversely affect the performance of another).
<!-- This characteristic will be demonstrated architecturally via the -->
<!-- decoupling of computation across the two RISC-V instrumentation -->
<!-- cores and two instrumentation units running on the FPGA. -->
<!--ITEM/-->
<!--ITEM-->
### Channel Independence
Independence among the two instrumentation channels within a division (inability for the behavior of one channel to interfere or adversely affect the performance of another).
<!-- This characteristic will be demonstrated architecturally by -->
<!-- decoupling the compute and I/O channels of the units from one -->
<!-- another. -->
<!--ITEM/-->
<!--ITEM-->
### Actuation Independence
Independence among the two trains of actuation logic (inability for the behavior of one train to interfere or adversely affect the performance of another).
<!-- This characteristic will be demonstrated architecturally by -->
<!-- partitioning the actuation logic across software and hardware -->
<!-- units. -->
<!--ITEM/-->
<!--ITEM-->
### Actuation Correctness
Completion of actuation whenever coincidence logic is satisfied or manual actuation is initiated.
<!-- This characteristic will be demonstrated by rigorous validation via -->
<!-- runtime verification and formal verification of the model and its -->
<!-- implementation, as discussed in detail below. -->
<!--ITEM/-->
<!--ITEM-->
### Self-Test/Trip Independence
Independence between periodic self-test functions and trip functions (inability for the behavior of the self-testing to interfere or adversely affect the trip functions).
<!-- This characteristic will be demonstrated architecturally by -->
<!-- partitioning the actuation logic across software and hardware -->
<!-- units. -->
<!--ITEM/-->
<!--REQUIREMENTS/-->

