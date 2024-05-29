# High Assurance Rigorous Digital Engineering for Nuclear Safety (HARDENS)

*Copyright (C) Galois 2021, 2022, 2023*

*Principal Investigator: Joe Kiniry <kiniry@galois.com>*

*Project Lead: Andrew Bivin <abivin@galois.com>*

*Research Engineers: Alexander Bakst <abakst@galois.com> and Michal Podhradsky <mpodhradsky@galois.com>*

*Special Thanks: Rishiyur Nikhil <nikhil@bluespec.com>*

Repository for the HARDENS project for the 
[Nuclear Regulatory Commission](https://www.nrc.gov/about-nrc.html).

```
This work is supported by the U.S. Nuclear Regulatory Commission 
(NRC), Office of Nuclear Regulatory Research, under contract/order 
number 31310021C0014.

All material is considered in development and not a finalized product. 

Any opinions, findings, conclusions or recommendations expressed in
this material are those of the author(s) and do not necessarily
reflect the views of the NRC.
```

## Project Overview

The goal of HARDENS is to provide to the NRC expert technical services
in order to (1) develop a better understanding of how Model-Based
Systems Engineering (MBSE) methods and tools can support regulatory
reviews of adequate design and design assurance, and (2) identify any
barriers or gaps associated with MBSE in a regulatory review of
Digital Instrumentation and Control Systems for existing Nuclear Power
Plants (NPPs).

In the HARDENS project Galois will demonstrate to the Nuclear
Regulatory Commission (NRC) cutting- edge capabilities in the
model-based design, validation, and verification of safety-critical,
mission-critical, high-assurance systems. Our demonstrator includes
high-assurance software and hardware, includes open source RISC-V
Central Processing Units (CPUs), and lays the groundwork for a
high-assurance reusable product for safety critical Digital
Instrumentation and Control Systems systems in NPPs.

Details about the HARDENS project are found in our 
[original proposal](docs/HARDENS.pdf), which was written in response 
to the [original NRC RFP](docs/RFP.pdf).

This document summarizes the current state of affairs of the project
and demonstrator.

## Executive Summary

In the **High Assurance Rigorous Digital Engineering for Nuclear
Safety** (HARDENS) project, Galois has developed a high-assurance,
safety-critical demonstration system for the Nuclear Regulatory
Commission using Rigorous Digital Engineering (RDE).  The system in
question is a Digital Instrumentation and Control (DI&C) system for
Nuclear Power Plants (NPPs), and is called the Reactor Trip System
(RTS).

RDE is the combination of *Model-based Engineering*, *Digital
Engineering*, and *Applied Formal Methods*.  The engineering focus of
RDE is broad, as we have used it to perform *software, firmware,
hardware, systems, domain, requirements, product line, safety, and
security engineering* of *high-assurance, secure-by-design systems*.
The HARDENS project includes nearly all of these kinds of engineering,
but for security engineering at this time.

To our knowledge, this demonstrator is the most rigorously specified
and assured system of its kind that includes formally assured software
and hardware for a safety-critical system.

*Model-based Engineering* focuses on the use of semi-formal and formal
models and their properties to describe aspects of a system
independent of a particular implementation.  Models are connected to
each other through a variety of relations (refinement, containment,
subtyping/subsumption/implication, traceability, etc.), models are
either or both denotational or operational (and thus executable), and
models are used to specify, examine, understand, and reason about a
system well-prior to a line of code ever being written.  Models are
used for rigorous validation---through automatic model-based test
bench generation and bisimulation---and formal verification---through
automatic model-based verification bench generation.

The models used in HARDENS include, from most to least abstract:

 - a Lando high-level system specification model, which includes
   within it:
   + a domain engineering model, 
   + a requirements engineering model, which includes:
     * derived certification requirements,
     * contractual requirements,
     * safety requirements, and
     * correctness requirements.
   + a product line (feature) model, 
   + a static system model, 
   + a dataflow model of the RDE methodology, 
   + a system event model, 
   + a system scenario model (including all normal and exceptional
     behaviors),
   + a hardware, software, and evidence Bill of Materials (BOMs), 
 - a SysMLv2 system model, which includes within it, as refined
   directly from the Lando model:
   + a stakeholder model,
   + a domain engineering model,
   + a requirements engineering model,
   + property specifications for all correctness and safety properties
     derived from the formal requirements model,
   + a product line (feature/variant) model,
   + a static system model that includes both the software and
     hardware manifestations of the system,
   + a system action model, and
   + a validation and verification assurance case model.
 - a formal requirements model expressed in JPL's FRET tool, as
   refined from the Lando and SysMLv2 requirements models above,
 - a Cryptol model of the entire system, including all subsystems and
   components, including formal, executable digital twin models of the
   system's sensors, actuators, and compute infrastructure, and this
   Cryptol model includes a refinement of all formal requirements from
   FRET into Cryptol properties (theorems) about the Cryptol model
   itself,
 - a model of the semantics of the RISC-V instruction set,
 - a model-based specification of critical portions of the RTS's
   software stack expressed in ACSL,
 - an executable and synthesizable Bluespec System Verilog model of a
   family of RISC-V-based SoCs, and
 - a System Verilog executable and synthesizable model of a simple,
   in-order 32-bit RISC-V CPU (NERV, from YosysHQ).

Digital Engineering focuses on the use of *digital twins* of physical
systems, subsystems, and their components.  A digital twin is
typically an executable model that has known and measurable objective
fidelity in relation to the models or systems that relate to the twin.
For example, an executable Cryptol or SCADE model are a digital twins.

The HARDENS system includes several digital twins, including
simulation and emulation of the system hardware (CPUs and SoCs),
software implementation, and system model.

Applied formal methods are the sensible use of formal methods
concepts, tools, and technologies to formally specifying and reasoning
about systems and their properties.  In the context of RDE and the
HARDENS project, we use formal methods to achieve the following
assurance:

 - critical components of the RTS are automatically synthesized from
   Cryptol model into both formally verifiable C implementations and
   formally verifiable System Verilog implementations,
 - automatically generated C code and hand-written implementations of
   the same models are used to fulfill safety-critical redundancy and
   fault-tolerance requirements, and all of those implementations are
   formally verified both against their model, as well as verified
   against each other as being equivalent, using Frama-C and Galois's
   SAW tool,
 - the RISC-V CPU is formally verified against the RISC-V ISA
   specification using the Yosys open source verification tool,
 - the RISC-V-based SoC is rigorously assured against the
   automatically generated end-to-end test bench,
 - the formal requirements specified in FRET are formally verified for
   consistency, completeness, and realizability using SAT and SMT
   solvers,
 - the refinement of these requirements into Cryptol properties are
   used as model validation theorems to rigorously check and formally
   verifying that the Cryptol model conforms to the requirements,
 - the Cryptol model is used to automatically generate a component-level
   and end-to-end test bench (in C) for the entire system, and that
   test bench is executed on all digital twins and (soon) the full
   hardware implementation as well, and
 - all models and assurance artifacts are traceable and sit in a
   semi-formal refinement hierarchy that spans semi-formal system
   specification written in precise natural language all of the way
   down for formally assured source code (in verifiable C), (a
   side-effect of the optional use of CompCert) binaries, and hardware
   designs (in System Verilog and Bluespec System Verilog).

## Task 1: Implementation

As described in our proposal and the project Statement of Work, in
Task 1 (Implementation), the first task of the HARDENS project, Galois
will implement the system described above using both (1) highly
integrated computer-based engineering development processes and (2)
model-based systems engineering.  All the modules of the simple
protection system will be modeled functionally, and one FPGA-based
circuit card will be modeled/designed in detail. The deliverable will
be the model-based design itself. We will use Galois’s RDE process and
methodology to achieve this goal, as well as the V&V in Task 2.

All project models---the SysMLv2 model, the executable, rigorously
validated and formally verified Cryptol model, and the semi-formal and
formal requirements model---are included in this release and are found
in the `develop` branch of the repository.

Also, the initial implementation of the system which runs as an
application on a POSIX host (e.g., a Linux or macOS development
machine or in the HARDENS Docker image) is found in the
as-of-yet-unmerged `c-impl` branch in the HARDENS repository.  That
implementation includes both hand-written C code conforming to the
model-based specifications discussed above, as well as automatically
synthesized formally verified sub-components, as described in the
HARDENS proposal, for a small handful of critical sub-components.
These synthesized components are generated in formally verified C
source code and in the System Verilog HDL. The POSIX-based simulation
can execute both the generated C components and the generated System
Verilog components by means of a shim library wrapping the Verilated
components.

Finally, we have a formally verified RISC-V CPU, called the `nerv`
CPU, built and tested on the ECP5-5G board.  We have sketched out
an initial three core SoC design using Bluespec SystemVerilog, but
have not yet built that SoC for emulation or put it on the FGPA.  We
will accomplish such early in Task 2, and cross-compile our POSIX C
implementation to that SoC.  That ongoing work is found in the `nerv`
branch of the repository.

## Task 2: Validation and Verification

As described in the Statement of Work, for Task 2 of the HARDENS
project Galois will perform preliminary validation and verification
and testing of the design using model-based engineering and testing
methods. The deliverable will be the artifacts as described in the
proposal.

The [Hardens Assurance Case](./Assurance.md) document in this
repository describes the end-to-end specification-to-implementation
process, system requirements, testing, and V&V associated with Task 2
deliverables. Rather than restate the document's contents here, Galois
recommends reviewing it as a conextualized summary of Task 2
artifacts.

Galois will continue to develop V&V capabilities and port the design
to actual hardware in preparation for Tasks 3 (Evaluation) and 4
(Presentation).

## Task 3: Evaluation

In order to evaluate the system, one might read the project's slide
decks (see Task 4 below), read the project's final report (see Task 5
below), and review the system's models, specifications,
implementation, and assurance.  This section summarizes the details of
this latter aspect.

We summarize in this section:

 - the structure of the project's repository, 
 - its submodules/dependencies, 
 - our use of a Docker containers to standardize development and
   evaluation virtual platforms, and
 - our hardware development board(s) used for the physical
   demonstrator (which is still under development) and the product's
   I/O devices.

### Repository Structure

The repository is structured as follows:

- [specs](./specs) contains a domain model (`*.lando`, `*.lobot`),
  requirements (exported from `FRET` to `RTS_requirements.json`), and
  a specification of the RTS architecture (`*.sysml`).
- [models](./models) contains the executable Cryptol model
- [assets](./assets) and [docs](./docs) contain project and device
  documentation
- [saw](./saw) contains SAW-based proofs of correctness of specific
  model-derived components
- [tests](./tests) contains end-to-end tests derived from the lando
  test scenarios.

### Submodules

This repository does not currently use any submodules.  If/when it
does, initialize with:

```
$ git submodule init
$ git submodule update --recursive
```

### Docker

A Docker container has been built to make for easier use, evaluation,
reusability, and repeatability of project results.  We are adding
tools to this container as necessary during project execution.

#### HARDENS Container

To build and run the core HARDENS Docker image, use the prebuild `galoisinc/hardens:latest` image. Note that `build_docker.sh` currently does not work, as `cryptol-codegen` no longer builds. Best if you use the following command:

```
$ docker run --network host --privileged -v $PWD:/HARDENS -it \
  galoisinc/hardens:latest
```

In order to run a long-lived Docker container for reuse, use a `docker
run` command like the following, ensuring that you are in the right
directory in order to bind your sandbox properly into the container.

```
$ docker run -d -it --name HARDENS --network host --privileged \
  -v $PWD:/HARDENS galoisinc/hardens:latest
```

If you have stopped a container running and it lists as "exited" when
you run a `docker container ls`, then you can restart it with the
following command.

```
$ docker start HARDENS
```

After running such a detached container, attach to it for interactive
use by running a command like:
```
$ docker exec -it HARDENS bash -l
```

The helper script `run_docker.sh` executed the above detached run
command, using Galois's public docker HARDENS image.  The helper
script `docker_shell.sh` runs a shell in the spawned container.

#### SysMLv2 Container

To pull and use the pre-build SysMLv2 container, use the following
`pull` command to pull the container from DockerHub.  

See https://hub.docker.com/r/gorenje/sysmlv2-jupyter for details.

```
$ docker pull gorenje/sysmlv2-jupyter:latest
$ docker run -d -it --name SysMLv2 --network host -v $PWD:/HARDENS \
  gorenje/sysmlv2-jupyter:latest
```

The Docker container contains snapshots of various tools that are not
necessarily the latest releases or development versions of said tools.
We include these particular versions because they are the versions
used for development of the demonstrator, in alignment with our
*Tool Dependencies* recommendations, **Tool Metadata**, **Tool
Availability**, and **Evaluation Platform**.

In particular, the version of Lando shipped in the image is incapable
of converting Lando input files into hyperlinked Markdown, as we
provide in [specs/Lando/](specs/Lando/).  This is partly due to the
fact that the new version of Lando is not ready for release and is
only available via Galois's private GitLab server.

### Lattice ECP5 evaluation board

We are using an ECP5-5G FPGA board for the RTS demonstrator.

Details [here](https://www.latticesemi.com/products/developmentboardsandkits/ecp5evaluationboard#_C694C444BC684AD48A3ED64C227B6455). The board uses ECP5-5G FPGA ([LFE5UM5G-85F-8BG381](https://www.latticesemi.com/en/Products/FPGAandCPLD/ECP5)) which has:

- 84k LUTs
- On-board Boot Flash – 128 Mbit Serial Peripheral Interface (SPI) Flash, with Quad read feature
- 8 input DIP switches, 3 push buttons and 8 LEDs for demo purposes

![ECP_board](assets/ecp5_top.png)

#### GPIO headers

Headers are: J5, J8, J32, J33 and Max I_OUT for 3V3 is 1.35A

J5 pinout:

* 1, 2 - VCCIO2 (Sensor 1 VIN, Sensor 2 VIN)
* 3, 4 - H20, G19 (Sensor 1 I2C)
* 5, 6 - GND (Sensor 1 GND, Sensor 2 GND)
* 7, 8 - K18, J18 (Sensor 2 I2C)

#### LEDs:

Several LEDs are available.

![ECP_LED](assets/ecp5_leds.png)

#### Switches

Several switches are available.

![ECP_DIP](assets/ecp5_dip.png)

#### Buttons

General purpose button `SW4` is connected to `P4`

### Sensors/Actuators

* MOSFET power control kit: https://www.sparkfun.com/products/12959
* 12 V Latch solenoid: https://www.sparkfun.com/products/15324
* Pressure sensor: https://www.sparkfun.com/products/11084

## Task 4: Presentation

Multiple slide decks have been written about this case study, and it
has been presented in several forums.  One deck is the final
presentation that was given to the NRC.

### Slide Deck

The HARDENS slide deck is meant to fully characterize the RTS
demonstrator and also, in tandem, explain the concepts, technologies,
and tools of model-driven engineering in the large.  This means that
we will be reviewing technologies that are used in the project as well
as those that are commonly used for MDE for hardware, firmware,
software, systems, safety, and security engineering.  Tools reviewed
will include all mainstream MBSE tools, tools that we use for
demonstrating correct-by-construction components and subsystems, and a
variety of assurance tools.

There are three versions of the HARDENS talk:

 1. A [short version summarizing the HARDENS
    project](docs/HARDENS_HCSS_May_2022.pdf), which was given at HCSS
    in May 2022.
 2. A [90 minute
    version](docs/HARDENS_Galois_Explaining_RDE_by_Example_May_2022.pdf)
    which was used to give a presentation at Galois in May 2022 about
    Rigorous Digital Engineering.  Friends of Galois attended this
    talk as well.
 3. A [six hour version that was the final presentation for the entire
    project to the NRC](docs/HARDENS_NRC_Oct_2022.pdf), given on 12
    October 2022.

These presentations were all written using Apple Keynote.  The
canonical source for the final presentation is found in the file
[HARDENS.key](docs/HARDENS.key).  A PowerPoint version of the slide
deck is also exported from Keynote and in the same directory. No
attempt has been made to make sure the exported PowerPoint is pretty.

## Task 5: Final Report

A final report for the NRC was written.

### Final Report

Our final report for HARDENS must have the following characteristics:

 1. [X] it must be well-suited to fit into the document-centric
        certification process used by the NRC and other similar
        government agencies,
 2. [X] it must completely describe the framing for the project, the
        technical work, the safety and correctness assurance case of
        the RTS demonstrator, and the manner in which the document can
        be read, the R&D can/should be reviewed, etc.
 3. [X] It must include all formal specifications and assurance
        artifacts as nicely typeset, hyper-textual cross-referenced
        appendix chapters.

In order to fulfill (1) above, the final report must be both:

 1. [X] a polished, high-quality, hyperlinked HTML web page, or set of
        web pages that compile into a single web page, that contains the
        entire report, includes its technical appendices, and
 2. [X] a polished, high-quality, hyperlinked PDF document that can be
        printed on paper and, in that form, it just as easy to read
        front-to-back and to follow cross-references therein.

In order to help certification actors review a model-based system and
its assurance case, we intend to provide a chapter in the report that
characterizes a workflow and set of best practices for such a review.

The source of the final report is available (invite only at the
minute) via [https://git.overleaf.com/623259a297f75c655f6d1f47](Overleaf), 
and a [PDF snapshot](./docs/HARDENS_Final_Report_Oct_2022.pdf)
of the final report is available in [docs folder](./docs/).

## License

   Copyright 2021, 2022, 2023 Galois, Inc.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

Portions of this system have additional copyright notices.

