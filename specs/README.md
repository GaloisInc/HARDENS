# HARDENS specifications 

This directory contains the specifications for the HARDENS Reactor Trip System:

- The high level project requirements and domain model specified in Lando (`*.lando` files), validated
  by `lando validate`; see [./Makefile](./Makefile)
- The project feature model [./RTS.lobot](./RTS.lobot) specified as a Lobot file (see [./Makefile](./Makefile))
- The system architecture in SysMLv2 (`*.sysml` files); see [../README.md](../README.md) for
  information on setting up an environment for viewing SysMLv2 files.

- The system requriements specified in FRET
  [./RTS_Requirements.json](./RTS_Requirements.json). 
  
  To view the requirements, install FRET <https://github.com/NASA-SW-VnV/fret>
  and import the [requirements](./RTS_Requirements.json). At the moment, to
  realizability checking requires the user to indicate the type of each variable
  and whether it is an input or output.
