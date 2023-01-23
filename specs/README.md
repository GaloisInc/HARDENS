# HARDENS specifications 

This directory contains the specifications for the HARDENS Reactor Trip System:

- The high level project requirements and domain model specified in
  Lando (`*.lando` files), validated by `lando validate`; see
  [./Makefile](./Makefile)
- The project feature model [./RTS.lobot](./RTS.lobot) specified as a
  Lobot file (see [./Makefile](./Makefile))
- The system architecture in SysMLv2 (`*.sysml` files); see
  [../README.md](../README.md) for information on setting up an
  environment for viewing SysMLv2 files.

- The system requriements specified in FRET
  [./RTS_Requirements.json](./RTS_Requirements.json). 
  
  To view the requirements, install FRET
  <https://github.com/NASA-SW-VnV/fret> and import the
  [requirements](./RTS_Requirements.json). At the moment, to
  realizability checking requires the user to indicate the type of
  each variable and whether it is an input or output.

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
