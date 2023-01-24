# Executable Behavioral Specification

## Alex Bakst, November 2021--February 2022

This directory contains the executable behavioral model, implemented in Cryptol,
which refines the formal specification given by the domain model, requirements,
and architecture in the [specs](../specs) directory.

## Methodology

The Cryptol model provides implementations of the components given in the
SysMLv2 architecture. Generally, the components are modeled either as (1) pure
functions, as in the case of `CoincidenceLogic`; or (2) as a record of component
state together with functions that manipulate such records, as in the case of
`Actuator`s. In either case, the model is designed to give an unambiguous
specification behaviors of the different components.

## Relationship to SysMLv2 model

The model is designed such that its connection to the architecture specification
is apparent, which is to say that given a component in the architecture, it
should be straightforward to identify the corresponding implementation in the
model. The following is a brief overview of this relationship.

In general, attributes in the architecture diagram are modeled as bitvectors in
Cryptol: `Boolean`s become `Bit`s, `enum`s with `n` values become `[lg2 n]`
(bitvectors of length `log_2(n)`), etc. 

Sometimes there is tension between straightforward translation to `Cryptol` and
ease of synthesizing implementations (such as `C` code): in such cases, we may
use `[8]` (bytes) to model `Boolean` values.

### RTS/Actuator.cry

This module models the `Actuator` part, with two operations to set automatic and
manual actuation.

### RTS/InstrumentationUnit.cry

The `InstrumentationUnit` part is modeled by a record of the same name that
capture the important attributes. The `Step` function in this module models the
simultaneous response of an `InstrumentationUnit` to the different sensor inputs
and commands.

### RTS/ActuationUnit.cry

This module models the `ActuationUnit` part. The actuation output ports are
captured by the `ActuationUnit` `output` field, while the named logic parts
`TemperatureLogic`, `SaturationLogic`, and the like, are modeled by functions
with the same name.

### RTS.cry

The Cryptol `RTS` type models the composition of the types exposed by the
previous modules in accordance with the architecture: one `Instrumentation`
component comprising 4 `InstrumentationUnit`s, one `Actuation` component
comprising 2 `ActuationUnit`s and 2 `Actuator`.

`Sense_Actuate` models the flow of the connections between the different
components (i.e., from sensor to actuator) as indicated by the architecture.

`Event_Control` models the `EventControl` package and `ControlUnit`
behavior.

## Implementation Status

- Each component in the architecture has a representation as Cryptol
  type and/or functions.

- Each Cryptol module has a set of _properties_ that are true of the
  model. These properties are either derived from the formal
  requirements (and indicated as such), or are further refinements of
  the system behavior. These properties are all provable by `SMT`
  except where indicated.
  
- The `InstrumentationUnit` module currently uses a strawman
  implementation for calculating the saturation margin given a
  temperature and pressure. The model is agnostic to its actual
  implementation, but this will be replaced by a lookup table derived
  from standard steam tables.

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
