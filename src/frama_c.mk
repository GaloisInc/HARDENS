#   Copyright 2021, 2022, 2023 Galois, Inc.
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.

F ?=
FRAMAC_FLAGS= -cpp-extra-args="-I include -I ../hardware/SoC/firmware" -c11 -wp-split -wp-session wp-session -wp-cache update -wp-smoke-tests $(F)
WP=frama-c $(FRAMAC_FLAGS)
FRAMAC=frama-c $(FRAMAC_FLAGS) -wp-rte -wp $(FRAMAC_FLAGS) -wp-prover tip,alt-ergo,z3
GUI=frama-c-gui $(FRAMAC_FLAGS) -wp-rte -wp-prover tip,alt-ergo-z3

SRC=actuation_logic.c core.c sense_actuate.c\
    variants/actuation_unit_generated_C.c\
    variants/actuation_unit_generated_SystemVerilog.c\
    variants/instrumentation_generated_C.c\
    variants/instrumentation_generated_SystemVerilog.c\
    variants/instrumentation_handwritten_C.c\
    variants/instrumentation_handwritten_SystemVerilog.c\
    variants/actuator_generated_C.c\
    components/instrumentation_common.c

EXCLUDE_ACT=$(addprefix -wp-skip-fct , rotl1 rotl2 rotr1 rotr2 )
EXCLUDE_ACTU=$(addprefix -wp-skip-fct , rotl1 rotl2 rotl8 rotr1 rotr2 rotr8)
EXCLUDE_INSTR=$(addprefix -wp-skip-fct , rotl1 rotl2 rotl3 rotl32 rotr1 rotr2 rotr3 rotr32)

proofs: actuator_proof actuation_unit_proof instrumentation_proof

report:
	$(FRAMAC) \
      variants/actuator_generated_C.c \
      variants/actuation_unit_generated_C.c \
      variants/instrumentation_generated_C.c \
      variants/instrumentation_handwritten_C.c \
      $(EXCLUDE_ACT) $(EXCLUDE_ACTU) $(EXCLUDE_INSTR) \
      -then -report

metrics:
	frama-c $(SRC) -metrics -cpp-extra-args="-I include" -c11

actuator_proof:
	$(FRAMAC) components/actuator.c
	$(FRAMAC) -cpp-extra-args='-include "common.h" -include "actuate.h"' generated/C/actuator_impl.c $(EXCLUDE_ACT)

actuation_unit_proof:
	$(FRAMAC) components/actuation_unit.c
	$(FRAMAC) -cpp-extra-args='-include "common.h" -include "actuation_logic.h"'  generated/C/actuation_unit_impl.c $(EXCLUDE_ACTU)

instrumentation_proof:
	$(FRAMAC) components/instrumentation.c
	$(FRAMAC) -cpp-extra-args='-include "common.h" -include "instrumentation.h"' generated/C/instrumentation_impl.c $(EXCLUDE_INSTR)
	$(FRAMAC) -cpp-extra-args='-include "common.h" -include "instrumentation.h"' handwritten/C/instrumentation_impl.c

actuator_gui:
	$(GUI) -cpp-extra-args='-include "common.h" -include "actuate.h"'  generated/C/actuator_impl.c $(EXCLUDE_ACTU)

actuation_unit_gui:
	$(GUI) -cpp-extra-args='-include "common.h" -include "actuation_logic.h"'  generated/C/actuation_unit_impl.c $(EXCLUDE_ACTU)

instrumentation_gui_generated:
	$(GUI) -cpp-extra-args='-include "common.h" -include "instrumentation.h"' generated/C/instrumentation_impl.c $(EXCLUDE_INSTR)

instrumentation_gui_handwritten:
	$(GUI) -cpp-extra-args='-include "common.h" -include "instrumentation.h"' handwritten/C/instrumentation_impl.c $(EXCLUDE_INSTR)
