F ?=
FRAMAC_FLAGS= -cpp-extra-args="-I include" -c11 -wp-split -wp-session wp-session -wp-cache update -wp-smoke-tests $(F)
WP=frama-c $(FRAMAC_FLAGS)
FRAMAC=frama-c $(FRAMAC_FLAGS) -wp-rte -wp $(FRAMAC_FLAGS) -wp-prover tip,alt-ergo,z3
GUI=frama-c-gui $(FRAMAC_FLAGS) -wp-rte -wp-prover tip

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
	$(FRAMAC) variants/actuator_generated_C.c $(EXCLUDE_ACT)

actuation_unit_proof:
	$(FRAMAC) variants/actuation_unit_generated_C.c $(EXCLUDE_ACTU)

instrumentation_proof:
	$(FRAMAC) variants/instrumentation_generated_C.c variants/instrumentation_handwritten_C.c $(EXCLUDE_INSTR)

gui:
	$(GUI) $(SRC)
