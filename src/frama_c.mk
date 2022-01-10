FRAMAC_FLAGS= -cpp-extra-args="-I include" -c11
FRAMAC=frama-c $(FRAMAC_FLAGS) -wp-rte -wp
GUI=frama-c-gui $(FRAMAC_FLAGS)

SRC=actuation_logic.c core.c sense_actuate.c\
    variants/actuation_unit_generated_C.c\
    variants/actuation_unit_generated_SystemVerilog.c\
    variants/instrumentation_generated_C.c\
    variants/instrumentation_generated_SystemVerilog.c\
    variants/instrumentation_handwritten_C.c\
    variants/instrumentation_handwritten_SystemVerilog.c\
    variants/actuator_generated_C.c\
    components/instrumentation_common.c


proofs: actuator_proof actuation_unit_proof instrumentation_proof validate_actuator_C validate_actuation_unit_C validate_instrumentation_unit_C

actuator_proof:
	$(FRAMAC) components/actuator.c -wp-fct actuate_devices

validate_actuator_C:
	$(FRAMAC) variants/actuator_generated_C.c -wp-fct ActuateActuator_generated_C

actuation_unit_proof:
	$(FRAMAC) components/actuation_unit.c -wp-fct actuation_logic_vote

validate_actuation_unit_C:
	$(FRAMAC) variants/actuation_unit_generated_C.c -wp-fct Actuate_D0_generated_C,Actuate_D1_generated_C,Coincidence_2_4_generated_C -wp-split -wp-split-depth 16 -wp-unfold-assigns 16 -wp-timeout 60 -wp-session wp-session -wp-prover tip,alt-ergo,z3

instrumentation_proof:
	$(FRAMAC) components/instrumentation.c -wp-fct instrumentation_step_trip

validate_instrumentation_unit_C: validate_instrumentation_unit_generated_C validate_instrumentation_unit_handwritten_C

validate_instrumentation_unit_generated_C:
	$(FRAMAC) variants/instrumentation_generated_C.c -wp-fct Generate_Sensor_Trips_generated_C,Is_Ch_Tripped_generated_C,Trip_generated_C -wp-split -wp-prover tip,alt-ergo,z3
validate_instrumentation_unit_handwritten_C:
	$(FRAMAC) variants/instrumentation_handwritten_C.c -wp-fct Generate_Sensor_Trips_handwritten_C,Is_Ch_Tripped_handwritten_C,Trip_handwritten_C -wp-split -wp-prover tip,alt-ergo,z3

gui:
	$(GUI) $(FRAMAC_FLAGS) -wp-split -wp-session wp-session -wp-cache update -wp-prover tip,alt-ergo,z3 $(SRC)
