CLANG9 ?=
CFLAGS = -g -O1 -I../src/include

proofs: instrumentation_proofs actuation_unit_proofs

../src/%.c: FORCE
	make -C ../src/ $*.c

generated/%.bc: generated/%.c ../src/generated/C/%.c
	$(CLANG9) $(CFLAGS) -o $@ -c $< -emit-llvm

handwritten/%.bc: handwritten/%.c ../src/handwritten/C/%.c
	$(CLANG9) $(CFLAGS) -o $@ -c $< -emit-llvm

actuation_unit_proofs: actuation_unit.saw generated/actuation_unit_impl.bc
	saw $<

instrumentation_proofs: instrumentation.saw generated/instrumentation_impl.bc handwritten/instrumentation_impl.bc
	saw $<

FORCE:
