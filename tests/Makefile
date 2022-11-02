# Run all scenario-based tests on whichever RTS digital twins exist.

all: test

quick:
	(QUICK=1 make test)

debug_test:
	(RTS_DEBUG=1 make test)

test:
	./run_all.py
