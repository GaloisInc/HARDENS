.PHONY: all validate

all: validate

validate: validate_lando validate_lobot

validate_lando:
	lando validate RTS.lando
	lando validate acronyms.lando
	lando validate architecture.lando
	lando validate dataflow.lando
	lando validate events.lando
	lando validate glossary.lando
	lando validate hardware.lando
	lando validate instrumentation.lando
	lando validate project_requirements.lando
	lando validate requirements.lando
	lando validate test_scenarios.lando
	lando validate tool_scenarios.lando

validate_lobot:
	lobot RTS.lobot
