LANDO=lando.sh
LOBOT=/tools/lando/source/lobot/dist-newstyle/build/x86_64-linux/ghc-8.8.4/lobot-0.1/x/lobot/build/lobot/lobot

.PHONY: all validate

all: validate

validate: validate_lando validate_lobot

validate_lando:
	$(LANDO) validate RTS.lando
	$(LANDO) validate acronyms.lando
	$(LANDO) validate architecture.lando
	$(LANDO) validate dataflow.lando
	$(LANDO) validate events.lando
	$(LANDO) validate glossary.lando
	$(LANDO) validate hardware.lando
	$(LANDO) validate instrumentation.lando
	$(LANDO) validate project_requirements.lando
	$(LANDO) validate requirements.lando
	$(LANDO) validate test_scenarios.lando
	$(LANDO) validate tool_scenarios.lando

validate_lobot:
	$(LOBOT) RTS.lobot
