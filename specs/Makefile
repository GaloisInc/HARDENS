LANDO=java -jar ../assets/lando-2.0-12-Jan-2022-29a47e19-jar-with-dependencies.jar
LOBOT=/tools/lando/source/lobot/dist-newstyle/build/x86_64-linux/ghc-8.8.4/lobot-0.1/x/lobot/build/lobot/lobot

.PHONY: all validate

all: validate

validate: validate_lando validate_lobot

validate_lando:
	$(LANDO) validate Lando/RTS.lando
	$(LANDO) validate Lando/acronyms.lando
	$(LANDO) validate Lando/architecture.lando
	$(LANDO) validate Lando/dataflow.lando
	$(LANDO) validate Lando/events.lando
	$(LANDO) validate Lando/glossary.lando
	$(LANDO) validate Lando/hardware.lando
	$(LANDO) validate Lando/instrumentation.lando
	$(LANDO) validate Lando/project_requirements.lando
	$(LANDO) validate Lando/requirements.lando
	$(LANDO) validate Lando/test_scenarios.lando
	$(LANDO) validate Lando/tool_scenarios.lando

validate_lobot:
	$(LOBOT) RTS.lobot
