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

LANDO=java -jar ../assets/lando-2.0-12-Jan-2022-29a47e19-jar-with-dependencies.jar
LOBOT=/tools/lando/source/lobot/dist-newstyle/build/x86_64-linux/ghc-8.8.4/lobot-0.1/x/lobot/build/lobot/lobot
OBJS := $(patsubst %.lando,%.md,$(wildcard Lando/*.lando))

.PHONY: all validate

all: $(OBJS)

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

%.md : %.lando
	@echo "Converting $< to $@"
	@$(LANDO) convert --to markdown $< $@

clean :
	@rm -rf $(OBJS)
