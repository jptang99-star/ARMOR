# Armor project workflow front end.
#
# Named design targets use the design-to-command mapping below.  Generic
# targets accept DESIGN and optional RUN_ARMOR_ARGS for designs or parameter
# combinations that are not represented in that mapping.

SHELL := /bin/bash
.DEFAULT_GOAL := help

PYTHON ?= python3
SBT ?= sbt
RUN_ARMOR := script/run_armor.py

DESIGN ?=
DESIGNS ?=
RUN_ARMOR_ARGS ?=

MAPPED_DESIGNS := \
	GEMM_16_16_8 \
	Conv2D_16_16_8 \
	gemmini-full-32x32mesh-1x1-all-uint8 \
	MediumRocket-8C

RUN_ARMOR_ARGS_GEMM_16_16_8 := --driver random
RUN_ARMOR_ARGS_Conv2D_16_16_8 := --driver random
RUN_ARMOR_ARGS_gemmini-full-32x32mesh-1x1-all-uint8 := --driver random
RUN_ARMOR_ARGS_MediumRocket-8C := --driver emulator --slp-phase2 false

EFFECTIVE_RUN_ARMOR_ARGS = $(RUN_ARMOR_ARGS_$(DESIGN)) $(RUN_ARMOR_ARGS)


# make run DESIGN=GEMM_16_16_8
# make run DESIGN=Conv2D_16_16_8
# make run DESIGN=gemmini-full-32x32mesh-1x1-all-uint8
# make run DESIGN=MediumRocket-8C

.PHONY: \
	help build list-designs run gen compile execute batch \
	$(MAPPED_DESIGNS)

help:
	@printf '%s\n' \
	  'Armor Make targets:' \
	  '  make build                         Build utils/bin/essent.jar' \
	  '  make list-designs                  List FIR designs' \
	  '  make <mapped-design>               Run its mapped command' \
	  '  make batch DESIGNS="d0 d1"          Run mapped commands for several designs' \
	  '  make run DESIGN=<design>            Run default workflow for one design' \
	  '  make gen DESIGN=<design>            Generate C++ only' \
	  '  make compile DESIGN=<design>        Compile an existing generated simulator' \
	  '  make execute DESIGN=<design>        Run an existing emulator' \
	  '' 

build:
	./build.sh

list-designs:
	@find designs -maxdepth 1 -type f -name '*.fir' -printf '%f\n' | sed 's/\.fir$$//' | sort

$(MAPPED_DESIGNS):
	$(PYTHON) $(RUN_ARMOR) "$@" $(RUN_ARMOR_ARGS_$@)

batch:
	@if [[ -z "$(strip $(DESIGNS))" ]]; then \
	  echo 'error: provide one or more mapped designs: make batch DESIGNS="d0 d1"' >&2; \
	  exit 2; \
	fi
	@status=0; \
	for design in $(DESIGNS); do \
	  if ! $(MAKE) --no-print-directory "$$design"; then status=1; fi; \
	done; \
	exit $$status

run:
	$(call require-design)
	$(PYTHON) $(RUN_ARMOR) "$(DESIGN)" $(EFFECTIVE_RUN_ARMOR_ARGS)

gen:
	$(call require-design)
	$(PYTHON) $(RUN_ARMOR) "$(DESIGN)" --steps gen_sim $(EFFECTIVE_RUN_ARMOR_ARGS)

compile:
	$(call require-design)
	$(PYTHON) $(RUN_ARMOR) "$(DESIGN)" --steps compile $(EFFECTIVE_RUN_ARMOR_ARGS)

execute:
	$(call require-design)
	$(PYTHON) $(RUN_ARMOR) "$(DESIGN)" --steps run $(EFFECTIVE_RUN_ARMOR_ARGS)

define require-design
	@if [[ -z "$(strip $(DESIGN))" ]]; then \
	  echo 'error: provide DESIGN=<design>' >&2; \
	  exit 2; \
	fi
endef
