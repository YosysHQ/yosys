ROOT_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
BUILD_DIR ?= $(ROOT_DIR)/..
ifneq ($(wildcard $(ROOT_DIR)/../Makefile.conf),)
include $(ROOT_DIR)/../Makefile.conf
endif

SBY   ?= sby
YOSYS ?= $(BUILD_DIR)/yosys
ifneq ($(ABCEXTERNAL),)
ABC	  ?= $(ABCEXTERNAL)
else
ABC   ?= $(BUILD_DIR)/yosys-abc
endif
YOSYS_FILTERLIB ?= $(BUILD_DIR)/yosys-filterlib
YOSYS_CONFIG ?= $(BUILD_DIR)/yosys-config
YOSYS_SMTBMC ?= $(BUILD_DIR)/yosys-smtbmc
YOSYS_MAX_THREADS ?= 4

export YOSYS
export YOSYS_CONFIG
export YOSYS_SMTBMC
export ABC
export SBY
export YOSYS_MAX_THREADS

all:

ifndef OVERRIDE_MAIN
clean:
	@rm -f *.log *.result
endif

define run_test
	@set -e; \
	rc=0; \
	( set -e; $(2) ) >/dev/null 2>&1 || rc=$$?; \
	if [ $$rc -eq 0 ]; then \
		echo "PASS $1"; \
		echo PASS > $1.result; \
	else \
		echo "FAIL $1"; \
		echo FAIL > $1.result; \
	fi
endef

.PHONY: summary
summary:
	@pass=$$(find . -type f -name '*.result' -exec grep '^PASS$$' {} + | wc -l); \
	fail=$$(find . -type f -name '*.result' -exec grep '^FAIL$$' {} + | wc -l); \
	total=$$((pass + fail)); \
	echo "=========================="; \
	echo "Tests: $$total"; \
	echo "Passed: $$pass"; \
	echo "Failed: $$fail"; \
	echo "=========================="; \
	if [ $$fail -ne 0 ]; then \
		echo; \
		$(MAKE) --no-print-directory report; \
	fi; \
	test $$fail -eq 0

.PHONY: report
report:
	@echo "=========================="
	@echo "Failing tests:"
	@find . -name '*.result' -type f -exec grep -H '^FAIL$$' {} + \
	  | cut -d: -f1 \
	  | sed 's|^\./||; s|\.result$$||'
	@echo "=========================="
