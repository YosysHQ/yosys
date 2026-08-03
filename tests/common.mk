ROOT_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
BUILD_DIR ?= $(realpath $(ROOT_DIR)/../build)
BUILD_CMD := $(BUILD_DIR)/$(PROGRAM_PREFIX)
SRC_DIR := $(realpath $(ROOT_DIR)/..)

SBY ?= sby
ABC ?= $(BUILD_CMD)yosys-abc
YOSYS ?= $(BUILD_CMD)yosys
YOSYS_CONFIG ?= $(BUILD_CMD)yosys-config
YOSYS_FILTERLIB ?= $(BUILD_CMD)yosys-filterlib
YOSYS_SMTBMC ?= $(BUILD_CMD)yosys-smtbmc
YOSYS_WITNESS ?= @$(BUILD_CMD)yosys-witness
YOSYS_MAX_THREADS ?= 4
COVERAGE_DIR ?= $(realpath $(ROOT_DIR)/..)/coverage
COVERAGE_HTML ?= $(realpath $(ROOT_DIR)/..)/coverage_html
LLVM_PROFILE_FILE ?= $(COVERAGE_DIR)/coverage_%p.profraw
VERIFIC_DIR ?= /usr/local/src/verific_lib

export BUILD_DIR
export SBY
export ABC
export YOSYS
export YOSYS_CONFIG
export YOSYS_FILTERLIB
export YOSYS_SMTBMC
export YOSYS_WITNESS
export YOSYS_MAX_THREADS
export LLVM_PROFILE_FILE
export LLVM_PROFILE_FILE_BUFFER_SIZE=0

ifeq ($(or $(V),$(VERBOSE)),1)
  QUIET :=
else
  QUIET := >/dev/null 2>&1
endif

all:

ifndef OVERRIDE_MAIN
clean:
	@rm -f *.log *.result
endif

define run_test
	@set -e; \
	rc=0; \
	( set -e; $(2) ) $(QUIET) || rc=$$?; \
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
