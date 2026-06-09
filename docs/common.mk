ROOT_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
BUILD_DIR ?= $(ROOT_DIR)/../build
BUILD_CMD := $(BUILD_DIR)/$(PROGRAM_PREFIX)

ABC ?= $(BUILD_CMD)yosys-abc
YOSYS ?= $(BUILD_CMD)yosys
YOSYS_CONFIG ?= $(BUILD_CMD)yosys-config
YOSYS_FILTERLIB ?= $(BUILD_CMD)yosys-filterlib
YOSYS_SMTBMC ?= $(BUILD_CMD)yosys-smtbmc
YOSYS_WITNESS ?= @$(BUILD_CMD)yosys-witness

export BUILD_DIR
export SBY
export ABC
export YOSYS
export YOSYS_CONFIG
export YOSYS_FILTERLIB
export YOSYS_SMTBMC
export YOSYS_WITNESS
