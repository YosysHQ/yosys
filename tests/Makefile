ifneq ($(wildcard ../Makefile.conf),)
include ../Makefile.conf
endif

OVERRIDE_MAIN=1
include ./common.mk

# Directories with tests not run:
#  errors
#  lut
#  pyosys
#  smv
#  sva
#  tools
#  unit
#  vloghtb

# Tests that generate Makefile with gen_tests_makefile.py
MK_TEST_DIRS =
MK_TEST_DIRS += ./arch/analogdevices
MK_TEST_DIRS += ./arch/anlogic
MK_TEST_DIRS += ./arch/ecp5
MK_TEST_DIRS += ./arch/efinix
MK_TEST_DIRS += ./arch/fabulous
MK_TEST_DIRS += ./arch/gatemate
MK_TEST_DIRS += ./arch/gowin
MK_TEST_DIRS += ./arch/ice40
MK_TEST_DIRS += ./arch/intel_alm
MK_TEST_DIRS += ./arch/machxo2
MK_TEST_DIRS += ./arch/microchip
MK_TEST_DIRS += ./arch/nanoxplore
MK_TEST_DIRS += ./arch/nexus
MK_TEST_DIRS += ./arch/quicklogic/pp3
MK_TEST_DIRS += ./arch/quicklogic/qlf_k6n10f
MK_TEST_DIRS += ./arch/xilinx
MK_TEST_DIRS += ./bind
MK_TEST_DIRS += ./bugpoint
MK_TEST_DIRS += ./opt
MK_TEST_DIRS += ./sat
MK_TEST_DIRS += ./sdc
MK_TEST_DIRS += ./sim
MK_TEST_DIRS += ./svtypes
MK_TEST_DIRS += ./techmap
MK_TEST_DIRS += ./various
MK_TEST_DIRS += ./rtlil
ifeq ($(ENABLE_VERIFIC),1)
ifneq ($(YOSYS_NOVERIFIC),1)
MK_TEST_DIRS += ./verific
endif
endif
MK_TEST_DIRS += ./verilog

# Tests that don't generate .mk
SH_TEST_DIRS =
MK_TEST_DIRS += ./simple
MK_TEST_DIRS += ./simple_abc9
MK_TEST_DIRS += ./hana
MK_TEST_DIRS += ./asicworld
MK_TEST_DIRS += ./realmath
MK_TEST_DIRS += ./share
MK_TEST_DIRS += ./opt_share
MK_TEST_DIRS += ./fsm
MK_TEST_DIRS += ./memlib
MK_TEST_DIRS += ./bram
#SH_TEST_DIRS += ./svinterfaces
MK_TEST_DIRS += ./xprop
MK_TEST_DIRS += ./select
MK_TEST_DIRS += ./peepopt
MK_TEST_DIRS += ./proc
MK_TEST_DIRS += ./blif
MK_TEST_DIRS += ./arch
MK_TEST_DIRS += ./rpc
MK_TEST_DIRS += ./memfile
#SH_TEST_DIRS += ./fmt
MK_TEST_DIRS += ./cxxrtl
MK_TEST_DIRS += ./liberty
#ifeq ($(ENABLE_FUNCTIONAL_TESTS),1)
#SH_TEST_DIRS += ./functional
#endif

# Tests that don't generate .mk and need special args
MK_TEST_DIRS += ./memories
MK_TEST_DIRS += ./aiger
MK_TEST_DIRS += ./alumacc

all: vanilla-test

# seed-./ is a dummy string, not a directory
.PHONY: seed-tests
seed-tests: $(SH_TEST_DIRS:%=seed-./%)
.PHONY: seed-./%
seed-./%: %/run-test.sh
	+cd $* && bash run-test.sh $(SEEDOPT)
	+@echo "...passed tests in $*"

# makefile-./ is a dummy string, not a directory
.PHONY: makefile-tests
.SILENT: $(MK_TEST_DIRS:%=%/Makefile)
makefile-tests: $(MK_TEST_DIRS:%=makefile-./%)
prep: $(MK_TEST_DIRS:%=%/Makefile)
	@echo "All Makefiles generated."

.PHONY: force-create
# this target actually emits Makefile files
%/Makefile: force-create
	+@cd $* && python3 generate_mk.py

makefile-./%: %/Makefile
	@$(MAKE) -C $*
	@echo "...passed tests in $*"

vanilla-test: makefile-tests seed-tests
	@echo ""
	@echo "  Passed \"make vanilla-test\"."
ifeq ($(ENABLE_VERIFIC),1)
ifeq ($(YOSYS_NOVERIFIC),1)
	@echo "  Ran tests without verific support due to YOSYS_NOVERIFIC=1."
endif
endif
	@echo ""
	@$(MAKE) --no-print-directory summary

clean:
	@rm -rf ./asicworld/*.out ./asicworld/*.log
	@rm -rf ./hana/*.out ./hana/*.log
	@rm -rf ./simple/*.out ./simple/*.log
	@rm -rf ./memories/*.out ./memories/*.log ./memories/*.dmp
	@rm -rf ./sat/*.log ./techmap/*.log ./various/*.log
	@rm -rf ./bram/temp ./fsm/temp ./realmath/temp ./share/temp ./smv/temp ./various/temp
	@rm -f ./svinterfaces/*.log_stdout ./svinterfaces/*.log_stderr ./svinterfaces/dut_result.txt ./svinterfaces/reference_result.txt ./svinterfaces/a.out ./svinterfaces/*_syn.v ./svinterfaces/*.diff
	@rm -f  ./tools/cmp_tbdata
	@rm -f $(addsuffix /Makefile,$(MK_TEST_DIRS))
	@find . -name '*.result' -type f -exec rm -f {} +
