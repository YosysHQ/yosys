ENABLE_VERIFIC := 0
ENABLE_VERIFIC_SYSTEMVERILOG := 1
ENABLE_VERIFIC_VHDL := 1
ENABLE_VERIFIC_HIER_TREE := 1
ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS := 0
ENABLE_VERIFIC_EDIF := 0
ENABLE_VERIFIC_LIBERTY := 0
ENABLE_HELP_SOURCE := 0

# SANITIZER = address
# SANITIZER = memory
# SANITIZER = undefined
# SANITIZER = cfi

ifeq ($(ENABLE_HELP_SOURCE),1)
CXXFLAGS += -DYOSYS_ENABLE_HELP_SOURCE
endif

ifneq ($(SANITIZER),)
$(info [Clang Sanitizer] $(SANITIZER))
CXXFLAGS += -g -O1 -fno-omit-frame-pointer -fno-optimize-sibling-calls -fsanitize=$(SANITIZER)
LINKFLAGS += -g -fsanitize=$(SANITIZER)
ifneq ($(findstring memory,$(SANITIZER)),)
CXXFLAGS += -fPIE -fsanitize-memory-track-origins
LINKFLAGS += -fPIE -fsanitize-memory-track-origins
endif
ifneq ($(findstring cfi,$(SANITIZER)),)
CXXFLAGS += -flto
LINKFLAGS += -flto
LTOFLAGS =
endif
endif

LIBS_VERIFIC =
ifeq ($(ENABLE_VERIFIC),1)
VERIFIC_DIR ?= /usr/local/src/verific_lib
VERIFIC_COMPONENTS ?= database util containers
ifeq ($(ENABLE_VERIFIC_HIER_TREE),1)
VERIFIC_COMPONENTS += hier_tree
CXXFLAGS += -DVERIFIC_HIER_TREE_SUPPORT
else
ifneq ($(wildcard $(VERIFIC_DIR)/hier_tree),)
VERIFIC_COMPONENTS += hier_tree
endif
endif
ifeq ($(ENABLE_VERIFIC_SYSTEMVERILOG),1)
VERIFIC_COMPONENTS += verilog
CXXFLAGS += -DVERIFIC_SYSTEMVERILOG_SUPPORT
else
ifneq ($(wildcard $(VERIFIC_DIR)/verilog),)
VERIFIC_COMPONENTS += verilog
endif
endif
ifeq ($(ENABLE_VERIFIC_VHDL),1)
VERIFIC_COMPONENTS += vhdl
CXXFLAGS += -DVERIFIC_VHDL_SUPPORT
else
ifneq ($(wildcard $(VERIFIC_DIR)/vhdl),)
VERIFIC_COMPONENTS += vhdl
endif
endif
ifeq ($(ENABLE_VERIFIC_EDIF),1)
VERIFIC_COMPONENTS += edif
CXXFLAGS += -DVERIFIC_EDIF_SUPPORT
endif
ifeq ($(ENABLE_VERIFIC_LIBERTY),1)
VERIFIC_COMPONENTS += synlib
CXXFLAGS += -DVERIFIC_LIBERTY_SUPPORT
endif
ifeq ($(ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS),1)
VERIFIC_COMPONENTS += extensions
CXXFLAGS += -DYOSYSHQ_VERIFIC_EXTENSIONS
else
# YosysHQ flavor of Verific always needs extensions linked
# if disabled it will just not be invoked but parts
# are required for it to initialize properly
ifneq ($(wildcard $(VERIFIC_DIR)/extensions),)
VERIFIC_COMPONENTS += extensions
OBJS += kernel/log_compat.o
endif
endif
CXXFLAGS += $(patsubst %,-I$(VERIFIC_DIR)/%,$(VERIFIC_COMPONENTS)) -DYOSYS_ENABLE_VERIFIC
ifeq ($(OS), Darwin)
LIBS_VERIFIC += $(foreach comp,$(patsubst %,$(VERIFIC_DIR)/%/*-mac.a,$(VERIFIC_COMPONENTS)),-Wl,-force_load $(comp)) -lz
else
LIBS_VERIFIC += -Wl,--whole-archive $(patsubst %,$(VERIFIC_DIR)/%/*-linux.a,$(VERIFIC_COMPONENTS)) -Wl,--no-whole-archive -lz
endif
endif

ifeq ($(ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS),1)
OBJS += kernel/log_compat.o
endif

ifeq ($(ENABLE_VERIFIC),1)
include $(YOSYS_SRC)/frontends/verific/Makefile.inc
endif

ifeq ($(ENABLE_VERIFIC),1)
CXXFLAGS_NOVERIFIC = $(foreach v,$(CXXFLAGS),$(if $(findstring $(VERIFIC_DIR),$(v)),,$(v)))
LIBS_NOVERIFIC = $(foreach v,$(LIBS),$(if $(findstring $(VERIFIC_DIR),$(v)),,$(v)))
else
CXXFLAGS_NOVERIFIC = $(CXXFLAGS)
LIBS_NOVERIFIC = $(LIBS)
endif

.PHONY: check-git-abc

check-git-abc:
	@if [ ! -d "$(YOSYS_SRC)/abc" ] && git -C "$(YOSYS_SRC)" status >/dev/null 2>&1; then \
		echo "Error: The 'abc' directory does not exist."; \
		echo "Initialize the submodule: Run 'git submodule update --init' to set up 'abc' as a submodule."; \
		exit 1; \
	elif git -C "$(YOSYS_SRC)" submodule status abc 2>/dev/null | grep -q '^ '; then \
		exit 0; \
	elif [ -f "$(YOSYS_SRC)/abc/.gitcommit" ] && ! grep -q '\$$Format:%[hH]\$$' "$(YOSYS_SRC)/abc/.gitcommit"; then \
		echo "'abc' comes from a tarball. Continuing."; \
		exit 0; \
	elif git -C "$(YOSYS_SRC)" submodule status abc 2>/dev/null | grep -q '^+'; then \
		echo "'abc' submodule does not match expected commit."; \
		echo "Run 'git submodule update' to check out the correct version."; \
		echo "Note: If testing a different version of abc, call 'git commit abc' in the Yosys source directory to update the expected commit."; \
		exit 1; \
	elif git -C "$(YOSYS_SRC)" submodule status abc 2>/dev/null | grep -q '^U'; then \
		echo "'abc' submodule has merge conflicts."; \
		echo "Please resolve merge conflicts before continuing."; \
		exit 1; \
	elif [ -f "$(YOSYS_SRC)/abc/.gitcommit" ] && grep -q '\$$Format:%[hH]\$$' "$(YOSYS_SRC)/abc/.gitcommit"; then \
		echo "Error: 'abc' is not configured as a git submodule."; \
		echo "To resolve this:"; \
		echo "1. Back up your changes: Save any modifications from the 'abc' directory to another location."; \
		echo "2. Remove the existing 'abc' directory: Delete the 'abc' directory and all its contents."; \
		echo "3. Initialize the submodule: Run 'git submodule update --init' to set up 'abc' as a submodule."; \
		echo "4. Reapply your changes: Move your saved changes back to the 'abc' directory, if necessary."; \
		exit 1; \
	elif ! git -C "$(YOSYS_SRC)" status >/dev/null 2>&1; then \
		echo "$(realpath $(YOSYS_SRC)) is not configured as a git repository, and 'abc' folder is missing."; \
		echo "If you already have ABC, set 'ABCEXTERNAL' make variable to point to ABC executable."; \
		echo "Otherwise, download release archive 'yosys.tar.gz' from https://github.com/YosysHQ/yosys/releases."; \
		echo "    ('Source code' archive does not contain submodules.)"; \
		exit 1; \
	else \
		echo "Initialize the submodule: Run 'git submodule update --init' to set up 'abc' as a submodule."; \
		exit 1; \
	fi

.git-abc-submodule-hash: FORCE
	@new=$$(cd abc 2>/dev/null && git rev-parse HEAD 2>/dev/null || echo none); \
	old=$$(cat .git-abc-submodule-hash 2>/dev/null || echo none); \
	if [ "$$new" != "$$old" ]; then \
		echo "$$new" > .git-abc-submodule-hash; \
	fi

ifneq ($(SEED),)
SEEDOPT="-S $(SEED)"
endif

ifneq ($(ABCEXTERNAL),)
ABCOPT="-A $(ABCEXTERNAL)"
endif

test: vanilla-test unit-test

vanilla-test: $(TARGETS) $(EXTRA_TARGETS)
	@$(MAKE) -C tests vanilla-test \
	$(if $(ENABLE_VERIFIC),ENABLE_VERIFIC=$(ENABLE_VERIFIC)) \
	$(if $(YOSYS_NOVERIFIC),YOSYS_NOVERIFIC=$(YOSYS_NOVERIFIC)) \
	SEEDOPT=$(SEEDOPT) ABCOPT=$(ABCOPT)

VALGRIND ?= valgrind --error-exitcode=1 --leak-check=full --show-reachable=yes --errors-for-leak-kinds=all

vgtest: $(TARGETS) $(EXTRA_TARGETS)
	$(VALGRIND) ./yosys -p 'setattr -mod -unset top; synth' $$( ls tests/simple/*.v | grep -v repwhile.v )
	@echo ""
	@echo "  Passed \"make vgtest\"."
	@echo ""

vloghtb: $(TARGETS) $(EXTRA_TARGETS)
	+cd tests/vloghtb && bash run-test.sh
	@echo ""
	@echo "  Passed \"make vloghtb\"."
	@echo ""

ystests: $(TARGETS) $(EXTRA_TARGETS)
	rm -rf tests/ystests
	git clone https://github.com/YosysHQ/yosys-tests.git tests/ystests
	+$(MAKE) PATH="$$PWD:$$PATH" -C tests/ystests
	@echo ""
	@echo "  Finished \"make ystests\"."
	@echo ""

# Unit test

docs/source/generated/cmds.json: docs/source/generated $(TARGETS) $(EXTRA_TARGETS)
	$(Q) ./$(PROGRAM_PREFIX)yosys -p 'help -dump-cmds-json $@'

docs/source/generated/cells.json: docs/source/generated $(TARGETS) $(EXTRA_TARGETS)
	$(Q) ./$(PROGRAM_PREFIX)yosys -p 'help -dump-cells-json $@'

docs/source/generated/%.cc: backends/%.cc
	$(Q) mkdir -p $(@D)
	$(Q) cp $< $@

# diff returns exit code 1 if the files are different, but it's not an error
docs/source/generated/functional/rosette.diff: backends/functional/smtlib.cc backends/functional/smtlib_rosette.cc
	$(Q) mkdir -p $(@D)
	$(Q) diff -U 20 $^ > $@ || exit 0

PHONY: docs/gen/functional_ir
docs/gen/functional_ir: docs/source/generated/functional/smtlib.cc docs/source/generated/functional/rosette.diff

docs/source/generated/%.log: docs/source/generated $(TARGETS) $(EXTRA_TARGETS)
	$(Q) ./$(PROGRAM_PREFIX)yosys -qQT -h '$*' -l $@

docs/source/generated/chformal.cc: passes/cmds/chformal.cc docs/source/generated
	$(Q) cp $< $@

PHONY: docs/gen/chformal
docs/gen/chformal: docs/source/generated/chformal.log docs/source/generated/chformal.cc

PHONY: docs/gen docs/usage docs/reqs
docs/gen: $(TARGETS)
	$(Q) $(MAKE) -C docs gen

docs/source/generated:
	$(Q) mkdir -p docs/source/generated

# some commands return an error and print the usage text to stderr
define DOC_USAGE_STDERR
docs/source/generated/$(1): $(TARGETS) docs/source/generated FORCE
	-$(Q) ./$(PROGRAM_PREFIX)$(1) --help 2> $$@
endef
DOCS_USAGE_STDERR := yosys-filterlib

# The in-tree ABC (yosys-abc) is only built when ABCEXTERNAL is not set.
ifeq ($(ABCEXTERNAL),)
DOCS_USAGE_STDERR += yosys-abc
endif

$(foreach usage,$(DOCS_USAGE_STDERR),$(eval $(call DOC_USAGE_STDERR,$(usage))))

# others print to stdout
define DOC_USAGE_STDOUT
docs/source/generated/$(1): $(TARGETS) docs/source/generated
	$(Q) ./$(PROGRAM_PREFIX)$(1) --help > $$@ || rm $$@
endef
DOCS_USAGE_STDOUT := yosys yosys-smtbmc yosys-witness yosys-config
$(foreach usage,$(DOCS_USAGE_STDOUT),$(eval $(call DOC_USAGE_STDOUT,$(usage))))

docs/usage: $(addprefix docs/source/generated/,$(DOCS_USAGE_STDOUT) $(DOCS_USAGE_STDERR))

docs/reqs:
	$(Q) $(MAKE) -C docs reqs

.PHONY: docs/prep
docs/prep: docs/source/generated/cells.json docs/source/generated/cmds.json docs/gen docs/usage docs/gen/functional_ir docs/gen/chformal

DOC_TARGET ?= html
docs: docs/prep
	$(Q) $(MAKE) -C docs $(DOC_TARGET)

coverage:
	./$(PROGRAM_PREFIX)yosys -qp 'help; help -all'
	rm -rf coverage.info coverage_html
	lcov --capture -d . --no-external -o coverage.info
	genhtml coverage.info --output-directory coverage_html

clean_coverage:
	find . -name "*.gcda" -type f -delete

FUNC_KERNEL := functional.cc functional.h sexpr.cc sexpr.h compute_graph.h
FUNC_INCLUDES := $(addprefix --include *,functional/* $(FUNC_KERNEL))
coverage_functional:
	rm -rf coverage.info coverage_html
	lcov --capture -d backends/functional -d kernel $(FUNC_INCLUDES) --no-external -o coverage.info
	genhtml coverage.info --output-directory coverage_html
