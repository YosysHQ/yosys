UNAME_S := $(shell uname -s)

# GoogleTest flags
GTEST_PREFIX := $(shell brew --prefix googletest 2>/dev/null)
ifeq ($(GTEST_PREFIX),)
  GTEST_CXXFLAGS :=
  GTEST_LDFLAGS := -lgtest -lgtest_main
else
  GTEST_CXXFLAGS := -I$(GTEST_PREFIX)/include
  GTEST_LDFLAGS := -L$(GTEST_PREFIX)/lib -lgtest -lgtest_main
endif

ifeq ($(UNAME_S),Darwin)
  RPATH = -Wl,-rpath,$(ROOTPATH)
else
  RPATH = -Wl,-rpath=$(ROOTPATH)
endif

EXTRAFLAGS := -lyosys -pthread

MAKEFILE_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
OBJTEST := $(MAKEFILE_DIR)objtest
BINTEST := $(MAKEFILE_DIR)bintest

ALLTESTFILE := $(shell cd $(MAKEFILE_DIR) && find . -name '*Test.cc' | sed 's|^\./||' | tr '\n' ' ')
TESTDIRS := $(sort $(dir $(ALLTESTFILE)))
TESTS := $(addprefix $(BINTEST)/, $(basename $(ALLTESTFILE:%Test.cc=%Test.o)))

# Prevent make from removing our .o files
.SECONDARY:

all: prepare $(TESTS) run-tests

$(BINTEST)/%: $(OBJTEST)/%.o | prepare
	$(CXX) -L$(ROOTPATH) $(RPATH) $(LINKFLAGS) -o $@ $^ $(LIBS) \
		$(GTEST_LDFLAGS) $(EXTRAFLAGS)

$(OBJTEST)/%.o: $(MAKEFILE_DIR)/%.cc | prepare
	$(CXX) -o $@ -c -I$(ROOTPATH) $(CPPFLAGS) $(CXXFLAGS) $(GTEST_CXXFLAGS) $^

.PHONY: prepare run-tests clean

run-tests: $(TESTS)
ifeq ($(UNAME_S),Darwin)
	@for t in $^; do \
		echo "Running $$t"; \
		DYLD_LIBRARY_PATH=$(ROOTPATH) $$t || exit 1; \
	done
else
	@for t in $^; do \
		echo "Running $$t"; \
		$$t || exit 1; \
	done
endif

prepare:
	mkdir -p $(addprefix $(BINTEST)/,$(TESTDIRS))
	mkdir -p $(addprefix $(OBJTEST)/,$(TESTDIRS))

clean:
	rm -rf $(OBJTEST)
	rm -rf $(BINTEST)
