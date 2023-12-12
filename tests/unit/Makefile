GTESTFLAG := -lgtest -lgtest_main
RPATH := -Wl,-rpath
EXTRAFLAGS := -lyosys -pthread

OBJTEST := objtest
BINTEST := bintest

ALLTESTFILE := $(shell find -name '*Test.cc' -printf '%P ')
TESTDIRS := $(sort $(dir $(ALLTESTFILE)))
TESTS := $(addprefix $(BINTEST)/, $(basename $(ALLTESTFILE:%Test.cc=%Test.o)))

# Prevent make from removing our .o files
.SECONDARY:

all: prepare $(TESTS) run-tests

$(BINTEST)/%: $(OBJTEST)/%.o
	$(CXX) $(RPATH)=$(ROOTPATH) -L$(ROOTPATH) -o $@ $^ $(LDLIBS) \
		$(GTESTFLAG) $(EXTRAFLAGS)
	patchelf --replace-needed $(YOSYSLIBDIR)/libyosys.so libyosys.so $@

$(OBJTEST)/%.o: $(basename $(subst $(OBJTEST),.,%)).cc
	$(CXX) -o $@ -c -I$(ROOTPATH) -I$(ROOTPATH)/backends/cxxrtl/runtime $(CPPFLAGS) $(CXXFLAGS) $^

.PHONY: prepare run-tests clean

run-tests: $(TESTS)
	$(subst Test ,Test; ,$^)

prepare:
	mkdir -p $(addprefix $(BINTEST)/,$(TESTDIRS))
	mkdir -p $(addprefix $(OBJTEST)/,$(TESTDIRS))

clean:
	rm -rf $(OBJTEST)
	rm -rf $(BINTEST)
