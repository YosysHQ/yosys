GTESTFLAG := -lgtest -lgtest_main
RPATH := -Wl,-rpath
EXTRAFLAGS := -lyosys -pthreads

OBJTEST := objtest
BINTEST := bintest

ALLTESTFILE := $(shell find -name '*Test.cc' -printf '%P ')
TESTDIRS := $(sort $(dir $(ALLTESTFILE)))
TESTS := $(addprefix $(BINTEST)/, $(basename $(ALLTESTFILE:%Test.cc=%Test.o)))

# Prevent make from removing our .o files
.SECONDARY:

all: prepare $(TESTS) run-tests

$(BINTEST)/%: $(OBJTEST)/%.o
	$(CXX) -L$(ROOTPATH) $(RPATH)=$(ROOTPATH) -o $@ $^ $(LDLIBS) \
		$(GTESTFLAG) $(EXTRAFLAGS)

$(OBJTEST)/%.o: $(basename $(subst $(OBJTEST),.,%)).cc
	$(CXX) -o $@ -c -I$(ROOTPATH) $(CPPFLAGS) $(CXXFLAGS) $^

.PHONY: prepare run-tests clean

run-tests: $(TESTS)
	$(subst Test ,Test; ,$^)

prepare:
	mkdir -p $(addprefix $(BINTEST)/,$(TESTDIRS))
	mkdir -p $(addprefix $(OBJTEST)/,$(TESTDIRS))

clean:
	rm -rf $(OBJTEST)
	rm -rf $(BINTEST)
