GTESTFLAG := -lgtest -lgtest_main
RPATH := -Wl,-rpath
EXTRAFLAGS := -lyosys

ALLTESTFILE := $(wildcard ./**/*Test.cc)
OBJTEST := objtest
BINTEST := bintest

all: prepare $(ALLTESTFILE:%Test.cc=%Test.o)

%Test.o: %Test.cc
	$(CXX) -o $(OBJTEST)/$(notdir $@) -c -I$(ROOTPATH) $(CPPFLAGS) $(CXXFLAGS) $<
	$(CXX) -L$(ROOTPATH) $(RPATH)=$(ROOTPATH) -o \
		$(BINTEST)/$(basename $(notdir $@)) $(OBJTEST)/$(notdir $@) $(LDLIBS) \
		$(GTESTFLAG) $(EXTRAFLAGS)
	
.PHONY: prepare run-tests clean

run-tests:
	$(CURDIR)/$(BINTEST)/*

prepare:
	mkdir -p $(OBJTEST)
	mkdir -p $(BINTEST)

clean:
	rm -rf $(OBJTEST)
	rm -rf $(BINTEST)
