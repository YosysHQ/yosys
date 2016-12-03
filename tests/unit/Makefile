GTESTFLAG := -lgtest -lgtest_main

ALLTESTFILE := $(wildcard ./**/*Test.cc)
OBJTEST := objtest
BINTEST := bintest

# Prepare object list
OBJSWITHOUTMAIN := $(filter-out kernel/driver.o,$(OBJS))
FULLPATHOBJS := $(OBJSWITHOUTMAIN:%.o=$(ROOTPATH)/%.o)

all: prepare $(ALLTESTFILE:%Test.cc=%Test.o)

%Test.o: %Test.cc
	$(CXX) -o $(OBJTEST)/$(notdir $@) -c -I$(ROOTPATH) $(CPPFLAGS) $(CXXFLAGS) $<
	$(LD) -o $(BINTEST)/$(basename $(notdir $@)) $(LDFLAGS) $(FULLPATHOBJS) \
						$(LDLIBS) $(GTESTFLAG) -I$(ROOTPATH)

.PHONY: prepare run-tests clean

run-tests:
	$(CURDIR)/$(BINTEST)/*

prepare:
	mkdir -p $(OBJTEST)
	mkdir -p $(BINTEST)

clean:
	rm -rf $(OBJTEST)
	rm -rf $(BINTEST)
