
TESTS = $(sort $(basename $(wildcard *.sv)) $(basename $(wildcard *.vhd)))

all: $(addsuffix .ok,$(TESTS))

%.ok:
	bash runtest.sh $@

clean:
	rm -rf $(addsuffix .ok,$(TESTS)) $(addsuffix .sby,$(TESTS)) $(TESTS)
	rm -rf $(addsuffix _pass.sby,$(TESTS)) $(addsuffix _pass,$(TESTS))
	rm -rf $(addsuffix _fail.sby,$(TESTS)) $(addsuffix _fail,$(TESTS))

