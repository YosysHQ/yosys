
TESTS = $(basename $(wildcard *.sv))

all: $(addsuffix .ok,$(TESTS))

%.ok: %.sv
	bash runtest.sh $<

clean:
	rm -rf $(addsuffix .ok,$(TESTS))
	rm -rf $(addsuffix _pass.sby,$(TESTS)) $(addsuffix _pass,$(TESTS))
	rm -rf $(addsuffix _fail.sby,$(TESTS)) $(addsuffix _fail,$(TESTS))

