Suppose you're making significant changes to a pass that should not change
the pass's output in any way. It might be useful to run a large number of
automatically generated tests to try to find bugs where the output has
changed. This document describes how to do that.

Basically we're going to use [AFL++](https://github.com/AFLplusplus/AFLplusplus) with the
[Grammar-Mutator](https://github.com/AFLplusplus/Grammar-Mutator) plugin to generate
RTLIL testcases. For each testcase, we run a Yosys script that applies both the old and new
implementation of the pass to the same design and compares the results. Testcase
generation is coverage-guided, i.e. the fuzzer will try to find testcases that exercise all
code in the old and new implementation of the pass (and in the RTLIL parser).

## Setup

These instructions clone tools into subdirectories of your home directory. They assume
you have a Yosys checkout under `$HOME/yosys`, and that you're testing the `opt_merge` pass.
They have been tested with AFL++ revision 68b492b2c7725816068718ef9437b72b40e67519 and Grammar-Mutator revision 05d8f537f8d656f0754e7ad5dcc653c42cb4f8ff.

Clone and build AFL++ and Grammar-Mutator:
```
cd $HOME
git clone https://github.com/AFLplusplus/AFLplusplus.git
git -C AFLplusplus checkout stable
git clone https://github.com/AFLplusplus/Grammar-Mutator.git
git -C Grammar-Mutator checkout stable
```

Check that `rtlil-fuzz-grammar.json` generates RTLIL constructs relevant to your pass.
Currently it's quite simple and generates a limited set of cells and wires; you may need to
extend it to generate different kinds of cells and other RTLIL constructs (e.g. `proc`).

Build AFL++ and Grammar-Mutator:
```
make -C $HOME/AFLplusplus -j all
make -C $HOME/Grammar-Mutator -j GRAMMAR_FILE=$HOME/yosys/tests/tools/rtlil-fuzz-grammar.json
```

Create a Yosys commit that adds the old version of your pass as a new command, e.g. copy
`opt_merge.cc` into `old_opt_merge.cc` and change the name of the command to `old_opt_merge`.
[Here's](https://github.com/YosysHQ/yosys/commit/827cd8c998f3e455b14ac990a3159030ddc19b21) an example.

You may also need to patch in [this commit](https://github.com/YosysHQ/yosys/commit/121c52f514c4ca282b4e6b3b14f71184f3849ddf) to work around a bug involving `std::reverse` on
empty vectors in the RTLIL parser when building with fuzzing instrumentation.
I think this is a clang++ bug so hopefully it will get fixed eventually and that patch will not be
necessary.

Rebuild Yosys with the AFL++ compiler wrapper. This assumes your config builds Yosys with clang++.
```
(cd $HOME/yosys; patch -lp1 << EOF)
diff --git a/Makefile b/Makefile
index 9c361294d..c9a98f74c 100644
--- a/Makefile
+++ b/Makefile
@@ -238,7 +238,7 @@
 LTOFLAGS := $(GCC_LTO)
 
 ifeq ($(CONFIG),clang)
-CXX = clang++
+CXX = $(HOME)/AFLplusplus/afl-c++
 CXXFLAGS += -std=$(CXXSTD) $(OPT_LEVEL)
 ifeq ($(ENABLE_LTO),1)
 LINKFLAGS += -fuse-ld=lld
EOF
make -C yosys clean && make -C yosys -j
```

You probably need to configure coredumps to work normally instead of going through some OS service:
```
echo core | sudo tee /proc/sys/kernel/core_pattern
```

## Running the fuzzer

Generate some initial testcases using Grammar-Mutator:
```
(cd $HOME/Grammar-Mutator; rm -rf seeds trees; ./grammar_generator-rtlil 100 1000 ./seeds ./trees)
```

Now run AFL++. 
```
(cd $HOME/Grammar-Mutator; \
  AFL_CUSTOM_MUTATOR_LIBRARY=./libgrammarmutator-rtlil.so \
  AFL_CUSTOM_MUTATOR_ONLY=1 \
  AFL_BENCH_UNTIL_CRASH=1 \
	YOSYS_WORK_UNITS_PER_THREAD=1 \
	YOSYS_ABORT_ON_LOG_ERROR=1 \
	$HOME/AFLplusplus/afl-fuzz -t 5000 -m none -i seeds -o out -- \
	$HOME/yosys/yosys -p 'read_rtlil -legalize @@; design -save init; old_opt_merge; design -save old; design -load init; opt_merge; design_equal old' \
)
```
This will run the fuzzer until the first crash (including any pass output mismatches) and then stop.
Or if you're lucky, the fuzzer will run indefinitely. This uses very little parallelism; if it doesn't find any errors right away, you can increase the test throughput by running AFL++ in parallel using the instructions [here](https://aflplus.plus/docs/parallel_fuzzing).

## Working with fuzz test failures

Any failing testcases will be dropped in `$HOME/Grammar-Mutator/out/default/crashes`.
Run `yosys -p 'read_rtlil -legalize ... ; dump'` to get the testcase as legalized RTLIL.

## Notes on generating semantically valid RTLIL

`Grammar-Mutator` generates RTLIL files according to the context-free grammar in `rtlil-fuzz-grammar.json`.
However, the testcases must also be semantically valid, e.g. references to wires should only refer to
wires that actually exist. These constraints cannot reasonably be expresed in a CFG. Therefore we
have added a `-legalize` option to the `read_rtlil` command. When `-legalize` is set, when `read_rtlil`
detects a failed semantic check, instead of erroring out it emits a warning and patches the incoming RTLIL
to make it valid.
