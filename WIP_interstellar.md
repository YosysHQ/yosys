## why?

- no way to build a proper STATIC lib (= .a) with the current Makefile
    - "config-gcc-static" FAIL, and in any case it is not a static build
- the generated libyosys.so has a wrong SONAME(= $(LIBDIR)/libyosys.so) when it SHOULD be libyosys.so
 which makes it hard to properly package libyosys (without resorting to patchelf)
- a Makefile is NOT made to handle dependencies; that is what autoconf is for
- configure the Makefile requires generating a file on disk (Makefile.conf) which is less than ideal when
integrating with CMake downstream projects

## all Makefiles

```
find . -type f -name "*Makefile*"

./frontends/verific/Makefile.inc
./frontends/ast/Makefile.inc
./frontends/liberty/Makefile.inc
./frontends/aiger/Makefile.inc
./frontends/json/Makefile.inc
./frontends/rpc/Makefile.inc
./frontends/verilog/Makefile.inc
./frontends/rtlil/Makefile.inc
./frontends/blif/Makefile.inc
./backends/smt2/Makefile.inc
./backends/intersynth/Makefile.inc
./backends/cxxrtl/Makefile.inc
./backends/aiger/Makefile.inc
./backends/firrtl/Makefile.inc
./backends/edif/Makefile.inc
./backends/btor/Makefile.inc
./backends/json/Makefile.inc
./backends/smv/Makefile.inc
./backends/spice/Makefile.inc
./backends/simplec/Makefile.inc
./backends/protobuf/Makefile.inc
./backends/verilog/Makefile.inc
./backends/rtlil/Makefile.inc
./backends/table/Makefile.inc
./backends/blif/Makefile.inc
./tests/unit/Makefile
./tests/sva/Makefile
./libs/subcircuit/Makefile
./libs/ezsat/Makefile
./libs/bigint/Makefile
./manual/PRESENTATION_Prog/Makefile
./manual/PRESENTATION_ExOth/Makefile
./manual/PRESENTATION_ExSyn/Makefile
./manual/PRESENTATION_Intro/Makefile
./manual/PRESENTATION_ExAdv/Makefile
./manual/CHAPTER_Prog/Makefile
./examples/smtbmc/Makefile
./examples/osu035/Makefile
./passes/memory/Makefile.inc
./passes/equiv/Makefile.inc
./passes/tests/Makefile.inc
./passes/opt/Makefile.inc
./passes/pmgen/Makefile.inc
./passes/sat/Makefile.inc
./passes/fsm/Makefile.inc
./passes/hierarchy/Makefile.inc
./passes/cmds/Makefile.inc
./passes/techmap/Makefile.inc
./passes/proc/Makefile.inc
./techlibs/coolrunner2/Makefile.inc
./techlibs/ice40/Makefile.inc
./techlibs/anlogic/Makefile.inc
./techlibs/gowin/Makefile.inc
./techlibs/easic/Makefile.inc
./techlibs/intel_alm/Makefile.inc
./techlibs/gatemate/Makefile.inc
./techlibs/sf2/Makefile.inc
./techlibs/nexus/Makefile.inc
./techlibs/efinix/Makefile.inc
./techlibs/xilinx/Makefile.inc
./techlibs/quicklogic/Makefile.inc
./techlibs/common/Makefile.inc
./techlibs/greenpak4/Makefile.inc
./techlibs/machxo2/Makefile.inc
./techlibs/intel/Makefile.inc
./techlibs/achronix/Makefile.inc
./techlibs/ecp5/Makefile.inc
./Makefile
```

## all sources

- fresh clone:
```
find . -type f -name "*.cpp" -o -name "*.c" -o -name "*.cc"
./frontends/verific/verific.cc
./frontends/verific/verificsva.cc
./frontends/ast/ast.cc
./frontends/ast/genrtlil.cc
./frontends/ast/simplify.cc
./frontends/ast/dpicall.cc
./frontends/ast/ast_binding.cc
./frontends/liberty/liberty.cc
./frontends/aiger/aigerparse.cc
./frontends/json/jsonparse.cc
./frontends/rpc/rpc_frontend.cc
./frontends/verilog/verilog_frontend.cc
./frontends/verilog/preproc.cc
./frontends/verilog/const2ast.cc
./frontends/rtlil/rtlil_frontend.cc
./frontends/blif/blifparse.cc
./backends/smt2/smt2.cc
./backends/intersynth/intersynth.cc
./backends/cxxrtl/cxxrtl_backend.cc
./backends/cxxrtl/cxxrtl_capi.cc
./backends/cxxrtl/cxxrtl_vcd_capi.cc
./backends/aiger/aiger.cc
./backends/aiger/xaiger.cc
./backends/firrtl/firrtl.cc
./backends/edif/edif.cc
./backends/btor/btor.cc
./backends/json/json.cc
./backends/smv/smv.cc
./backends/spice/spice.cc
./backends/simplec/test00_tb.c
./backends/simplec/simplec.cc
./backends/protobuf/protobuf.cc
./backends/verilog/verilog_backend.cc
./backends/rtlil/rtlil_backend.cc
./backends/table/table.cc
./backends/blif/blif.cc
./tests/various/plugin.cc
./tests/unit/kernel/rtlilTest.cc
./tests/unit/kernel/logTest.cc
./tests/tools/cmp_tbdata.c
./libs/minisat/SimpSolver.cc
./libs/minisat/Options.cc
./libs/minisat/System.cc
./libs/minisat/Solver.cc
./libs/json11/json11.cpp
./libs/sha1/sha1.cpp
./libs/subcircuit/scshell.cc
./libs/subcircuit/subcircuit.cc
./libs/subcircuit/demo.cc
./libs/ezsat/testbench.cc
./libs/ezsat/ezsat.cc
./libs/ezsat/demo_cmp.cc
./libs/ezsat/ezminisat.cc
./libs/ezsat/puzzle3d.cc
./libs/ezsat/demo_bit.cc
./libs/ezsat/demo_vec.cc
./libs/fst/fastlz.cc
./libs/fst/lz4.cc
./libs/fst/fstapi.cc
./libs/bigint/BigUnsignedInABase.cc
./libs/bigint/sample.cc
./libs/bigint/testsuite.cc
./libs/bigint/BigIntegerAlgorithms.cc
./libs/bigint/BigIntegerUtils.cc
./libs/bigint/BigUnsigned.cc
./libs/bigint/BigInteger.cc
./manual/PRESENTATION_Prog/my_cmd.cc
./manual/CHAPTER_StateOfTheArt/cmp_tbdata.c
./manual/CHAPTER_Prog/stubnets.cc
./examples/cxx-api/demomain.cc
./examples/cxx-api/evaldemo.cc
./passes/memory/memory_dff.cc
./passes/memory/memory_map.cc
./passes/memory/memory_narrow.cc
./passes/memory/memory_unpack.cc
./passes/memory/memory_share.cc
./passes/memory/memory.cc
./passes/memory/memory_memx.cc
./passes/memory/memory_nordff.cc
./passes/memory/memory_collect.cc
./passes/memory/memory_bram.cc
./passes/equiv/equiv_remove.cc
./passes/equiv/equiv_make.cc
./passes/equiv/equiv_struct.cc
./passes/equiv/equiv_purge.cc
./passes/equiv/equiv_miter.cc
./passes/equiv/equiv_mark.cc
./passes/equiv/equiv_induct.cc
./passes/equiv/equiv_simple.cc
./passes/equiv/equiv_opt.cc
./passes/equiv/equiv_status.cc
./passes/equiv/equiv_add.cc
./passes/tests/test_abcloop.cc
./passes/tests/test_autotb.cc
./passes/tests/test_cell.cc
./passes/opt/opt_mem_widen.cc
./passes/opt/pmux2shiftx.cc
./passes/opt/opt_demorgan.cc
./passes/opt/opt.cc
./passes/opt/opt_lut_ins.cc
./passes/opt/share.cc
./passes/opt/opt_reduce.cc
./passes/opt/wreduce.cc
./passes/opt/muxpack.cc
./passes/opt/opt_lut.cc
./passes/opt/opt_merge.cc
./passes/opt/opt_muxtree.cc
./passes/opt/opt_expr.cc
./passes/opt/opt_mem_priority.cc
./passes/opt/opt_dff.cc
./passes/opt/opt_mem.cc
./passes/opt/opt_share.cc
./passes/opt/opt_mem_feedback.cc
./passes/opt/opt_clean.cc
./passes/opt/rmports.cc
./passes/pmgen/test_pmgen.cc
./passes/pmgen/peepopt.cc
./passes/pmgen/xilinx_srl.cc
./passes/pmgen/xilinx_dsp.cc
./passes/pmgen/ice40_wrapcarry.cc
./passes/pmgen/ice40_dsp.cc
./passes/sat/mutate.cc
./passes/sat/qbfsat.cc
./passes/sat/assertpmux.cc
./passes/sat/async2sync.cc
./passes/sat/fminit.cc
./passes/sat/fmcombine.cc
./passes/sat/sat.cc
./passes/sat/eval.cc
./passes/sat/expose.cc
./passes/sat/cutpoint.cc
./passes/sat/clk2fflogic.cc
./passes/sat/miter.cc
./passes/sat/freduce.cc
./passes/sat/supercover.cc
./passes/sat/sim.cc
./passes/fsm/fsm_info.cc
./passes/fsm/fsm_expand.cc
./passes/fsm/fsm.cc
./passes/fsm/fsm_opt.cc
./passes/fsm/fsm_detect.cc
./passes/fsm/fsm_map.cc
./passes/fsm/fsm_extract.cc
./passes/fsm/fsm_export.cc
./passes/fsm/fsm_recode.cc
./passes/hierarchy/hierarchy.cc
./passes/hierarchy/submod.cc
./passes/hierarchy/uniquify.cc
./passes/cmds/copy.cc
./passes/cmds/connect.cc
./passes/cmds/add.cc
./passes/cmds/delete.cc
./passes/cmds/chformal.cc
./passes/cmds/edgetypes.cc
./passes/cmds/ltp.cc
./passes/cmds/rename.cc
./passes/cmds/chtype.cc
./passes/cmds/logcmd.cc
./passes/cmds/plugin.cc
./passes/cmds/setattr.cc
./passes/cmds/blackbox.cc
./passes/cmds/trace.cc
./passes/cmds/scc.cc
./passes/cmds/check.cc
./passes/cmds/portlist.cc
./passes/cmds/design.cc
./passes/cmds/bugpoint.cc
./passes/cmds/qwp.cc
./passes/cmds/write_file.cc
./passes/cmds/stat.cc
./passes/cmds/glift.cc
./passes/cmds/scratchpad.cc
./passes/cmds/torder.cc
./passes/cmds/cover.cc
./passes/cmds/logger.cc
./passes/cmds/splitnets.cc
./passes/cmds/show.cc
./passes/cmds/scatter.cc
./passes/cmds/tee.cc
./passes/cmds/sta.cc
./passes/cmds/splice.cc
./passes/cmds/autoname.cc
./passes/cmds/printattrs.cc
./passes/cmds/select.cc
./passes/cmds/exec.cc
./passes/cmds/setundef.cc
./passes/cmds/clean_zerowidth.cc
./passes/cmds/connwrappers.cc
./passes/techmap/shregmap.cc
./passes/techmap/zinit.cc
./passes/techmap/bmuxmap.cc
./passes/techmap/muxcover.cc
./passes/techmap/extractinv.cc
./passes/techmap/pmuxtree.cc
./passes/techmap/lut2mux.cc
./passes/techmap/dfflibmap.cc
./passes/techmap/abc9_ops.cc
./passes/techmap/filterlib.cc
./passes/techmap/clkbufmap.cc
./passes/techmap/flowmap.cc
./passes/techmap/libparse.cc
./passes/techmap/abc9_exe.cc
./passes/techmap/dffinit.cc
./passes/techmap/tribuf.cc
./passes/techmap/maccmap.cc
./passes/techmap/aigmap.cc
./passes/techmap/iopadmap.cc
./passes/techmap/extract_reduce.cc
./passes/techmap/attrmvcp.cc
./passes/techmap/nlutmap.cc
./passes/techmap/dfflegalize.cc
./passes/techmap/attrmap.cc
./passes/techmap/alumacc.cc
./passes/techmap/abc9.cc
./passes/techmap/deminout.cc
./passes/techmap/flatten.cc
./passes/techmap/dffunmap.cc
./passes/techmap/simplemap.cc
./passes/techmap/demuxmap.cc
./passes/techmap/extract_counter.cc
./passes/techmap/insbuf.cc
./passes/techmap/hilomap.cc
./passes/techmap/techmap.cc
./passes/techmap/abc.cc
./passes/techmap/extract_fa.cc
./passes/techmap/extract.cc
./passes/proc/proc_dff.cc
./passes/proc/proc_prune.cc
./passes/proc/proc_init.cc
./passes/proc/proc_clean.cc
./passes/proc/proc_mux.cc
./passes/proc/proc_memwr.cc
./passes/proc/proc_arst.cc
./passes/proc/proc_rmdead.cc
./passes/proc/proc.cc
./passes/proc/proc_dlatch.cc
./techlibs/coolrunner2/synth_coolrunner2.cc
./techlibs/coolrunner2/coolrunner2_fixup.cc
./techlibs/coolrunner2/coolrunner2_sop.cc
./techlibs/ice40/ice40_braminit.cc
./techlibs/ice40/ice40_opt.cc
./techlibs/ice40/synth_ice40.cc
./techlibs/anlogic/anlogic_eqn.cc
./techlibs/anlogic/synth_anlogic.cc
./techlibs/anlogic/anlogic_fixcarry.cc
./techlibs/gowin/synth_gowin.cc
./techlibs/easic/synth_easic.cc
./techlibs/intel_alm/synth_intel_alm.cc
./techlibs/gatemate/synth_gatemate.cc
./techlibs/sf2/synth_sf2.cc
./techlibs/nexus/synth_nexus.cc
./techlibs/efinix/synth_efinix.cc
./techlibs/efinix/efinix_fixcarry.cc
./techlibs/xilinx/synth_xilinx.cc
./techlibs/xilinx/xilinx_dffopt.cc
./techlibs/quicklogic/synth_quicklogic.cc
./techlibs/common/synth.cc
./techlibs/common/prep.cc
./techlibs/greenpak4/synth_greenpak4.cc
./techlibs/greenpak4/greenpak4_dffinv.cc
./techlibs/machxo2/synth_machxo2.cc
./techlibs/intel/synth_intel.cc
./techlibs/achronix/synth_achronix.cc
./techlibs/ecp5/synth_ecp5.cc
./techlibs/ecp5/ecp5_gsr.cc
./kernel/rtlil.cc
./kernel/cellaigs.cc
./kernel/log.cc
./kernel/celledges.cc
./kernel/driver.cc
./kernel/ff.cc
./kernel/binding.cc
./kernel/mem.cc
./kernel/fstdata.cc
./kernel/calc.cc
./kernel/satgen.cc
./kernel/yosys.cc
./kernel/ffmerge.cc
./kernel/qcsat.cc
./kernel/register.cc
./misc/launcher.c
```
- `echo -e "ENABLE_LIBYOSYS := 1\nENABLE_ABC := 0" > Makefile.conf`
- make -j16
- added: `find . -type f -name "*.cpp" -o -name "*.c" -o -name "*.cc"`
```
./frontends/verilog/verilog_parser.tab.cc
./frontends/verilog/verilog_lexer.cc
./frontends/rtlil/rtlil_lexer.cc
./frontends/rtlil/rtlil_parser.tab.cc
./share/include/backends/cxxrtl/cxxrtl_capi.cc
./share/include/backends/cxxrtl/cxxrtl_vcd_capi.cc
./kernel/version_07a43689d.cc
```
- CHECK with: `git clean -xdf -n | grep -v '\.o$' | grep -v '\.d$' | grep -v '\.mk$' | grep -v '\.vh$'`
```
# TODO what are .vh?

# Would remove .history/
# Would remove Makefile.conf
Would remove frontends/rtlil/rtlil_lexer.cc
Would remove frontends/rtlil/rtlil_parser.output
Would remove frontends/rtlil/rtlil_parser.tab.cc
Would remove frontends/rtlil/rtlil_parser.tab.hh
Would remove frontends/verilog/verilog_lexer.cc
Would remove frontends/verilog/verilog_parser.output
Would remove frontends/verilog/verilog_parser.tab.cc
Would remove frontends/verilog/verilog_parser.tab.hh
Would remove kernel/version_f32216e56.cc
# Would remove libyosys.so
Would remove passes/pmgen/ice40_dsp_pm.h
Would remove passes/pmgen/ice40_wrapcarry_pm.h
Would remove passes/pmgen/peepopt_pm.h
Would remove passes/pmgen/test_pmgen_pm.h
Would remove passes/pmgen/xilinx_dsp48a_pm.h
Would remove passes/pmgen/xilinx_dsp_CREG_pm.h
Would remove passes/pmgen/xilinx_dsp_cascade_pm.h
Would remove passes/pmgen/xilinx_dsp_pm.h
Would remove passes/pmgen/xilinx_srl_pm.h
Would remove share/
Would remove techlibs/common/simcells_help.inc
Would remove techlibs/common/simlib_help.inc
# Would remove yosys
# Would remove yosys-config
# Would remove yosys-filterlib
# Would remove yosys-smtbmc
```
