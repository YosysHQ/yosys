################################################################################
cmake_minimum_required(VERSION 3.22)

project(yosys)

################################################################################

# TODO add the various exe
# TODO add tests
# TODO add STATIC specific test (move to separate branch)

# Usuful only when dev/debug yosys-related code
option(YOSYS_ENABLE_DEBUG "ENABLE_DEBUG for Yosys Makefile" OFF)

option(YOSYS_ENABLE_TESTING "ENABLE_DEBUG for Yosys Makefile" OFF)
option(YOSYS_BUILD_SHARED_LIBS "Yosys BUILD_SHARED_LIBS" ON)

if(YOSYS_BUILD_SHARED_LIBS)
set(BUILD_SHARED_LIBS ON)
endif()

################################################################################

# TODO all the find SHOULD depend on the corresponding option

# find_program(MAKE_EXE make)
# if(NOT MAKE_EXE)
# message(FATAL_ERROR "make not found(abc prereq)")
# endif()

find_program(BISON bison)
if(NOT BISON)
    message(FATAL_ERROR "bison not found!")
endif()

find_program(FLEX flex)
if(NOT FLEX)
    message(FATAL_ERROR "flex not found!")
endif()

find_program(PYTHON3_EXE python3)
if(NOT PYTHON3_EXE)
    message(FATAL_ERROR "python3 not found!")
endif()

# Could alternatively compile without ENABLE_TCL
find_package(TCL REQUIRED)

# Could alternatively compile without ENABLE_READLINE
find_path(READLINE_INCLUDE_PATH NAMES readline/readline.h)
find_library(READLINE_LIBRARY NAMES readline)
if(NOT READLINE_INCLUDE_PATH)
    message(FATAL_ERROR "readline not found!(apt install libreadline-dev)")
endif()

# Could alternatively compile without ENABLE_ZLIB
find_package(ZLIB REQUIRED)

# TODO? if yes cf ENABLE_PLUGINS below
# include(FindFFI.cmake)
# if(NOT FFI_FOUND)
#     message(FATAL_ERROR "libffi!(apt install libffi-dev)")
# endif()


################################################################################
# Current version is using a custom CMake that compiles 99% of Yosys.
# It could be made to compile only what is needed, or go to 100% and make a PR in YosysHQ?
# (but they are not really interested in CMake)
# IMPORTANT: when STATIC linking "yosys"(= add_library name) you MUST use --whole-archive!
# cf https://stackoverflow.com/a/842770/5312991
# and https://www.cppstories.com/2018/02/static-vars-static-lib/#the-reason

# - cd yosys_ext-prefix/src/yosys_ext-build
# - make -f ~/..../_deps/yosys_dl-src/Makefile clean
# - make -f ~/..../_deps/yosys_dl-src/Makefile --just-print libyosys.so | grep ".*yosys_dl-src.*.cc$" | awk '{print $NF}'
set(YOSYS_SRCS
${PROJECT_BINARY_DIR}/kernel/version.cc
${PROJECT_SOURCE_DIR}/kernel/register.cc
${PROJECT_SOURCE_DIR}/kernel/rtlil.cc
${PROJECT_SOURCE_DIR}/kernel/log.cc
${PROJECT_SOURCE_DIR}/kernel/calc.cc
${PROJECT_SOURCE_DIR}/kernel/yosys.cc
${PROJECT_SOURCE_DIR}/kernel/binding.cc
${PROJECT_SOURCE_DIR}/kernel/cellaigs.cc
${PROJECT_SOURCE_DIR}/kernel/celledges.cc
${PROJECT_SOURCE_DIR}/kernel/satgen.cc
${PROJECT_SOURCE_DIR}/kernel/qcsat.cc
${PROJECT_SOURCE_DIR}/kernel/mem.cc
${PROJECT_SOURCE_DIR}/kernel/ffmerge.cc
${PROJECT_SOURCE_DIR}/kernel/ff.cc
${PROJECT_SOURCE_DIR}/kernel/fstdata.cc
${PROJECT_SOURCE_DIR}/libs/bigint/BigIntegerAlgorithms.cc
${PROJECT_SOURCE_DIR}/libs/bigint/BigInteger.cc
${PROJECT_SOURCE_DIR}/libs/bigint/BigIntegerUtils.cc
${PROJECT_SOURCE_DIR}/libs/bigint/BigUnsigned.cc
${PROJECT_SOURCE_DIR}/libs/bigint/BigUnsignedInABase.cc
${PROJECT_SOURCE_DIR}/libs/subcircuit/subcircuit.cc
${PROJECT_SOURCE_DIR}/libs/ezsat/ezsat.cc
${PROJECT_SOURCE_DIR}/libs/ezsat/ezminisat.cc
${PROJECT_SOURCE_DIR}/libs/minisat/Options.cc
${PROJECT_SOURCE_DIR}/libs/minisat/SimpSolver.cc
${PROJECT_SOURCE_DIR}/libs/minisat/Solver.cc
${PROJECT_SOURCE_DIR}/libs/minisat/System.cc
${PROJECT_SOURCE_DIR}/libs/fst/fstapi.cc
${PROJECT_SOURCE_DIR}/libs/fst/fastlz.cc
${PROJECT_SOURCE_DIR}/libs/fst/lz4.cc
${PROJECT_SOURCE_DIR}/frontends/aiger/aigerparse.cc
${PROJECT_SOURCE_DIR}/frontends/rpc/rpc_frontend.cc
${PROJECT_SOURCE_DIR}/frontends/verific/verific.cc
${PROJECT_SOURCE_DIR}/frontends/json/jsonparse.cc

${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.cc
${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.hh
${PROJECT_BINARY_DIR}/frontends/verilog/verilog_lexer.cc

${PROJECT_SOURCE_DIR}/frontends/verilog/preproc.cc
${PROJECT_SOURCE_DIR}/frontends/verilog/verilog_frontend.cc
${PROJECT_SOURCE_DIR}/frontends/verilog/const2ast.cc
${PROJECT_SOURCE_DIR}/frontends/ast/ast.cc
${PROJECT_SOURCE_DIR}/frontends/ast/simplify.cc
${PROJECT_SOURCE_DIR}/frontends/ast/genrtlil.cc
${PROJECT_SOURCE_DIR}/frontends/ast/dpicall.cc
${PROJECT_SOURCE_DIR}/frontends/ast/ast_binding.cc
${PROJECT_SOURCE_DIR}/frontends/blif/blifparse.cc
${PROJECT_SOURCE_DIR}/frontends/liberty/liberty.cc

${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.cc
${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.hh
${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_lexer.cc

${PROJECT_SOURCE_DIR}/frontends/rtlil/rtlil_frontend.cc
# ${PROJECT_SOURCE_DIR}/passes/tests/test_autotb.cc
# ${PROJECT_SOURCE_DIR}/passes/tests/test_cell.cc
# ${PROJECT_SOURCE_DIR}/passes/tests/test_abcloop.cc
${PROJECT_SOURCE_DIR}/passes/sat/sat.cc
${PROJECT_SOURCE_DIR}/passes/sat/freduce.cc
${PROJECT_SOURCE_DIR}/passes/sat/eval.cc
${PROJECT_SOURCE_DIR}/passes/sat/sim.cc
${PROJECT_SOURCE_DIR}/passes/sat/miter.cc
${PROJECT_SOURCE_DIR}/passes/sat/expose.cc
${PROJECT_SOURCE_DIR}/passes/sat/assertpmux.cc
${PROJECT_SOURCE_DIR}/passes/sat/clk2fflogic.cc
${PROJECT_SOURCE_DIR}/passes/sat/async2sync.cc
${PROJECT_SOURCE_DIR}/passes/sat/supercover.cc
${PROJECT_SOURCE_DIR}/passes/sat/fmcombine.cc
${PROJECT_SOURCE_DIR}/passes/sat/mutate.cc
${PROJECT_SOURCE_DIR}/passes/sat/cutpoint.cc
${PROJECT_SOURCE_DIR}/passes/sat/fminit.cc
${PROJECT_SOURCE_DIR}/passes/sat/qbfsat.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_merge.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_mem.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_mem_feedback.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_mem_priority.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_mem_widen.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_muxtree.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_reduce.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_dff.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_share.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_clean.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_expr.cc
${PROJECT_SOURCE_DIR}/passes/opt/share.cc
${PROJECT_SOURCE_DIR}/passes/opt/wreduce.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_demorgan.cc
${PROJECT_SOURCE_DIR}/passes/opt/rmports.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_lut.cc
${PROJECT_SOURCE_DIR}/passes/opt/opt_lut_ins.cc
${PROJECT_SOURCE_DIR}/passes/opt/pmux2shiftx.cc
${PROJECT_SOURCE_DIR}/passes/opt/muxpack.cc
${PROJECT_SOURCE_DIR}/passes/memory/memory.cc
${PROJECT_SOURCE_DIR}/passes/memory/memory_dff.cc
${PROJECT_SOURCE_DIR}/passes/memory/memory_share.cc
${PROJECT_SOURCE_DIR}/passes/memory/memory_collect.cc
${PROJECT_SOURCE_DIR}/passes/memory/memory_unpack.cc
${PROJECT_SOURCE_DIR}/passes/memory/memory_bram.cc
${PROJECT_SOURCE_DIR}/passes/memory/memory_map.cc
${PROJECT_SOURCE_DIR}/passes/memory/memory_memx.cc
${PROJECT_SOURCE_DIR}/passes/memory/memory_nordff.cc
${PROJECT_SOURCE_DIR}/passes/memory/memory_narrow.cc
${PROJECT_SOURCE_DIR}/passes/techmap/flatten.cc
${PROJECT_SOURCE_DIR}/passes/techmap/techmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/simplemap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/dfflibmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/maccmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/libparse.cc
${PROJECT_SOURCE_DIR}/passes/techmap/iopadmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/clkbufmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/hilomap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/extract.cc
${PROJECT_SOURCE_DIR}/passes/techmap/extract_fa.cc
${PROJECT_SOURCE_DIR}/passes/techmap/extract_counter.cc
${PROJECT_SOURCE_DIR}/passes/techmap/extract_reduce.cc
${PROJECT_SOURCE_DIR}/passes/techmap/alumacc.cc
${PROJECT_SOURCE_DIR}/passes/techmap/dffinit.cc
${PROJECT_SOURCE_DIR}/passes/techmap/pmuxtree.cc
${PROJECT_SOURCE_DIR}/passes/techmap/bmuxmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/demuxmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/muxcover.cc
${PROJECT_SOURCE_DIR}/passes/techmap/aigmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/tribuf.cc
${PROJECT_SOURCE_DIR}/passes/techmap/lut2mux.cc
${PROJECT_SOURCE_DIR}/passes/techmap/nlutmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/shregmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/deminout.cc
${PROJECT_SOURCE_DIR}/passes/techmap/insbuf.cc
${PROJECT_SOURCE_DIR}/passes/techmap/attrmvcp.cc
${PROJECT_SOURCE_DIR}/passes/techmap/attrmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/zinit.cc
${PROJECT_SOURCE_DIR}/passes/techmap/dfflegalize.cc
${PROJECT_SOURCE_DIR}/passes/techmap/dffunmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/flowmap.cc
${PROJECT_SOURCE_DIR}/passes/techmap/extractinv.cc
# ${PROJECT_SOURCE_DIR}/passes/pmgen/test_pmgen.cc
# ${PROJECT_SOURCE_DIR}/passes/pmgen/ice40_dsp.cc
# ${PROJECT_SOURCE_DIR}/passes/pmgen/ice40_wrapcarry.cc
# ${PROJECT_SOURCE_DIR}/passes/pmgen/xilinx_dsp.cc
# ${PROJECT_SOURCE_DIR}/passes/pmgen/peepopt.cc
# ${PROJECT_SOURCE_DIR}/passes/pmgen/xilinx_srl.cc
${PROJECT_SOURCE_DIR}/passes/cmds/exec.cc
${PROJECT_SOURCE_DIR}/passes/cmds/add.cc
${PROJECT_SOURCE_DIR}/passes/cmds/delete.cc
${PROJECT_SOURCE_DIR}/passes/cmds/design.cc
${PROJECT_SOURCE_DIR}/passes/cmds/select.cc
${PROJECT_SOURCE_DIR}/passes/cmds/show.cc
${PROJECT_SOURCE_DIR}/passes/cmds/rename.cc
${PROJECT_SOURCE_DIR}/passes/cmds/autoname.cc
${PROJECT_SOURCE_DIR}/passes/cmds/connect.cc
${PROJECT_SOURCE_DIR}/passes/cmds/scatter.cc
${PROJECT_SOURCE_DIR}/passes/cmds/setundef.cc
${PROJECT_SOURCE_DIR}/passes/cmds/splitnets.cc
${PROJECT_SOURCE_DIR}/passes/cmds/stat.cc
${PROJECT_SOURCE_DIR}/passes/cmds/setattr.cc
${PROJECT_SOURCE_DIR}/passes/cmds/copy.cc
${PROJECT_SOURCE_DIR}/passes/cmds/splice.cc
${PROJECT_SOURCE_DIR}/passes/cmds/scc.cc
${PROJECT_SOURCE_DIR}/passes/cmds/glift.cc
${PROJECT_SOURCE_DIR}/passes/cmds/torder.cc
${PROJECT_SOURCE_DIR}/passes/cmds/logcmd.cc
${PROJECT_SOURCE_DIR}/passes/cmds/tee.cc
${PROJECT_SOURCE_DIR}/passes/cmds/write_file.cc
${PROJECT_SOURCE_DIR}/passes/cmds/connwrappers.cc
${PROJECT_SOURCE_DIR}/passes/cmds/cover.cc
${PROJECT_SOURCE_DIR}/passes/cmds/trace.cc
${PROJECT_SOURCE_DIR}/passes/cmds/plugin.cc
${PROJECT_SOURCE_DIR}/passes/cmds/check.cc
${PROJECT_SOURCE_DIR}/passes/cmds/qwp.cc
${PROJECT_SOURCE_DIR}/passes/cmds/edgetypes.cc
${PROJECT_SOURCE_DIR}/passes/cmds/portlist.cc
${PROJECT_SOURCE_DIR}/passes/cmds/chformal.cc
${PROJECT_SOURCE_DIR}/passes/cmds/chtype.cc
${PROJECT_SOURCE_DIR}/passes/cmds/blackbox.cc
${PROJECT_SOURCE_DIR}/passes/cmds/ltp.cc
${PROJECT_SOURCE_DIR}/passes/cmds/bugpoint.cc
${PROJECT_SOURCE_DIR}/passes/cmds/scratchpad.cc
${PROJECT_SOURCE_DIR}/passes/cmds/logger.cc
${PROJECT_SOURCE_DIR}/passes/cmds/printattrs.cc
${PROJECT_SOURCE_DIR}/passes/cmds/sta.cc
${PROJECT_SOURCE_DIR}/passes/cmds/clean_zerowidth.cc
${PROJECT_SOURCE_DIR}/passes/hierarchy/hierarchy.cc
${PROJECT_SOURCE_DIR}/passes/hierarchy/uniquify.cc
${PROJECT_SOURCE_DIR}/passes/hierarchy/submod.cc
${PROJECT_SOURCE_DIR}/passes/equiv/equiv_make.cc
${PROJECT_SOURCE_DIR}/passes/equiv/equiv_miter.cc
${PROJECT_SOURCE_DIR}/passes/equiv/equiv_simple.cc
${PROJECT_SOURCE_DIR}/passes/equiv/equiv_status.cc
${PROJECT_SOURCE_DIR}/passes/equiv/equiv_add.cc
${PROJECT_SOURCE_DIR}/passes/equiv/equiv_remove.cc
${PROJECT_SOURCE_DIR}/passes/equiv/equiv_induct.cc
${PROJECT_SOURCE_DIR}/passes/equiv/equiv_struct.cc
${PROJECT_SOURCE_DIR}/passes/equiv/equiv_purge.cc
${PROJECT_SOURCE_DIR}/passes/equiv/equiv_mark.cc
${PROJECT_SOURCE_DIR}/passes/equiv/equiv_opt.cc
${PROJECT_SOURCE_DIR}/passes/fsm/fsm.cc
${PROJECT_SOURCE_DIR}/passes/fsm/fsm_detect.cc
${PROJECT_SOURCE_DIR}/passes/fsm/fsm_extract.cc
${PROJECT_SOURCE_DIR}/passes/fsm/fsm_opt.cc
${PROJECT_SOURCE_DIR}/passes/fsm/fsm_expand.cc
${PROJECT_SOURCE_DIR}/passes/fsm/fsm_recode.cc
${PROJECT_SOURCE_DIR}/passes/fsm/fsm_info.cc
${PROJECT_SOURCE_DIR}/passes/fsm/fsm_export.cc
${PROJECT_SOURCE_DIR}/passes/fsm/fsm_map.cc
${PROJECT_SOURCE_DIR}/passes/proc/proc.cc
${PROJECT_SOURCE_DIR}/passes/proc/proc_prune.cc
${PROJECT_SOURCE_DIR}/passes/proc/proc_clean.cc
${PROJECT_SOURCE_DIR}/passes/proc/proc_rmdead.cc
${PROJECT_SOURCE_DIR}/passes/proc/proc_init.cc
${PROJECT_SOURCE_DIR}/passes/proc/proc_arst.cc
${PROJECT_SOURCE_DIR}/passes/proc/proc_mux.cc
${PROJECT_SOURCE_DIR}/passes/proc/proc_dlatch.cc
${PROJECT_SOURCE_DIR}/passes/proc/proc_dff.cc
${PROJECT_SOURCE_DIR}/passes/proc/proc_memwr.cc
${PROJECT_SOURCE_DIR}/backends/firrtl/firrtl.cc
${PROJECT_SOURCE_DIR}/backends/simplec/simplec.cc
${PROJECT_SOURCE_DIR}/backends/edif/edif.cc
${PROJECT_SOURCE_DIR}/backends/cxxrtl/cxxrtl_backend.cc
${PROJECT_SOURCE_DIR}/backends/aiger/aiger.cc
${PROJECT_SOURCE_DIR}/backends/aiger/xaiger.cc
${PROJECT_SOURCE_DIR}/backends/smt2/smt2.cc
${PROJECT_SOURCE_DIR}/backends/table/table.cc
${PROJECT_SOURCE_DIR}/backends/btor/btor.cc
${PROJECT_SOURCE_DIR}/backends/intersynth/intersynth.cc
${PROJECT_SOURCE_DIR}/backends/json/json.cc
${PROJECT_SOURCE_DIR}/backends/verilog/verilog_backend.cc
${PROJECT_SOURCE_DIR}/backends/smv/smv.cc
${PROJECT_SOURCE_DIR}/backends/blif/blif.cc
${PROJECT_SOURCE_DIR}/backends/rtlil/rtlil_backend.cc
${PROJECT_SOURCE_DIR}/backends/spice/spice.cc
${PROJECT_SOURCE_DIR}/techlibs/easic/synth_easic.cc
# ${PROJECT_SOURCE_DIR}/techlibs/xilinx/synth_xilinx.cc
# ${PROJECT_SOURCE_DIR}/techlibs/xilinx/xilinx_dffopt.cc
${PROJECT_SOURCE_DIR}/techlibs/gowin/synth_gowin.cc
${PROJECT_SOURCE_DIR}/techlibs/ice40/synth_ice40.cc
${PROJECT_SOURCE_DIR}/techlibs/ice40/ice40_braminit.cc
${PROJECT_SOURCE_DIR}/techlibs/ice40/ice40_opt.cc
${PROJECT_SOURCE_DIR}/techlibs/nexus/synth_nexus.cc
${PROJECT_SOURCE_DIR}/techlibs/machxo2/synth_machxo2.cc
${PROJECT_SOURCE_DIR}/techlibs/intel/synth_intel.cc
${PROJECT_SOURCE_DIR}/techlibs/ecp5/synth_ecp5.cc
${PROJECT_SOURCE_DIR}/techlibs/ecp5/ecp5_gsr.cc
${PROJECT_SOURCE_DIR}/techlibs/coolrunner2/synth_coolrunner2.cc
${PROJECT_SOURCE_DIR}/techlibs/coolrunner2/coolrunner2_sop.cc
${PROJECT_SOURCE_DIR}/techlibs/coolrunner2/coolrunner2_fixup.cc
${PROJECT_SOURCE_DIR}/techlibs/efinix/synth_efinix.cc
${PROJECT_SOURCE_DIR}/techlibs/efinix/efinix_fixcarry.cc
${PROJECT_SOURCE_DIR}/techlibs/greenpak4/synth_greenpak4.cc
${PROJECT_SOURCE_DIR}/techlibs/greenpak4/greenpak4_dffinv.cc
${PROJECT_SOURCE_DIR}/techlibs/gatemate/synth_gatemate.cc
${PROJECT_SOURCE_DIR}/techlibs/anlogic/synth_anlogic.cc
${PROJECT_SOURCE_DIR}/techlibs/anlogic/anlogic_eqn.cc
${PROJECT_SOURCE_DIR}/techlibs/anlogic/anlogic_fixcarry.cc
${PROJECT_SOURCE_DIR}/techlibs/achronix/synth_achronix.cc
${PROJECT_SOURCE_DIR}/techlibs/common/synth.cc
${PROJECT_SOURCE_DIR}/techlibs/common/prep.cc
${PROJECT_SOURCE_DIR}/techlibs/quicklogic/synth_quicklogic.cc
${PROJECT_SOURCE_DIR}/techlibs/intel_alm/synth_intel_alm.cc
${PROJECT_SOURCE_DIR}/techlibs/sf2/synth_sf2.cc
# clear && make -f ~/Documents/interstellar/lib_circuits/build/mono-clang/_deps/yosys_dl-src/Makefile --just-print libyosys.so | grep ".*yosys_dl-src.*.cpp$" | awk '{print $NF}'
${PROJECT_SOURCE_DIR}/libs/sha1/sha1.cpp
${PROJECT_SOURCE_DIR}/libs/json11/json11.cpp

${PROJECT_BINARY_DIR}/techlibs/common/simcells_help.inc
${PROJECT_BINARY_DIR}/techlibs/common/simlib_help.inc
)

################################################################################

add_library(libyosys
    ${YOSYS_SRCS}
)

target_include_directories(libyosys
    PUBLIC
    # needed for #include <kernel/yosys.h> (eg in verilog_compiler.cpp)
    # TODO could probably do what "make install" does and skip including the whole sources
    "${PROJECT_SOURCE_DIR}"

    PRIVATE
    "${PROJECT_BINARY_DIR}"

    "${TCL_INCLUDE_PATH}"
)

target_compile_definitions(libyosys
    PUBLIC
    # kernel/yosys.h:75:4: error: It looks like you are trying to build Yosys without the config defines set.          When building Yosys with a custom make system, make sure you set all the          defines the Yosys Makefile would set for your build configuration.
    # [build] #  error It looks like you are trying to build Yosys without the config defines set. \
    _YOSYS_

    PRIVATE
    # TODO all of those SHOULD depend on the corresponding option
    # cf Yosys beginning of Yosys Makefile
    # ENABLE_LIBYOSYS=1
    # ENABLE_ABC=0
    $<IF:$<BOOL:${YOSYS_ENABLE_DEBUG}>,DEBUG,RELEASE>
    # ENABLE_TCL := 1
    YOSYS_ENABLE_TCL
    # ENABLE_ABC := 0
    # ENABLE_GLOB := 1
    YOSYS_ENABLE_GLOB
    # ENABLE_PLUGINS := 1
    # YOSYS_ENABLE_PLUGINS # TODO? if yes add FindFFI
    # ENABLE_READLINE := 1
    YOSYS_ENABLE_READLINE
    # ENABLE_EDITLINE := 0
    # ENABLE_GHDL := 0
    # ENABLE_VERIFIC := 0
    # DISABLE_VERIFIC_EXTENSIONS := 0
    # DISABLE_VERIFIC_VHDL := 0
    # ENABLE_COVER := 1
    YOSYS_ENABLE_COVER
    # ENABLE_LIBYOSYS := 0
    # ENABLE_PROTOBUF := 0
    # ENABLE_ZLIB=1
    YOSYS_ENABLE_ZLIB

    # not needed b/c we are not using the Makefile anymore
    # PREFIX=${INSTALL_DIR}

    YOSYS_SRC="${PROJECT_SOURCE_DIR}"
)

target_link_libraries(libyosys
    PRIVATE
    # TODO?
    # -lm

    # TODO all of those SHOULD depend on the corresponding option
    ${TCL_LIBRARY}
    ZLIB::ZLIB
    ${READLINE_LIBRARY}
)

# c++20: "error: use of overloaded operator '==' is ambiguous"
set_property(TARGET libyosys PROPERTY CXX_STANDARD 11)

target_compile_options(libyosys
    PRIVATE
    $<$<CXX_COMPILER_ID:GNU>:
        -Wno-class-memaccess
        -Wno-maybe-uninitialized
    >
    $<$<CXX_COMPILER_ID:Clang>:

    >
)

################################################################################
# cf https://github.com/Interstellar-Network/lib_server/blob/develop/cmake/yosys/CMakeLists.txt

# kernel/version_$(GIT_REV).cc: $(YOSYS_SRC)/Makefile
# around line 730 in Yosys Makefile
configure_file(${PROJECT_SOURCE_DIR}/version/version.in.cc ${PROJECT_BINARY_DIR}/kernel/version.cc)

# see yosys/frontends/verilog/Makefile.inc
# frontends/verilog/verilog_parser.tab.cc: frontends/verilog/verilog_parser.y
# 	$(Q) mkdir -p $(dir $@)
# 	$(P) $(BISON) -d -r all -b frontends/verilog/verilog_parser $<
# 	$(Q) mv frontends/verilog/verilog_parser.tab.c frontends/verilog/verilog_parser.tab.cc
add_custom_command(
    COMMAND ${BISON} -d -r all -b ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser ${PROJECT_SOURCE_DIR}/frontends/verilog/verilog_parser.y
    OUTPUT
        ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.c
        ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.h
    DEPENDS ${PROJECT_SOURCE_DIR}/frontends/verilog/verilog_parser.y
    WORKING_DIRECTORY ${PROJECT_BINARY_DIR}
)
# NOTE: use symlink instead of mv to avoid regenerating each build
add_custom_command(
    COMMAND ${CMAKE_COMMAND} -E create_symlink ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.c ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.cc
    OUTPUT ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.cc
    DEPENDS ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.c
    WORKING_DIRECTORY ${PROJECT_BINARY_DIR}
)
add_custom_command(
    COMMAND ${CMAKE_COMMAND} -E create_symlink ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.h ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.hh
    OUTPUT ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.hh
    DEPENDS ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.h
    WORKING_DIRECTORY ${PROJECT_BINARY_DIR}
)

# frontends/verilog/verilog_lexer.cc: frontends/verilog/verilog_lexer.l
# 	$(Q) mkdir -p $(dir $@)
# 	$(P) flex -o frontends/verilog/verilog_lexer.cc $<
add_custom_command(
    COMMAND ${FLEX} -o ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_lexer.cc ${PROJECT_SOURCE_DIR}/frontends/verilog/verilog_lexer.l
    OUTPUT ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_lexer.cc
    DEPENDS
        ${PROJECT_SOURCE_DIR}/frontends/verilog/verilog_lexer.l
        ${PROJECT_BINARY_DIR}/frontends/verilog/verilog_parser.tab.cc
    WORKING_DIRECTORY ${PROJECT_BINARY_DIR}
)

# build/_deps/yosys_dl-src/frontends/rtlil/Makefile.inc
# frontends/rtlil/rtlil_parser.tab.cc: frontends/rtlil/rtlil_parser.y
# 	$(Q) mkdir -p $(dir $@)
# 	$(P) $(BISON) -o $@ -d -r all -b frontends/rtlil/rtlil_parser $<
add_custom_command(
    COMMAND ${BISON} -d -r all -b ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser ${PROJECT_SOURCE_DIR}/frontends/rtlil/rtlil_parser.y
    OUTPUT
        ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.c
        ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.h
    DEPENDS ${PROJECT_SOURCE_DIR}/frontends/rtlil/rtlil_parser.y
    WORKING_DIRECTORY ${PROJECT_BINARY_DIR}
)
# NOTE: use symlink instead of mv to avoid regenerating each build
add_custom_command(
    COMMAND ${CMAKE_COMMAND} -E create_symlink ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.c ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.cc
    OUTPUT ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.cc
    DEPENDS ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.c
    WORKING_DIRECTORY ${PROJECT_BINARY_DIR}
)
add_custom_command(
    COMMAND ${CMAKE_COMMAND} -E create_symlink ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.h ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.hh
    OUTPUT ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.hh
    DEPENDS ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.h
    WORKING_DIRECTORY ${PROJECT_BINARY_DIR}
)

# frontends/rtlil/rtlil_lexer.cc: frontends/rtlil/rtlil_lexer.l
# 	$(Q) mkdir -p $(dir $@)
# 	$(P) flex -o frontends/rtlil/rtlil_lexer.cc $<
add_custom_command(
    COMMAND ${FLEX} -o ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_lexer.cc ${PROJECT_SOURCE_DIR}/frontends/rtlil/rtlil_lexer.l
    OUTPUT ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_lexer.cc
    DEPENDS
        ${PROJECT_SOURCE_DIR}/frontends/rtlil/rtlil_lexer.l
        ${PROJECT_BINARY_DIR}/frontends/rtlil/rtlil_parser.tab.cc
    WORKING_DIRECTORY ${PROJECT_BINARY_DIR}
)

# see yosys/techlibs/common/Makefile.inc
function(simlib_help input_v output_inc)
    # techlibs/common/simlib_help.inc: techlibs/common/cellhelp.py techlibs/common/simlib.v
    #     $(Q) mkdir -p techlibs/common
    #     $(P) python3 $^ > $@.new
    #     $(Q) mv $@.new $@
    add_custom_command(
        COMMAND ${PYTHON3_EXE} ${PROJECT_SOURCE_DIR}/techlibs/common/cellhelp.py ${input_v} > ${output_inc}
        OUTPUT ${output_inc}
        DEPENDS ${input_v}
        WORKING_DIRECTORY ${PROJECT_BINARY_DIR}
    )
endfunction(simlib_help)

simlib_help(${PROJECT_SOURCE_DIR}/techlibs/common/simcells.v ${PROJECT_BINARY_DIR}/techlibs/common/simcells_help.inc)
simlib_help(${PROJECT_SOURCE_DIR}/techlibs/common/simlib.v ${PROJECT_BINARY_DIR}/techlibs/common/simlib_help.inc)

################################################################################

add_executable(yosys_exe
    ${PROJECT_SOURCE_DIR}/kernel/driver.cc
)

target_link_libraries(yosys_exe
    PRIVATE
    libyosys
)

################################################################################

if(YOSYS_ENABLE_TESTING)
  enable_testing()
  add_subdirectory(tests)
endif(YOSYS_ENABLE_TESTING)