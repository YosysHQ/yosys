CMAKE_MINIMUM_REQUIRED(VERSION 2.8.11)
PROJECT(yosys)

SET(CMAKE_C_STANDARD 11)
SET(CMAKE_CXX_STANDARD 11)

OPTION(ENABLE_ABC "Enable use ABC library." OFF)

ADD_DEFINITIONS(-D_YOSYS_)
ADD_DEFINITIONS(-DYOSYS_ENABLE_READLINE)
ADD_DEFINITIONS(-DYOSYS_ENABLE_PLUGINS)
ADD_DEFINITIONS(-DYOSYS_ENABLE_GLOB)
ADD_DEFINITIONS(-DYOSYS_ENABLE_TCL)
ADD_DEFINITIONS(-DYOSYS_ENABLE_COVER)
ADD_DEFINITIONS(-DYOSYS_ENABLE_ZLIB)
ADD_DEFINITIONS(-DYOSYS_SRC="./")
ADD_DEFINITIONS(-DYOSYS_DATDIR="/usr/local/share/yosys")

INCLUDE_DIRECTORIES(.)
INCLUDE_DIRECTORIES(/usr/include/tcl8.6)
ADD_COMPILE_OPTIONS(-Wall -Wextra -ggdb -Os -g -I/usr/include/tcl -MD -fPIC)
ADD_COMPILE_OPTIONS(-Wno-unused-parameter)

IF (${ENABLE_ABC})
    ADD_DEFINITIONS(-DYOSYS_ENABLE_ABC)
    ADD_SUBDIRECTORY(abc)
ENDIF()

ADD_SUBDIRECTORY(kernel)
ADD_SUBDIRECTORY(frontends)
ADD_SUBDIRECTORY(passes)
ADD_SUBDIRECTORY(backends)

SET(SRC_LIST
        ./libs/json11/json11.hpp
        ./libs/ezsat/ezminisat.h
        ./libs/ezsat/ezsat.h
        ./libs/subcircuit/subcircuit.h
        ./libs/minisat/IntTypes.h
        ./libs/minisat/SolverTypes.h
        ./libs/minisat/ParseUtils.h
        ./libs/minisat/Queue.h
        ./libs/minisat/Solver.h
        ./libs/minisat/Alloc.h
        ./libs/minisat/Rnd.h
        ./libs/minisat/SimpSolver.h
        ./libs/minisat/IntMap.h
        ./libs/minisat/Vec.h
        ./libs/minisat/System.h
        ./libs/minisat/Alg.h
        ./libs/minisat/Map.h
        ./libs/minisat/Heap.h
        ./libs/minisat/Options.h
        ./libs/minisat/Dimacs.h
        ./libs/minisat/XAlloc.h
        ./libs/minisat/Sort.h
        ./libs/bigint/BigUnsignedInABase.hh
        ./libs/bigint/BigIntegerLibrary.hh
        ./libs/bigint/BigIntegerAlgorithms.hh
        ./libs/bigint/BigIntegerUtils.hh
        ./libs/bigint/BigUnsigned.hh
        ./libs/bigint/BigInteger.hh
        ./libs/bigint/NumberlikeArray.hh
        ./libs/sha1/sha1.h

        ./techlibs/intel/synth_intel.cc
        ./techlibs/gowin/synth_gowin.cc
        ./techlibs/xilinx/xilinx_dffopt.cc
        ./techlibs/xilinx/synth_xilinx.cc
        ./techlibs/coolrunner2/coolrunner2_fixup.cc
        ./techlibs/coolrunner2/coolrunner2_sop.cc
        ./techlibs/coolrunner2/synth_coolrunner2.cc
        ./techlibs/sf2/synth_sf2.cc
        ./techlibs/easic/synth_easic.cc
        ./techlibs/intel_alm/synth_intel_alm.cc
        ./techlibs/ecp5/ecp5_gsr.cc
        ./techlibs/ecp5/synth_ecp5.cc
        ./techlibs/greenpak4/synth_greenpak4.cc
        ./techlibs/greenpak4/greenpak4_dffinv.cc
        ./techlibs/anlogic/anlogic_fixcarry.cc
        ./techlibs/anlogic/synth_anlogic.cc
        ./techlibs/anlogic/anlogic_eqn.cc
        ./techlibs/common/prep.cc
        ./techlibs/common/synth.cc
        ./techlibs/achronix/synth_achronix.cc
        ./techlibs/ice40/ice40_opt.cc
        ./techlibs/ice40/synth_ice40.cc
        ./techlibs/ice40/ice40_braminit.cc
        ./techlibs/efinix/efinix_fixcarry.cc
        ./techlibs/efinix/synth_efinix.cc
        ./libs/bigint/BigUnsignedInABase.cc
        ./libs/bigint/BigIntegerAlgorithms.cc
        ./libs/bigint/BigInteger.cc
        ./libs/bigint/BigUnsigned.cc
        ./libs/bigint/BigIntegerUtils.cc
        ./libs/ezsat/ezsat.cc
        ./libs/ezsat/ezminisat.cc
        ./libs/json11/json11.hpp
        ./libs/json11/json11.cpp
        ./libs/minisat/System.cc
        ./libs/minisat/Solver.cc
        ./libs/minisat/Options.cc
        ./libs/minisat/SimpSolver.cc
        ./libs/sha1/sha1.h
        ./libs/sha1/sha1.cpp
        ./libs/subcircuit/subcircuit.h
        ./libs/subcircuit/subcircuit.cc
        )

ADD_EXECUTABLE(${PROJECT_NAME} ${SRC_LIST})
TARGET_LINK_LIBRARIES(${PROJECT_NAME}
        -Wl,--start-group
        frontends
        passes
        kernel
        backends
        -Wl,--end-group
        )

IF (${ENABLE_ABC})
    TARGET_LINK_LIBRARIES(${PROJECT_NAME} libabc)
ENDIF()

TARGET_LINK_LIBRARIES(${PROJECT_NAME} -lstdc++ -lm -lz -lrt -lreadline -lffi -ldl -ltcl8.6)
