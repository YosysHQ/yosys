
SET(BIGINT_LIB_SRC
        bigint/BigInteger.cc
        bigint/BigInteger.hh
        bigint/BigIntegerAlgorithms.cc
        bigint/BigIntegerAlgorithms.hh
        bigint/BigIntegerLibrary.hh
        bigint/BigIntegerUtils.cc
        bigint/BigIntegerUtils.hh
        bigint/BigUnsigned.cc
        bigint/BigUnsigned.hh
        bigint/BigUnsignedInABase.cc
        bigint/BigUnsignedInABase.hh
        bigint/NumberlikeArray.hh
        )

SET(EZSAT_LIB_SRC
        ezsat/ezminisat.cc
        ezsat/ezminisat.h
        ezsat/ezsat.cc
        ezsat/ezsat.h
        )

SET(JSON11_LIB_SRC
        json11/json11.cpp
        json11/json11.hpp
        )

SET(MINISAT_LIB_SRC
        minisat/Alg.h
        minisat/Alloc.h
        minisat/Dimacs.h
        minisat/Heap.h
        minisat/IntMap.h
        minisat/IntTypes.h
        minisat/Map.h
        minisat/Options.cc
        minisat/Options.h
        minisat/ParseUtils.h
        minisat/Queue.h
        minisat/Rnd.h
        minisat/SimpSolver.cc
        minisat/SimpSolver.h
        minisat/Solver.cc
        minisat/Solver.h
        minisat/SolverTypes.h
        minisat/Sort.h
        minisat/System.cc
        minisat/System.h
        minisat/Vec.h
        minisat/XAlloc.h
        )

SET(SHA1_LIB_SRC
        sha1/sha1.cpp
        sha1/sha1.h
        )

SET(SUBCIRCUIT_LIB_SRC
        subcircuit/subcircuit.cc
        subcircuit/subcircuit.h
        )

SET(LIBS_SRC )
SET(ENABLED_LIBS )

MACRO(ADD_YOSYS_LIBS Name Enabled)
    OPTION(ENABLE_${Name}_LIB "Enable ${Name} lib." ${Enabled})
    IF (ENABLE_${Name}_LIB)
        FOREACH(SRC ${${Name}_LIB_SRC})
            LIST(APPEND LIBS_SRC ${CMAKE_CURRENT_LIST_DIR}/${SRC})
        ENDFOREACH()
        LIST(APPEND ENABLED_LIBS ${Name})
    ENDIF()
ENDMACRO()

ADD_YOSYS_LIBS(BIGINT      ON)
ADD_YOSYS_LIBS(EZSAT       ON)
ADD_YOSYS_LIBS(JSON11      ON)
ADD_YOSYS_LIBS(MINISAT     ON)
ADD_YOSYS_LIBS(SHA1        ON)
ADD_YOSYS_LIBS(SUBCIRCUIT  ON)

MESSAGE("<< Enabled libs: ${ENABLED_LIBS} >>")
SET(LIBS_SRC ${LIBS_SRC} PARENT_SCOPE)
