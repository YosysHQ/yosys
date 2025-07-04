set(MK_TEST_DIRS
        tests/arch/anlogic
        tests/arch/ecp5
        tests/arch/efinix
        tests/arch/gatemate
        tests/arch/gowin
        tests/arch/ice40
        tests/arch/intel_alm
        tests/arch/machxo2
        tests/arch/microchip
        tests/arch/nanoxplore
        tests/arch/nexus
        tests/arch/quicklogic/pp3
        tests/arch/quicklogic/qlf_k6n10f
        tests/arch/xilinx
        tests/opt
        tests/sat
        tests/sim
        tests/svtypes
        tests/techmap
        tests/various
)
if(ENABLE_VERIFIC AND NOT YOSYS_NOVERIFIC)
  list(APPEND MK_TEST_DIRS tests/verific)
endif()
list(APPEND MK_TEST_DIRS tests/verilog)


set(SH_TEST_DIRS
        tests/simple
        tests/simple_abc9
        tests/hana
        tests/asicworld
        tests/share
        tests/opt_share
        tests/fsm
        tests/memlib
        tests/bram
        tests/svinterfaces
        tests/xprop
        tests/select
        tests/peepopt
        tests/proc
        tests/blif
        tests/arch
        tests/rpc
        tests/memfile
        tests/fmt
        tests/cxxrtl
        tests/liberty
)
if(ENABLE_FUNCTIONAL_TESTS)
  list(APPEND SH_TEST_DIRS tests/functional)
endif()


set(SH_ABC_TEST_DIRS
        tests/memories
        tests/aiger
        tests/alumacc
)