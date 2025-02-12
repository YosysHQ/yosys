add_library(yosys_passes_tests INTERFACE)

target_sources(yosys_passes_tests INTERFACE
    test_autotb.cc
    test_cell.cc
    test_abcloop.cc
)

target_link_libraries(yosys PRIVATE yosys_passes_tests)
