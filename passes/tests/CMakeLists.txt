

add_library(yosys_passes_tests OBJECT
    test_autotb.cc
    test_cell.cc
    test_abcloop.cc
)

target_link_libraries(yosys PUBLIC yosys_passes_tests)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_passes_tests>)
