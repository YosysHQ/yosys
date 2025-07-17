

add_library(yosys_passes_tests OBJECT
    test_autotb.cc
    test_cell.cc
    test_abcloop.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_passes_tests)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_passes_tests>)
