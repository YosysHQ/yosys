

add_library(yosys_backends_aiger OBJECT
    aiger.cc
    xaiger.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_aiger)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_aiger>)