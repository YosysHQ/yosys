

add_library(yosys_backends_aiger2 OBJECT
    aiger.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_aiger2)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_aiger2>)
