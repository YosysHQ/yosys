

add_library(yosys_backends_smv OBJECT
    smv.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_smv)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_smv>)
