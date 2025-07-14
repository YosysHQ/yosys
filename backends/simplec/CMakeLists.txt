

add_library(yosys_backends_simplec OBJECT
    simplec.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_simplec)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_simplec>)
