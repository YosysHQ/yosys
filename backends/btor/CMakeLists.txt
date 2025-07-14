

add_library(yosys_backends_btor OBJECT
    btor.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_btor)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_btor>)
