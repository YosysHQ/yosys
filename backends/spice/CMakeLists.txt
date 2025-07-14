

add_library(yosys_backends_spice OBJECT
    spice.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_spice)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_spice>)
