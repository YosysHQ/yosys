

add_library(yosys_backends_spice OBJECT
    spice.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_backends_spice)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_backends_spice>)
