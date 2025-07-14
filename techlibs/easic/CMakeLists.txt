

add_library(yosys_techlibs_easic OBJECT
    synth_easic.cc
)

target_link_libraries(yosys PUBLIC yosys_techlibs_easic)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_techlibs_easic>)
