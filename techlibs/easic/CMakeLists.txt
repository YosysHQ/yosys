

add_library(yosys_techlibs_easic OBJECT
    synth_easic.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_techlibs_easic)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_techlibs_easic>)
