

add_library(yosys_backends_intersynth OBJECT
    intersynth.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_backends_intersynth)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_backends_intersynth>)
