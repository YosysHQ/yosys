

add_library(yosys_backends_intersynth OBJECT
    intersynth.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_intersynth)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_intersynth>)
