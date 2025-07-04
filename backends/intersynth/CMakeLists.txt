add_library(yosys_backends_intersynth INTERFACE)

target_sources(yosys_backends_intersynth INTERFACE
    intersynth.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_intersynth)
