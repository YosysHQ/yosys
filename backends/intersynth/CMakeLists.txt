add_library(yosys_backends_intersynth INTERFACE)

target_sources(yosys_backends_intersynth INTERFACE
    intersynth.cc
)

target_link_libraries(yosys PRIVATE yosys_backends_intersynth)
