add_library(yosys_backends_jny INTERFACE)

target_sources(yosys_backends_jny INTERFACE
    jny.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_jny)
