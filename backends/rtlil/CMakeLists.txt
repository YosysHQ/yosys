add_library(yosys_backends_rtlil INTERFACE)

target_sources(yosys_backends_rtlil INTERFACE
    rtlil_backend.cc
    rtlil_backend.h
)

target_link_libraries(yosys PUBLIC yosys_backends_rtlil)
