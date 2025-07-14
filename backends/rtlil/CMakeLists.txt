

add_library(yosys_backends_rtlil OBJECT
    rtlil_backend.cc
    rtlil_backend.h
)

target_link_libraries(yosys PUBLIC yosys_backends_rtlil)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_rtlil>)
