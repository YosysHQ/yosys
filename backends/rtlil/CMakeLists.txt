

add_library(yosys_backends_rtlil OBJECT
    rtlil_backend.cc
    rtlil_backend.h
)

target_link_libraries(yosys_obj PUBLIC yosys_backends_rtlil)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_backends_rtlil>)
