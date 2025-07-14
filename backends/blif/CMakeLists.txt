

add_library(yosys_backends_blif OBJECT
    blif.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_blif)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_blif>)
