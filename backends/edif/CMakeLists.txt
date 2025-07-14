

add_library(yosys_backends_edif OBJECT
    edif.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_edif)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_edif>)
