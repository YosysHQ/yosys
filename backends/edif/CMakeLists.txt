

add_library(yosys_backends_edif OBJECT
    edif.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_backends_edif)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_backends_edif>)
