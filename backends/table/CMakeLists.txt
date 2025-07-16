

add_library(yosys_backends_table OBJECT
    table.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_backends_table)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_backends_table>)
