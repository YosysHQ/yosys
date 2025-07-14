

add_library(yosys_backends_table OBJECT
    table.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_table)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_table>)
