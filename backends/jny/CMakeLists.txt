

add_library(yosys_backends_jny OBJECT
    jny.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_jny)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_jny>)
