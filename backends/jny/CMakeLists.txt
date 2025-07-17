

add_library(yosys_backends_jny OBJECT
    jny.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_backends_jny)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_backends_jny>)
