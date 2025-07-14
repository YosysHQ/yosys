

add_library(yosys_backends_firrtl OBJECT
    firrtl.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_firrtl)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_firrtl>)
