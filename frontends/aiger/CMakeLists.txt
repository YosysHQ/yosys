

add_library(yosys_frontends_aiger OBJECT
    aigerparse.cc
    aigerparse.h
)

target_link_libraries(yosys PUBLIC yosys_frontends_aiger)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_aiger>)
