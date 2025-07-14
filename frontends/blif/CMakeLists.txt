

add_library(yosys_frontends_blif OBJECT
    blifparse.cc
    blifparse.h
)

target_link_libraries(yosys PUBLIC yosys_frontends_blif)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_blif>)
