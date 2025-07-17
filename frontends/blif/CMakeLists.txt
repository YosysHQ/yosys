

add_library(yosys_frontends_blif OBJECT
    blifparse.cc
    blifparse.h
)

target_link_libraries(yosys_obj PUBLIC yosys_frontends_blif)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_frontends_blif>)
