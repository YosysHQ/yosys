

add_library(yosys_frontends_verific OBJECT
    verific.cc
    #verificsva.cc
)

target_link_libraries(yosys PUBLIC yosys_frontends_verific)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_verific>)
