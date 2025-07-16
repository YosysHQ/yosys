

add_library(yosys_frontends_verific OBJECT
    verific.cc
    #verificsva.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_frontends_verific)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_frontends_verific>)
