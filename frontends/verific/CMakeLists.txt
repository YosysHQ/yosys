add_library(yosys_frontends_verific INTERFACE)

target_sources(yosys_frontends_verific INTERFACE
    verific.cc
    #verificsva.cc
)

target_link_libraries(yosys PUBLIC yosys_frontends_verific)
