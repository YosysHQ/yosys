if (NOT DISABLE_SPAWN)
    

    add_library(yosys_frontends_rpc OBJECT
        rpc_frontend.cc
    )

    target_link_libraries(yosys PUBLIC yosys_frontends_rpc)
    target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_rpc>)
endif()
