if (NOT DISABLE_SPAWN)
    

    add_library(yosys_frontends_rpc OBJECT
        rpc_frontend.cc
    )

    target_link_libraries(yosys_obj PUBLIC yosys_frontends_rpc)
    target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_frontends_rpc>)
endif()
