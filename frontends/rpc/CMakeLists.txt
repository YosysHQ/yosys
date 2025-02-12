add_library(yosys_frontends_rpc INTERFACE)

target_sources(yosys_frontends_rpc INTERFACE
    rpc_frontend.cc
)

target_link_libraries(yosys PRIVATE yosys_frontends_rpc)
