

add_library(yosys_passes_sat OBJECT
    sat.cc
    freduce.cc
    eval.cc
    miter.cc
    expose.cc
    assertpmux.cc
    clk2fflogic.cc
    async2sync.cc
    formalff.cc
    supercover.cc
    fmcombine.cc
    mutate.cc
    cutpoint.cc
    fminit.cc
    recover_names.cc
    synthprop.cc

)

if (ENABLE_ZLIB)
target_sources(yosys_passes_sat PRIVATE
    sim.cc
)
endif()

if (NOT DISABLE_SPAWN)
target_sources(yosys_passes_sat PRIVATE
    qbfsat.cc
)
endif()

target_link_libraries(yosys_obj PUBLIC yosys_passes_sat)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_passes_sat>)
