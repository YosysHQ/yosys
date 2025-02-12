add_library(yosys_passes_sat INTERFACE)

target_sources(yosys_passes_sat INTERFACE
    sat.cc
    freduce.cc
    eval.cc
    sim.cc
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
    qbfsat.cc
    synthprop.cc

)

target_link_libraries(yosys PRIVATE yosys_passes_sat)
