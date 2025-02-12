add_library(yosys_passes_fsm INTERFACE)

target_sources(yosys_passes_fsm INTERFACE
    fsm.cc
    fsm_detect.cc
    fsm_extract.cc
    fsm_opt.cc
    fsm_expand.cc
    fsm_recode.cc
    fsm_info.cc
    fsm_export.cc
    fsm_map.cc
    fsmdata.h
)

target_link_libraries(yosys PRIVATE yosys_passes_fsm)
