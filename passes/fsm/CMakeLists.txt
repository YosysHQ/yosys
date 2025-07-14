

add_library(yosys_passes_fsm OBJECT
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

target_link_libraries(yosys PUBLIC yosys_passes_fsm)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_passes_fsm>)
