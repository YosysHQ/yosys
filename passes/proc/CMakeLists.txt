

add_library(yosys_passes_proc OBJECT
    proc.cc
    proc_prune.cc
    proc_clean.cc
    proc_rmdead.cc
    proc_init.cc
    proc_arst.cc
    proc_rom.cc
    proc_mux.cc
    proc_dlatch.cc
    proc_dff.cc
    proc_memwr.cc
)

target_link_libraries(yosys PUBLIC yosys_passes_proc)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_passes_proc>)
