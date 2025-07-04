add_library(yosys_passes_proc INTERFACE)

target_sources(yosys_passes_proc INTERFACE
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
