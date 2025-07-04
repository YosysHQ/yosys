add_library(yosys_passes_equiv INTERFACE)

target_sources(yosys_passes_equiv INTERFACE
    equiv_make.cc
    equiv_miter.cc
    equiv_simple.cc
    equiv_status.cc
    equiv_add.cc
    equiv_remove.cc
    equiv_induct.cc
    equiv_struct.cc
    equiv_purge.cc
    equiv_mark.cc
    equiv_opt.cc
)

target_link_libraries(yosys PUBLIC yosys_passes_equiv)
