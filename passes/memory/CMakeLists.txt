add_library(yosys_passes_memory INTERFACE)

target_sources(yosys_passes_memory INTERFACE
    memory.cc
    memory_dff.cc
    memory_share.cc
    memory_collect.cc
    memory_unpack.cc
    memory_bram.cc
    memory_map.cc
    memory_memx.cc
    memory_nordff.cc
    memory_narrow.cc
    memory_libmap.cc
    memory_bmux2rom.cc
    memlib.cc
    memlib.h
)

target_link_libraries(yosys PUBLIC yosys_passes_memory)
