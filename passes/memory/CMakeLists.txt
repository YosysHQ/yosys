

add_library(yosys_passes_memory OBJECT
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

target_link_libraries(yosys_obj PUBLIC yosys_passes_memory)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_passes_memory>)
