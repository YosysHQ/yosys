

add_library(yosys_techlibs_gatemate OBJECT
    synth_gatemate.cc
    gatemate_foldinv.cc
)

add_custom_command(
	COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/make_lut_tree_lib.py
	DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/make_lut_tree_lib.py
	OUTPUT lut_tree_cells.genlib lut_tree_map.v
	COMMENT "Generating techlibs/gatemate/lut_tree_map.v..."
    WORKING_DIRECTORY ${yosys_BINARY_DIR}
)

target_sources(yosys_techlibs_gatemate PRIVATE
	${CMAKE_CURRENT_BINARY_DIR}/lut_tree_cells.genlib
    ${CMAKE_CURRENT_BINARY_DIR}/lut_tree_map.v
)

target_link_libraries(yosys_obj PUBLIC yosys_techlibs_gatemate)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_techlibs_gatemate>)

add_share_file("share/gatemate" "reg_map.v")
add_share_file("share/gatemate" "mux_map.v")
add_share_file("share/gatemate" "lut_map.v")
add_share_file("share/gatemate" "mul_map.v")
add_share_file("share/gatemate" "arith_map.v")
add_share_file("share/gatemate" "cells_sim.v")
add_share_file("share/gatemate" "cells_bb.v")
add_share_file("share/gatemate" "brams_map.v")
add_share_file("share/gatemate" "brams.txt")
add_share_file("share/gatemate" "brams_init_20.vh")
add_share_file("share/gatemate" "brams_init_40.vh")
add_share_file("share/gatemate" "inv_map.v")

add_gen_share_file("share/gatemate" ${CMAKE_CURRENT_BINARY_DIR}/lut_tree_cells.genlib)
add_gen_share_file("share/gatemate" ${CMAKE_CURRENT_BINARY_DIR}/lut_tree_map.v)
