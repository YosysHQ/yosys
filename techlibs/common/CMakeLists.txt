add_library(yosys_techlib_common INTERFACE)

add_custom_command(
    COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_CURRENT_BINARY_DIR}/techlibs/common
	COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/cellhelp.py ${CMAKE_CURRENT_SOURCE_DIR}/simlib.v > ${CMAKE_CURRENT_BINARY_DIR}/simlib_help.inc
	DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/cellhelp.py ${CMAKE_CURRENT_SOURCE_DIR}/simlib.v
	OUTPUT simlib_help.inc
	COMMENT "Generating techlibs/common/simlib_help.inc..."
)
add_custom_command(
    COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_CURRENT_BINARY_DIR}/techlibs/common
	COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/cellhelp.py ${CMAKE_CURRENT_SOURCE_DIR}/simcells.v > ${CMAKE_CURRENT_BINARY_DIR}/simcells_help.inc
	DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/cellhelp.py ${CMAKE_CURRENT_SOURCE_DIR}/simcells.v
	OUTPUT simcells_help.inc
	COMMENT "Generating techlibs/common/simcells_help.inc..."
)

add_custom_target(yosys_techlib_common_gen DEPENDS
	${CMAKE_CURRENT_BINARY_DIR}/simlib_help.inc
	${CMAKE_CURRENT_BINARY_DIR}/simcells_help.inc
)

target_sources(yosys_techlib_common INTERFACE
    synth.cc
    prep.cc
)

add_dependencies(yosys_techlib_common yosys_techlib_common_gen)

target_link_libraries(yosys PRIVATE yosys_techlib_common)