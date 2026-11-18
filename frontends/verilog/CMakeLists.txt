if (APPLE)
	# Prefer the FlexLexer.h shipped next to the flex executable in use
	get_filename_component(_flex_bin "${FLEX_EXECUTABLE}" DIRECTORY)
	get_filename_component(_flex_real "${FLEX_EXECUTABLE}" REALPATH)
	get_filename_component(_flex_real_bin "${_flex_real}" DIRECTORY)
	find_path(FLEX_LEXER_INCLUDE_DIR FlexLexer.h
		PATHS
			${_flex_bin}/../include ${_flex_bin}
			${_flex_real_bin}/../include ${_flex_real_bin}
		NO_DEFAULT_PATH
	)
	if (FLEX_LEXER_INCLUDE_DIR)
		set(FLEX_INCLUDE_DIRS ${FLEX_LEXER_INCLUDE_DIR})
	endif()
endif()

if (NOT FLEX_INCLUDE_DIRS)
	set(FLEX_INCLUDE_DIRS ${YOSYS_CMAKE_SOURCE_DIR}/libs/flex)
endif()

flex_target(verilog_lexer
	verilog_lexer.l
	verilog_lexer.cc
)
bison_target(verilog_parser
	verilog_parser.y
	verilog_parser.tab.cc
	# (requires CMake 4.0)
	# OPTIONS
	# 	-Wall -Werror
)
yosys_frontend(verilog
  const2ast.cc
	preproc.cc
	preproc.h
	verilog_error.cc
	verilog_error.h
	verilog_frontend.cc
	verilog_frontend.h
	verilog_lexer.h
	verilog_location.h
	${FLEX_verilog_lexer_OUTPUTS}
	${BISON_verilog_parser_OUTPUTS}
	INCLUDE_DIRS
		${FLEX_INCLUDE_DIRS}
	REQUIRES
		sha1
		ast
	PROVIDES
		verilog_defaults
		verilog_defines
		read_verilog_file_list
	ESSENTIAL
)
set_source_files_properties(
	${BISON_verilog_parser_OUTPUT_SOURCE}
	PROPERTIES
		COMPILE_DEFINITIONS -DYYMAXDEPTH=10000000
)
