# Syntax:
#
# 	yosys_cxx_library(<target> {SHARED|STATIC}
# 		OUTPUT_NAME <name>
# 		[INCLUDE_IN_ALL_IF <condition>]
# 	)
#
# Creates a libary target `<target>` with `SHARED` or `STATIC` scope called `<name>` (or `<target>` if
# not specified), placed in the root of the build directory and prefixed with `${YOSYS_PROGRAM_PREFIX}`.
# Target is built by default and installed only if `<condition>` (an `if()` expression) is true.
#
function(yosys_cxx_library arg_TARGET arg_SCOPE)
	cmake_parse_arguments(PARSE_ARGV 2 arg "" "OUTPUT_NAME;INCLUDE_IN_ALL_IF" "")
	if (NOT arg_OUTPUT_NAME)
		message(FATAL_ERROR "OUTPUT_NAME argument is mandatory")
	endif()

	add_library(${arg_TARGET} ${arg_SCOPE})
	set_target_properties(${arg_TARGET} PROPERTIES
		PREFIX "${YOSYS_PROGRAM_PREFIX}"
		OUTPUT_NAME "${arg_OUTPUT_NAME}"
		RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
	)
	if (${arg_INCLUDE_IN_ALL_IF})
		install(TARGETS ${arg_TARGET} DESTINATION ${YOSYS_INSTALL_LIBDIR})
	else()
		set_target_properties(${arg_TARGET} PROPERTIES EXCLUDE_FROM_ALL TRUE)
	endif()
endfunction()

# Syntax:
#
# 	yosys_cxx_executable(<target>
# 		[OUTPUT_NAME <name>]
# 		[INCLUDE_IN_ALL_IF <condition>]
# 	)
#
# Creates an executable target `<target>` scope called `<name>` (or `<target>` if not specified), placed
# in the root of the build directory and prefixed with `${YOSYS_PROGRAM_PREFIX}`. Target is built by
# default and installed only if `<condition>` (an `if()` expression) is true.
#
function(yosys_cxx_executable arg_TARGET)
	cmake_parse_arguments(PARSE_ARGV 1 arg "" "OUTPUT_NAME;INCLUDE_IN_ALL_IF" "")
	if (NOT arg_OUTPUT_NAME)
		message(FATAL_ERROR "OUTPUT_NAME argument is mandatory")
	endif()

	add_executable(${arg_TARGET})
	set_target_properties(${arg_TARGET} PROPERTIES
		PREFIX "${YOSYS_PROGRAM_PREFIX}"
		OUTPUT_NAME "${arg_OUTPUT_NAME}"
		RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
	)
	if (${arg_INCLUDE_IN_ALL_IF})
		install(TARGETS ${arg_TARGET} DESTINATION ${YOSYS_INSTALL_BINDIR})
	else()
		set_target_properties(${arg_TARGET} PROPERTIES EXCLUDE_FROM_ALL TRUE)
	endif()
endfunction()

# Syntax:
#
# 	yosys_python_executable(<target> <source>)
#
# Installs Python script `<source>` as an executable in the standard binary directory, adding a launcher wrapper
# if the platform requires it. Inside `<source>`, several substitutions are available:
#  - `@PYTHON_SHEBANG@` will be replaced with an appropriate shebang line (without the initial `#!`)
#  - `@YOSYS_PROGRAM_PREFIX@` will be replaced with the program prefix
#  - any other `@\w+@` tokens have unspecified behavior and must not be used
#
function(yosys_python_executable basename source)
	if (CMAKE_SYSTEM_NAME STREQUAL MSYS)
		execute_process(
			COMMAND cygpath -w -m ${CMAKE_INSTALL_BINDIR}/python3
			OUTPUT_VARIABLE PYTHON_SHEBANG
			COMMAND_ERROR_IS_FATAL ANY
		)

		add_executable(${basename} ${CMAKE_SOURCE_DIR}/misc/launcher.c)
		target_compile_definitions(${basename} -DGUI=0)
		install(TARGETS ${basename} DESTINATION ${YOSYS_INSTALL_BINDIR})

		set(scriptname ${CMAKE_BINARY_DIR}/${YOSYS_PROGRAM_PREFIX}${basename}-script.py)
		configure_file(${CMAKE_CURRENT_SOURCE_DIR}/${source} ${scriptname} @ONLY)
		install(FILES ${scriptname} DESTINATION ${YOSYS_INSTALL_BINDIR})
	else()
		set(PYTHON_SHEBANG "/usr/bin/env python3")
		set(scriptname ${CMAKE_BINARY_DIR}/${YOSYS_PROGRAM_PREFIX}${basename}${CMAKE_EXECUTABLE_SUFFIX})
		configure_file(${CMAKE_CURRENT_SOURCE_DIR}/${source} ${scriptname} USE_SOURCE_PERMISSIONS @ONLY)
		install(PROGRAMS ${scriptname} DESTINATION ${YOSYS_INSTALL_BINDIR})
	endif()
endfunction()
