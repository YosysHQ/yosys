include(CheckCompilerFlag)

function(target_safe_compile_options target scope)
	foreach (lang C CXX)
		foreach (flag ${ARGN})
			check_compiler_flag(${lang} ${flag} HAVE_${lang}_${flag})
			if (HAVE_${lang}_${flag})
				target_compile_options(${target} ${scope} $<$<COMPILE_LANGUAGE:${lang}>:${flag}>)
			endif()
		endforeach()
	endforeach()
endfunction()

function(_yosys_abc_extract_makefile result vardecl filename)
	# Parse a Makefile fragment and extracts the first matching variable assignment into
	# a list of values.
	file(READ ${filename} contents)
	set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS ${contents})
	if ("${contents}" MATCHES "${vardecl}(\\\\\n|[ \t])*(([^\\\\\n]|\\\\\n)+)")
		string(REGEX REPLACE "(\\\\\n|[ \t])+" ";" ${result} "${CMAKE_MATCH_2}")
	endif()
	return (PROPAGATE ${result})
endfunction()

function(yosys_abc_target arg_LIBNAME arg_EXENAME)
	cmake_parse_arguments(PARSE_ARGV 2 arg "" "INCLUDE_IN_ALL_IF" "")

	# Instead of using either the ABC Make or CMake build system, we parse the source
	# of truth: ABC's `module.make` files. This turns out to be quite trivial.
	# This way, no assumptions about the environment are made, and Yosys can be compiled
	# on Windows without MSYS as a result (while benefitting other platforms as well).
	set(all_sources)
	_yosys_abc_extract_makefile(module_files "MODULES :=" ${CMAKE_SOURCE_DIR}/abc/Makefile)
	_yosys_abc_extract_makefile(module_files_cudd "MODULES \\+=" ${CMAKE_SOURCE_DIR}/abc/Makefile)
	list(REMOVE_ITEM module_files "$(wildcard" "src/ext*)")
	foreach (module_file ${module_files} ${module_files_cudd})
		_yosys_abc_extract_makefile(module_sources "SRC \\+=" ${CMAKE_SOURCE_DIR}/abc/${module_file}/module.make)
		list(APPEND all_sources ${module_sources})
	endforeach()
	list(TRANSFORM all_sources PREPEND abc/)

	# Required to get `-DABC_NAMESPACE` below to work consistently.
	set_source_files_properties(${all_sources} PROPERTIES LANGUAGE CXX)

	set(main_source abc/src/base/main/main.c)
	list(REMOVE_ITEM all_sources ${main_source})

	find_package(Threads)
	yosys_cxx_library(${arg_LIBNAME} STATIC
		OUTPUT_NAME ${arg_LIBNAME}
	)
	target_sources(${arg_LIBNAME} PRIVATE ${all_sources})
	target_include_directories(${arg_LIBNAME} PRIVATE abc/src)
	target_compile_definitions(${arg_LIBNAME} PUBLIC
		-DWIN32_NO_DLL
		-DABC_NAMESPACE=abc
		-DABC_USE_STDINT_H=1
		-DABC_USE_CUDD=1
		-DABC_NO_DYNAMIC_LINKING
		$<$<BOOL:${Threads_FOUND}>:-DABC_USE_PTHREADS>
		$<${YOSYS_ENABLE_READLINE}:-DABC_USE_READLINE>
		-DABC_NO_RLIMIT
	)
	target_safe_compile_options(${arg_LIBNAME} PRIVATE
		-fpermissive
		-fno-exceptions
		-Wno-write-strings
		-Wno-changes-meaning
		-Wno-attributes
		-Wno-deprecated-declarations
		-Wno-deprecated-comma-subscript
		-Wno-format
		-Wno-constant-logical-operand
	)
	target_link_libraries(${arg_LIBNAME} PUBLIC
		$<$<BOOL:${Threads_FOUND}>:Threads::Threads>
		$<${YOSYS_ENABLE_READLINE}:PkgConfig::readline>
		$<$<BOOL:${WIN32}>:-lshlwapi>
	)

	yosys_cxx_executable(${arg_EXENAME}
		OUTPUT_NAME ${arg_EXENAME}
		INCLUDE_IN_ALL_IF "${arg_INCLUDE_IN_ALL_IF}"
	)
	target_sources(${arg_EXENAME} PRIVATE ${main_source})
	target_include_directories(${arg_EXENAME} PRIVATE abc/src)
	target_link_libraries(${arg_EXENAME} PRIVATE ${arg_LIBNAME})
endfunction()
