# Syntax:
#
# 	use_homebrew([ROOT <root>])
#
# Includes all packages installed in `<root>` (output of brew --prefix if not
# specified) in `CMAKE_FIND_ROOT_PATH`.
#
function(use_homebrew)
	cmake_parse_arguments(PARSE_ARGV 0 arg "" "ROOT" "")
	if (NOT arg_ROOT)
		execute_process(
			COMMAND brew --prefix
			WORKING_DIRECTORY ${YOSYS_CMAKE_SOURCE_DIR}
			RESULT_VARIABLE brew_prefix_result
			OUTPUT_VARIABLE brew_prefix_out
			OUTPUT_STRIP_TRAILING_WHITESPACE
			ERROR_QUIET
		)
		if (${brew_prefix_result} EQUAL 0)
			set (arg_ROOT "${brew_prefix_out}/Cellar")
		endif()
	endif()

	if (NOT arg_ROOT)
		# unset and no brew binary available
		return()
	endif()

	file(GLOB package_roots ${arg_ROOT}/*/*) # e.g. `/opt/homebrew/Cellar/bison/3.8.2/`
	foreach (package_root ${package_roots})
		if (IS_DIRECTORY ${package_root})
			list(APPEND CMAKE_FIND_ROOT_PATH ${package_root})
		endif()
	endforeach()

	return(PROPAGATE CMAKE_FIND_ROOT_PATH)
endfunction()
