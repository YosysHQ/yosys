# Syntax:
#
# 	use_homebrew([ROOT <root>])
#
# Includes all packages installed in `<root>` (`/opt/homebrew/Cellar` if not specified)
# in `CMAKE_FIND_ROOT_PATH`.
#
function(use_homebrew)
	cmake_parse_arguments(PARSE_ARGV 0 arg "" "ROOT" "")
	if (NOT arg_ROOT)
		set(arg_ROOT /opt/homebrew/Cellar)
	endif()

	file(GLOB package_roots ${arg_ROOT}/*/*) # e.g. `/opt/homebrew/Cellar/bison/3.8.2/`
	foreach (package_root ${package_roots})
		if (IS_DIRECTORY ${package_root})
			list(APPEND CMAKE_FIND_ROOT_PATH ${package_root})
		endif()
	endforeach()

	return(PROPAGATE CMAKE_FIND_ROOT_PATH)
endfunction()
