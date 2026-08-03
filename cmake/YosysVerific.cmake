if (APPLE)
	set(VERIFIC_LIB_SUFFIX -mac.a)
elseif (LINUX)
	set(VERIFIC_LIB_SUFFIX -linux.a)
elseif (WIN32)
	set(VERIFIC_LIB_SUFFIX -windows.a)
else()
	set(VERIFIC_LIB_SUFFIX -NOTFOUND)
endif()

# Syntax:
#
# 	get_verific_components(<result>)
#
# Assigns variable `<result>` to a list of Verific components detected in `${YOSYS_VERIFIC_DIR}`.
#
function(get_verific_components result)
	file(GLOB libraries
		RELATIVE ${YOSYS_VERIFIC_DIR}
		${YOSYS_VERIFIC_DIR}/*/*${VERIFIC_LIB_SUFFIX}
	)
	set(components)
	foreach (library ${libraries})
		cmake_path(GET library PARENT_PATH component)
		list(APPEND components ${component})
	endforeach()

	# Always remove TCL command interface
	list(REMOVE_ITEM components commands)

	set(${result} ${components})
	return(PROPAGATE ${result})
endfunction()

# Syntax:
#
# 	get_verific_options(<include_dirs> <libraries> <components>...)
#
# Assigns variables `<include_dirs>` and `<libraries>` to lists required to use Verific
# `<components>`.
#
function(get_verific_options include_dirs libraries)
	set(${include_dirs})
	set(${libraries})
	foreach (component ${ARGN})
		list(APPEND ${include_dirs} ${YOSYS_VERIFIC_DIR}/${component})
		list(APPEND ${libraries} ${YOSYS_VERIFIC_DIR}/${component}/${component}${VERIFIC_LIB_SUFFIX})
	endforeach()

	return(PROPAGATE ${include_dirs} ${libraries})
endfunction()
