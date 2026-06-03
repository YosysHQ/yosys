set(namespace "yosys")

# Properties internal to the component system.
define_property(TARGET PROPERTY YOSYS_COMPONENT)
define_property(TARGET PROPERTY YOSYS_PROVIDES)
define_property(TARGET PROPERTY YOSYS_REQUIRES)
define_property(TARGET PROPERTY YOSYS_DATA_FILES)
define_property(TARGET PROPERTY YOSYS_ENABLE_IF)

# Syntax:
#
# 	yosys_component(<prefix> <name> [INTERFACE]
# 		[<source>...]
# 		[DEFINITIONS <definition>...]
#		[INCLUDE_DIRS <directory>...]
# 		[LIBRARIES <library>...]
# 		[PROVIDES <provided>...]
# 		[REQUIRES <required>...]
# 		[DATA_DIR <data_dir>]
#		[DATA_FILES <data_file>...]
# 		[DATA_EXPLICIT [<dest_file> <src_file>]...]
# 		[ESSENTIAL]
# 		[ENABLE_IF "<condition>"]
# 	)
#
# Creates a target `yosys_<name>` (if `<prefix>` is empty) or `yosys_<prefix>_<name>` (if `<prefix>` is not empty).
# This target is an library target with some Yosys-specific behavior that simplifies partitioning the compiler
# into small pieces with explicitly defined compile-time and run-time dependency metadata. Circular dependencies
# between compilation units in different components are allowed.
#
# Parameter description:
#  - `INTERFACE` should be specified for header-only libraries.
#  - `<source>...` is a shortcut for `target_sources(PRIVATE)`.
#  - `DEFINITIONS <definition>...` is a shortcut for `target_compile_definitions(PRIVATE)`.
#  - `INCLUDE_DIRS <directory>...` is a shortcut for `target_include_directories(PRIVATE)`.
#  - `LIBRARIES <library>...` is a shortcut for `target_link_libraries(PRIVATE)`.
#  - `PROVIDES <provided>...` creates aliases to each `<provided>` component name.
#  - `REQUIRES <required>...` ensures that if this target is linked into the Yosys binary, then every
#    `<required>` component is also linked in.
#  - `DATA_DIR <data_dir>` configures a base directory for installing data files; this directory
#    is (relative to the root build directory or the installation prefix) `share/<data_dir>` if
#    `DATA_DIR` is provided, and `share` if not.
#  - `DATA_FILES <data_file>...` installs each of `<data_file>` as `share/<data_dir>/<path>/<name>`,
#    where `<path>` is the directory name of `<data_file>` and `<name>` is the filename of `<data_file>`.
#  - `DATA_EXPLICIT [<dest_file> <src_file>]...` installs each `<src_file>` as `share/<data_dir>/<dest_file>`.
#    Where possible, `DATA_FILES` should be used instead.
#  - `ESSENTIAL` ensures that this target is always linked into the Yosys binary.
#  - `ENABLE_IF "<condition>"` marks the component as available only when `if(<condition>)` would run.
#
# Avoid using this function directly. Instead, use one of the wrappers below as follows:
#  - to define a normal pass, use `yosys_pass(<name>)` to add a component called `<name>`.
#  - to define a test pass, use `yosys_test_pass(<name>)` to add a component called `test_<name>`.
#  - to define a frontend, use `yosys_frontend(<name>)` to add a component called `read_<name>`.
#  - to define a backend, use `yosys_backend(<name>)` to add a component called `write_<name>`.
#  - if the component sources define more than one pass, use `PROVIDES` with names of the other passes.
#  - if the component uses `Pass::call()`, `Frontend::frontend_call()`, `Backend::backend_call()`, or other
#    similar functions, use `REQUIRES` with names of all possibly needed passes.
#  - if the component needs an essential pass, add the latter to `REQUIRES` anyway for completeness.
#  - if the component subclasses a `ScriptPass`, build Yosys, then run `misc/script_pass_depends.py <pass>`
#    to extract the names of all referenced passes.
#  - in general, component names should be the same as corresponding pass names (as used in the REPL),
#    but this is not a hard requirement and any suitable name can be used if desired.
#
function(yosys_component arg_PREFIX arg_NAME)
	cmake_parse_arguments(PARSE_ARGV 2 arg
		"INTERFACE;ESSENTIAL;BOOTSTRAP"
		"DATA_DIR;ENABLE_IF"
		"DEFINITIONS;INCLUDE_DIRS;LIBRARIES;DATA_FILES;DATA_EXPLICIT;PROVIDES;REQUIRES"
	)
	set(arg_SOURCES ${arg_UNPARSED_ARGUMENTS})
	if ("${arg_ENABLE_IF}" STREQUAL "")
		set(arg_ENABLE_IF TRUE)
	endif()

	if (arg_PREFIX STREQUAL "")
		set(component "${arg_NAME}")
	else()
		set(component "${arg_PREFIX}_${arg_NAME}")
	endif()
	set(target "${namespace}_${component}")
	list(TRANSFORM arg_PROVIDES PREPEND ${namespace}_ OUTPUT_VARIABLE provides_targets)

	# An OBJECT library is used to allow for circular symbol dependencies between any source files.
	# Unfortunately, public dependencies between OBJECT libraries aren't handled correctly, so we have
	# to do it ourselves.
	if (arg_SOURCES AND NOT arg_INTERFACE)
		add_library(${target} EXCLUDE_FROM_ALL OBJECT)
		target_sources(${target} PRIVATE ${arg_SOURCES})
		target_include_directories(${target} PRIVATE ${arg_INCLUDE_DIRS})
		target_compile_definitions(${target} PRIVATE ${arg_DEFINITIONS})
		target_link_libraries(${target} PUBLIC yosys_common ${arg_LIBRARIES})
		foreach (alias ${provides_targets})
			add_library(${alias} ALIAS ${target})
		endforeach()
	else()
		add_library(${target} EXCLUDE_FROM_ALL INTERFACE)
	endif()
	set_target_properties(${target} PROPERTIES
		YOSYS_COMPONENT YES
		YOSYS_PROVIDES "${arg_PROVIDES}"
		YOSYS_REQUIRES "${arg_REQUIRES}"
		YOSYS_DATA_FILES ""
		YOSYS_ENABLE_IF "${arg_ENABLE_IF}"
	)

	set(share_file_pairs)
	foreach (share_file ${arg_DATA_FILES})
		list(APPEND share_file_pairs ${share_file} ${share_file})
	endforeach()
	list(APPEND share_file_pairs ${arg_DATA_EXPLICIT})
	if (share_file_pairs)
		set(data_depends)
		set(share_root ${CMAKE_BINARY_DIR}/share)
		while (share_file_pairs)
			list(LENGTH share_file_pairs share_file_unpaired)
			if (share_file_unpaired EQUAL 1)
				message(FATAL_ERROR "Unpaired DATA_EXPLICIT argument: ${share_file_pairs}")
			endif()
			list(POP_FRONT share_file_pairs dst_file src_file)
			cmake_path(ABSOLUTE_PATH src_file BASE_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
			set(out_dir ${arg_DATA_DIR})
			cmake_path(GET dst_file PARENT_PATH dst_parent)
			cmake_path(APPEND out_dir ${dst_parent})
			cmake_path(GET dst_file FILENAME dst_filename)
			cmake_path(APPEND out_dir ${dst_filename} OUTPUT_VARIABLE out_file)
			file(MAKE_DIRECTORY ${share_root}/${out_dir})
			add_custom_command(
				DEPENDS ${src_file}
				OUTPUT ${share_root}/${out_file}
				COMMAND ${CMAKE_COMMAND} -E copy_if_different ${src_file} ${share_root}/${out_file}
				VERBATIM
				COMMENT "Copying share/${out_file}"
			)
			set_property(TARGET ${target} APPEND PROPERTY YOSYS_DATA_FILES ${out_file})
			list(APPEND data_depends ${share_root}/${out_file})
		endwhile()
		add_custom_target(${target}-data DEPENDS ${data_depends})
		add_dependencies(${target} ${target}-data)
	endif()

	if (NOT arg_BOOTSTRAP)
		set_property(TARGET yosys_everything APPEND PROPERTY YOSYS_REQUIRES ${component})
		if (arg_ESSENTIAL)
			set_property(TARGET yosys_essentials APPEND PROPERTY YOSYS_REQUIRES ${component})
		endif()
	endif()
endfunction()

# Syntax:
#
# 	yosys_core(<name> [<option>...]) →
# 		yosys_component("" <name> [<option>...])
#
# 	yosys_pass(<name> [<option>...]) →
# 		yosys_component("" <name> [<option>...])
#
# 	yosys_test_pass(<name> [<option>...]) →
# 		yosys_component("test" <name> [<option>...])
#
# 	yosys_frontend(<name> [<option>...]) →
# 		yosys_component("frontend" <name> [<option>...])
#
# 	yosys_backend(<name> [<option>...]) →
# 		yosys_component("backend" <name> [<option>...])
#
# See `yosys_component()` for details.
#
function(yosys_core)
	yosys_component("" ${ARGV})
endfunction()

function(yosys_pass)
  yosys_component("" ${ARGV})
endfunction()

function(yosys_test_pass)
	yosys_component(test ${ARGV})
endfunction()

function(yosys_frontend)
  yosys_component(read ${ARGV})
endfunction()

function(yosys_backend)
  yosys_component(write ${ARGV})
endfunction()

# Syntax:
#
# 	yosys_expand_components(<variable> <component>...)
#
# Populates `<variable>` with the list of components required for linking every `<component>`,
# sorted by pre-order traversal.
#
function(yosys_expand_components arg_OUTPUT)
	cmake_parse_arguments(PARSE_ARGV 1 arg "QUIET" "" "")
	set(arg_COMPONENTS ${arg_UNPARSED_ARGUMENTS})

	function(check_components context components)
		set(error 0)
		foreach (component ${components})
			set(target "${namespace}_${component}")
			if (NOT TARGET ${target})
				message(SEND_ERROR "${context}Target ${target} does not exist")
				set(error 1)
				continue()
			endif()
			get_target_property(target_is_component ${target} YOSYS_COMPONENT)
			if (NOT target_is_component)
				message(SEND_ERROR "${context}Target ${target} is not a Yosys component")
				set(error 1)
			endif()
		endforeach()
		return (PROPAGATE error)
	endfunction()

	function(depth_first_search component visited_components required_components)
		list(APPEND visited_components ${component})
		get_target_property(component_requires "${namespace}_${component}" YOSYS_REQUIRES)
		check_components("In REQUIRES of ${component}: " "${component_requires}")
		foreach (requirement ${component_requires})
			if (NOT requirement IN_LIST visited_components)
				depth_first_search(${requirement} "${visited_components}" "${required_components}")
			endif()
		endforeach()
		list(APPEND required_components ${component})
		return (PROPAGATE visited_components required_components)
	endfunction()

	set(visited_components)
	set(required_components)
	check_components("" "${arg_COMPONENTS}")
	foreach (component ${arg_COMPONENTS})
		if (NOT component IN_LIST visited_components)
			depth_first_search(${component} "${visited_components}" "${required_components}")
		endif()
	endforeach()

	# If `everything` is in the component list, ignore disabled dependencies, else fail the build.
	set(fail_if_disabled TRUE)
	if (everything IN_LIST arg_COMPONENTS)
		set(fail_if_disabled FALSE)
	endif()

	# ${required_components} are now sorted in pre-order (every component is visited before
	# all of its dependents). Figure out which components are enabled and which components
	# have disabled dependencies.
	set(enabled_components)
	if (NOT arg_QUIET)
		message(TRACE "Resolving component dependencies:")
	endif()
	foreach (component ${required_components})
		set(why_disabled "")
		get_target_property(component_enable_if "${namespace}_${component}" YOSYS_ENABLE_IF)
		if (${component_enable_if})
			get_target_property(component_requires "${namespace}_${component}" YOSYS_REQUIRES)
			foreach (requirement ${component_requires})
				if (NOT requirement IN_LIST enabled_components)
					set(why_disabled "dependency ${requirement}")
					break()
				endif()
			endforeach()
		else()
			set(why_disabled "condition")
		endif()
		if ("${why_disabled}" STREQUAL "")
			list(APPEND enabled_components ${component})
			if (NOT arg_QUIET)
				message(TRACE "  Component ${component} enabled")
			endif()
		else()
			if (NOT arg_QUIET)
				message(TRACE "  Component ${component} disabled (cause: ${why_disabled})")
			endif()
			if (fail_if_disabled)
				message(FATAL_ERROR "Required component ${component} is disabled (cause: ${why_disabled})")
			endif()
		endif()
	endforeach()

	set(${arg_OUTPUT} ${enabled_components})
	return(PROPAGATE ${arg_OUTPUT})
endfunction()

# Syntax:
#
# 	yosys_link_components(<target> {INTERFACE|PUBLIC|PRIVATE} <component>...)
#
# Link every `<component>` into `<target>`.
#
function(yosys_link_components arg_TARGET arg_SCOPE)
	cmake_parse_arguments(PARSE_ARGV 2 arg "" "" "")
	set(arg_COMPONENTS ${arg_UNPARSED_ARGUMENTS})

	message(VERBOSE "Components for ${arg_TARGET}: ${arg_COMPONENTS}")
	list(TRANSFORM arg_COMPONENTS PREPEND ${namespace}_ OUTPUT_VARIABLE linked_targets)
	target_link_libraries(${arg_TARGET} ${arg_SCOPE} ${linked_targets})
endfunction()

# Syntax:
#
# 	yosys_install_component_data(<component>... DESTINATION <directory>)
#
# Install data files for every `<component>` into `<directory>`.
# Equivalent to copying `${CMAKE_BINARY_DIR}/share/.` to `<directory>/.` after a clean rebuild.
#
function(yosys_install_component_data)
	cmake_parse_arguments(PARSE_ARGV 0 arg "" "DESTINATION" "")
	set(arg_COMPONENTS ${arg_UNPARSED_ARGUMENTS})
	if (NOT arg_DESTINATION)
		message(FATAL_ERROR "Missing DESTINATION argument")
	endif()

	foreach (component ${arg_COMPONENTS})
		get_target_property(data_files ${namespace}_${component} YOSYS_DATA_FILES)
		foreach (data_file ${data_files})
			cmake_path(GET data_file PARENT_PATH data_dir)
			install(FILES ${CMAKE_BINARY_DIR}/share/${data_file} DESTINATION ${arg_DESTINATION}/${data_dir})
		endforeach()
	endforeach()
endfunction()
