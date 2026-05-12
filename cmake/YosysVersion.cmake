# Syntax:
#
# 	yosys_call_git(<args>...)
#
# Calls `git <args>...` in the project source directory. Never causes errors.
#
# Defines the following variables:
#  - `git_result`: exit code
#  - `git_output`: standard output (standard error is discarded)
#
function(yosys_call_git)
	execute_process(
    COMMAND ${GIT_EXECUTABLE} ${ARGV}
		WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    RESULT_VARIABLE git_result
    OUTPUT_VARIABLE git_output
    OUTPUT_STRIP_TRAILING_WHITESPACE
    ERROR_QUIET
	)
	return(PROPAGATE git_result git_output)
endfunction()

# Syntax:
#
# 	yosys_extract_version()
#
# Defines the following variables:
#  - `YOSYS_VERSION_MAJOR`: major version number
#  - `YOSYS_VERSION_MINOR`: minor version number
#  - `YOSYS_VERSION_COMMIT`: distance since release
#  - `YOSYS_VERSION`: either `<major>.<minor>+<distance>` or `<major>.<minor>+post`
#  - `YOSYS_CHECKOUT_INFO`: either `<abbrev>`, `<abbrev>-dirty`, or `UNKNOWN`
#  - `YOSYS_ORIGIN_INFO`: either `forge.tld/repo/user at branch` or ``
#
# For builds without git, it is possible to define `-DYOSYS_CHECKOUT_INFO=` and
# `-DYOSYS_ORIGIN_INFO=` explicitly when configuring, which will be included in log output.
#
function(yosys_extract_version)
	# Version numbers are placed in an external file that can be easily rewritten.
	include(YosysVersionData)

	# Extract git metadata if possible.
	set(git_distance "")
	set(git_abbrev "")
	set(git_dirty NO)
	set(git_origin "")
	set(git_branch "")
	find_package(Git QUIET)
	if (Git_FOUND)
		yosys_call_git(rev-parse --git-dir)
		if (git_result EQUAL 0)
			set(git_dir ${git_output})
			set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS ${git_dir}/HEAD)
			file(READ ${git_dir}/HEAD git_head)
			if (git_head MATCHES "^ref: (.+)\n$")
				set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS ${git_dir}/${CMAKE_MATCH_1})
			endif()
			yosys_call_git(rev-list --count v${YOSYS_VERSION_MAJOR}.${YOSYS_VERSION_MINOR}..HEAD)
			set(git_distance ${git_output})
			yosys_call_git(rev-parse --short=9 HEAD)
			set(git_abbrev ${git_output})
			yosys_call_git(diff --exit-code --quiet)
			set(git_dirty ${git_result})
			yosys_call_git(config --get remote.origin.url)
			set(git_origin ${git_output})
			yosys_call_git(rev-parse --abbrev-ref HEAD)
			set(git_branch ${git_output})
		endif()
	endif()

	# Build YOSYS_VERSION (just the version info).
	set(YOSYS_VERSION "${YOSYS_VERSION_MAJOR}.${YOSYS_VERSION_MINOR}")
	if (git_distance STREQUAL "")
		string(APPEND YOSYS_VERSION "+post")
	else()
		set(YOSYS_VERSION_COMMIT ${git_distance})
		if (NOT git_distance EQUAL 0)
			string(APPEND YOSYS_VERSION "+${git_distance}")
		endif()
	endif()
	message(STATUS "Configuring Yosys ${YOSYS_VERSION}")

	if (NOT YOSYS_CHECKOUT_INFO)
		# Build YOSYS_CHECKOUT_INFO (git sha1 and dirty status).
		if (git_abbrev STREQUAL "")
			# No git checkout, see if the tarball was created with `git archive`.
			file(READ ${CMAKE_SOURCE_DIR}/.gitcommit git_abbrev)
			set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS ${CMAKE_SOURCE_DIR}/.gitcommit)
			string(STRIP "${git_abbrev}" git_abbrev)
			if (git_abbrev MATCHES "Format:")
				# No substitutions, we're out of options.
				set(YOSYS_CHECKOUT_INFO UNKNOWN)
			else()
				# Substitutions were made, good.
				set(YOSYS_CHECKOUT_INFO ${git_abbrev})
			endif()
		else()
			# Valid git checkout, use accurate information.
			set(YOSYS_CHECKOUT_INFO ${git_abbrev})
			if (git_dirty)
				string(APPEND YOSYS_CHECKOUT_INFO "-dirty")
			endif()
		endif()
	endif()

	if (NOT YOSYS_ORIGIN_INFO)
		# Build YOSYS_ORIGIN_INFO (git repository origin and branch)
		if (git_origin AND git_branch)
			string(REGEX REPLACE "^https://|.git$" "" git_origin ${git_origin})
			if (git_origin STREQUAL "github.com/YosysHQ/yosys" AND git_branch MATCHES "^HEAD|main|release/v.+$")
				# Nothing to highlight.
				set(YOSYS_ORIGIN_INFO "")
			else()
				# Highlight clone URL and branch.
				set(YOSYS_ORIGIN_INFO "${git_origin} at ${git_branch}")
			endif()
		endif()
	endif()

	if (YOSYS_ORIGIN_INFO)
		message(STATUS "Git commit ${YOSYS_CHECKOUT_INFO} from ${YOSYS_ORIGIN_INFO}")
	else()
		message(STATUS "Git commit ${YOSYS_CHECKOUT_INFO}")
	endif()

	return(PROPAGATE
		YOSYS_VERSION_MAJOR
		YOSYS_VERSION_MINOR
		YOSYS_VERSION_COMMIT
		YOSYS_VERSION
		YOSYS_CHECKOUT_INFO
		YOSYS_ORIGIN_INFO
	)
endfunction()

# Syntax:
#
# 	yosys_version_file(<input> <output>)
#
# Templates `<output>` file based on `<input>` with the following substitutions:
#  - `@YOSYS_VERSION@`: version in `<major>.<minor>+<post>` format
#  - `@YOSYS_BUILD_INFO@`: free-form build information
#    (not actually entirely free-form as external software tries to parse it sometimes)
#
# Must have executed `yosys_extract_version()` first.
#
function(yosys_version_file arg_INPUT arg_OUTPUT)
	set(YOSYS_BUILD_INFO "Yosys")
	string(APPEND YOSYS_BUILD_INFO " ${YOSYS_VERSION}")
	string(APPEND YOSYS_BUILD_INFO " (git sha1 ${YOSYS_CHECKOUT_INFO},")
	if (CMAKE_BUILD_TYPE)
		string(APPEND YOSYS_BUILD_INFO " ${CMAKE_BUILD_TYPE},")
	endif()
	string(APPEND YOSYS_BUILD_INFO " ${CMAKE_CXX_COMPILER_ID}")
	string(APPEND YOSYS_BUILD_INFO " ${CMAKE_CXX_COMPILER}")
	string(APPEND YOSYS_BUILD_INFO " ${CMAKE_CXX_COMPILER_VERSION})")
	if (YOSYS_ORIGIN_INFO)
		string(APPEND YOSYS_BUILD_INFO " [${YOSYS_ORIGIN_INFO}]")
	endif()

	configure_file(${arg_INPUT} ${arg_OUTPUT} @ONLY)
endfunction()
