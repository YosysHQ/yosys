# depends on YosysVersion.cmake

function(yosys_check_abc_submodule)
	yosys_call_git(status)
	set(yosys_status "tarball")
	if (git_result EQUAL 0)
		set(yosys_status "git")
	endif()

	yosys_call_git(submodule status abc)
	set(git_commit)
	if (EXISTS "${CMAKE_SOURCE_DIR}/abc/.gitcommit")
		file(READ "${CMAKE_SOURCE_DIR}/abc/.gitcommit" git_commit)
		string(STRIP "${git_commit}" git_commit)
	endif()
	set(abc_status "none")
	if (git_result EQUAL 0 AND git_output MATCHES "^ ")
		set(abc_status "git")
	elseif (git_result EQUAL 0 AND git_output MATCHES "^\\+")
		set(abc_status "git-changed")
	elseif (git_result EQUAL 0 AND git_output MATCHES "^U")
		set(abc_status "git-conflict")
	elseif (git_commit MATCHES "^[0-9a-fA-F]+$")
		set(abc_status "tarball")
	elseif (git_commit MATCHES "\\$Format:%[hH]\\$")
		set(abc_status "unknown")
	endif()

	if (abc_status STREQUAL "git" OR abc_status STREQUAL "tarball")
		# Normal submodule or a tarball.
	elseif (abc_status STREQUAL "git-changed")
		message(FATAL_ERROR
			"'abc' submodule does not match expected commit.\n"
			"Run 'git submodule update' to check out the correct version.\n"
			"Note: If testing a different version of ABC, call 'git commit abc' "
			"in the Yosys source directory to update the expected commit.\n"
		)
	elseif (abc_status STREQUAL "git-conflict")
		message(FATAL_ERROR
			"'abc' submodule has merge conflicts.\n"
			"Please resolve merge conflicts before continuing.\n"
		)
	elseif (abc_status STREQUAL "unknown") # OK
		message(FATAL_ERROR
			"Error: 'abc' is not configured as a git submodule.\n"
			"To resolve this:\n"
			"1. Back up your changes: Save any modifications from the 'abc' directory to another location.\n"
			"2. Remove the existing 'abc' directory: Delete the 'abc' directory and all its contents.\n"
			"3. Initialize the submodule: Run 'git submodule update --init' to set up 'abc' as a submodule.\n"
			"4. Reapply your changes: Move your saved changes back to the 'abc' directory, if necessary.\n"
		)
	elseif (yosys_status STREQUAL "git") # OK
		message(FATAL_ERROR
			"Initialize the submodule: Run 'git submodule update --init' to set up 'abc' as a submodule.\n"
		)
	else() #
		message(FATAL_ERROR
			"${CMAKE_SOURCE_DIR} is not configured as a git repository, and 'abc' folder is missing.\n"
			"If you already have ABC, set 'YOSYS_ABC_EXECUTABLE' CMake variable to point to ABC executable.\n"
			"Otherwise, download release archive 'yosys.tar.gz' from https://github.com/YosysHQ/yosys/releases.\n"
			"    ('Source code' archive does not contain submodules.)\n"
		)
	endif()
endfunction()
