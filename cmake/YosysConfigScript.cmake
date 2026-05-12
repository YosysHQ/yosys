# Syntax:
#
# 	yosys_config_script({BUILD|INSTALL})
#
# Generates a `yosys-config` executable with embedded paths for in-tree builds or after installation.
#
function(yosys_config_script scope)
	if (scope STREQUAL BUILD)
		set(BINDIR ${CMAKE_BINARY_DIR})
		set(LIBDIR ${CMAKE_BINARY_DIR})
		set(DATDIR ${CMAKE_BINARY_DIR}/share)
		set(suffix "")
	elseif (scope STREQUAL INSTALL)
		set(BINDIR ${YOSYS_INSTALL_FULL_BINDIR})
		set(LIBDIR ${YOSYS_INSTALL_FULL_LIBDIR})
		set(DATDIR ${YOSYS_INSTALL_FULL_DATADIR})
		set(suffix ".install")
	else()
		message(FATAL_ERROR "Invalid scope ${scope}")
	endif()

	set(platform_link_flags)
	set(platform_libs)
	if (CMAKE_SYSTEM_NAME STREQUAL "Darwin")
		set(platform_link_flags -undefined dynamic_lookup)
	endif()
	if (MINGW)
		set(platform_libs yosys.exe.a)
	endif()

	set(CXX ${CMAKE_CXX_COMPILER})
	string(JOIN " " CXXFLAGS
		${CMAKE_CXX_FLAGS}
		${CMAKE_CXX_COMPILE_OPTIONS_PIC}
		${yosys_core_definitions}
		${yosys_version_definitions}
		-I${DATDIR}/include
	)
	string(JOIN " " LINKFLAGS
		${CMAKE_SHARED_LIBRARY_CXX_FLAGS}
		-L${LIBDIR}
		${platform_link_flags}
	)
	string(JOIN " " LIBS
		${platform_libs}
	)
	configure_file(${CMAKE_SOURCE_DIR}/misc/yosys-config.in
		${YOSYS_PROGRAM_PREFIX}yosys-config${suffix}
		USE_SOURCE_PERMISSIONS
		@ONLY
	)
	if (scope STREQUAL INSTALL)
		install(PROGRAMS ${CMAKE_BINARY_DIR}/${YOSYS_PROGRAM_PREFIX}yosys-config
			DESTINATION ${YOSYS_INSTALL_BINDIR})
	endif()
endfunction()
