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

	set(link_flags)
	if (scope STREQUAL BUILD OR YOSYS_INSTALL_LIBRARY)
		set(link_flags -L${LIBDIR})
	endif()

	set(platform_link_flags)
	set(platform_libs)
	if (CMAKE_SYSTEM_NAME STREQUAL "Darwin")
		set(platform_link_flags -undefined dynamic_lookup)
	endif()
	if (MINGW)
		set(platform_libs -l:yosys.exe.a)
	endif()
	if (MINGW AND YOSYS_INSTALL_DRIVER)
		set(platform_link_flags -L${LIBDIR})
	endif()

	set(CXX ${CMAKE_CXX_COMPILER})
	string(JOIN " " CXXFLAGS
		-std=c++${CMAKE_CXX_STANDARD}
		${CMAKE_CXX_FLAGS}
		${CMAKE_CXX_COMPILE_OPTIONS_PIC}
		-D_YOSYS_
		"-DYOSYS_VER=\"${YOSYS_VERSION}\""
		"-DYOSYS_MAJOR=${YOSYS_VERSION_MAJOR}"
		"-DYOSYS_MINOR=${YOSYS_VERSION_MINOR}"
		"-DYOSYS_COMMIT=${YOSYS_VERSION_COMMIT}"
		-I${DATDIR}/include
	)
	string(JOIN " " LINKFLAGS
		${CMAKE_SHARED_LIBRARY_CXX_FLAGS}
		${link_flags}
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
		install(PROGRAMS ${CMAKE_BINARY_DIR}/${YOSYS_PROGRAM_PREFIX}yosys-config.install
			RENAME yosys-config
			DESTINATION ${YOSYS_INSTALL_BINDIR}
		)
	endif()
endfunction()
