# Helper to generate `YosysConfig.cmake`, package configuration file for a consumer to use `find_package(Yosys)`.
# Allows generating values for either `BUILD` or `INSTALL` variant.

include(CMakePackageConfigHelpers)

function(yosys_package_config variant)
	# Set paths which have different values for BUILD and INSTALL
	if (variant STREQUAL BUILD)
		set(prefix ${YOSYS_CMAKE_BINARY_DIR})
		set(dest ${YOSYS_CMAKE_BINARY_DIR})
		set(output ${YOSYS_CMAKE_BINARY_DIR})
		set(yosys_pkg_DATADIR share)
		set(yosys_pkg_BINDIR "")
	elseif (variant STREQUAL INSTALL)
		set(prefix ${CMAKE_INSTALL_PREFIX})
		set(dest ${YOSYS_INSTALL_CMAKEDIR})
		set(output ${YOSYS_CMAKE_BINARY_DIR}/CMakeFiles/YosysPackage)
		set(yosys_pkg_DATADIR ${YOSYS_INSTALL_DATADIR})
		set(yosys_pkg_BINDIR ${YOSYS_INSTALL_BINDIR})
	else ()
		message(FATAL_ERROR "Unknown variant ${variant}")
	endif()

	# ABC path depends on how it is integrated
	if (NOT YOSYS_ENABLE_ABC OR YOSYS_ABC_EXECUTABLE STREQUAL "INTEGRATED-NOTFOUND")
		# In-process
		set(yosys_pkg_ABC_EXECUTABLE "")
	elseif (YOSYS_ABC_EXECUTABLE STREQUAL "")
		# Building
		cmake_path(APPEND yosys_pkg_BINDIR "${abc_filename}" OUTPUT_VARIABLE abc_rel)
		set(yosys_pkg_ABC_EXECUTABLE "\${PACKAGE_PREFIX_DIR}/${abc_rel}")
	else ()
		# External
		set(yosys_pkg_ABC_EXECUTABLE "${YOSYS_ABC_EXECUTABLE}")
	endif ()

	# Write config file
	configure_package_config_file(${YOSYS_CMAKE_SOURCE_DIR}/cmake/YosysConfig.cmake.in
		${output}/YosysConfig.cmake
		INSTALL_PREFIX ${prefix}
		INSTALL_DESTINATION ${dest}
		PATH_VARS yosys_pkg_DATADIR
	)

	# Write version file
	write_basic_package_version_file(${output}/YosysConfigVersion.cmake
		VERSION ${YOSYS_VERSION_MAJOR}.${YOSYS_VERSION_MINOR}
		COMPATIBILITY SameMinorVersion
	)

	if (variant STREQUAL BUILD)
		export(EXPORT Yosys
			NAMESPACE Yosys::
			FILE ${output}/YosysTargets.cmake
		)
	else()
		install(EXPORT Yosys
			NAMESPACE Yosys::
			FILE YosysTargets.cmake
			DESTINATION ${dest}
		)
		install(FILES
			${output}/YosysConfig.cmake
			${output}/YosysConfigVersion.cmake
			DESTINATION ${dest}
		)
	endif()
endfunction()
