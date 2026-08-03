# Syntax:
#
# 	pkg_config_import(<package>)
#
# To use this command, `find_package(PkgConfig)` must be used beforehand, but it does
# not have to succeed. If the `PkgConfig` package is not found, all imports silently fail.
#
# Imports `<package>` as a CMake `IMPORTED` target `PkgConfig::<package>`.
# Updates the global `PACKAGES_FOUND` and `PACKAGES_NOT_FOUND` properties and defines
# the `<package>_FOUND` variable.
#
function(pkg_config_import arg_PREFIX)
	cmake_parse_arguments(PARSE_ARGV 1 arg "" "" "MODULES")
	if (NOT arg_MODULES)
		set(arg_MODULES ${arg_PREFIX})
	endif()

	if (PkgConfig_FOUND)
		# Once CMake 4.1 is available, this call should be replaced with `cmake_pkg_config()`.
		pkg_check_modules(${arg_PREFIX} IMPORTED_TARGET ${arg_MODULES})
		if (${arg_PREFIX}_FOUND)
			# We found the pkgconfig file, but is it actually a usable package?
			# The main cause of failure here would be cross-compiling, which pkg-config does not
			# handle very well (especially pre-`cmake_pkg_config()`).
			try_compile(is_usable
				SOURCE_FROM_CONTENT "main.cc" "int main() {}"
				LINK_LIBRARIES PkgConfig::${arg_PREFIX}
				LOG_DESCRIPTION "Checking if PkgConfig::${arg_PREFIX} is usable"
			)
			if (NOT is_usable)
				message(STATUS "Modules '${arg_MODULES}' unusable (bad \$PKG_CONFIG_LIBDIR?)")
				set(${arg_PREFIX}_FOUND 0)
			endif()
		endif()
	endif()

	if (${arg_PREFIX}_FOUND)
		set_property(GLOBAL APPEND PROPERTY PACKAGES_FOUND ${arg_PREFIX})
	else()
		set_property(GLOBAL APPEND PROPERTY PACKAGES_NOT_FOUND ${arg_PREFIX})
	endif()
	return (PROPAGATE ${arg_PREFIX}_FOUND)
endfunction()
