include(CMakePushCheckState)
include(CheckCXXSymbolExists)
include(FindPackageHandleStandardArgs)

if (WIN32 OR MSYS)
	# Windows; dlopen is available via a polyfill `libs/dlfcn-win32`.
	set(Dlfcn_LIBRARIES dlfcn)
else()
	# Unix and Wasm; dlopen may or may not be available depending on platform.
	cmake_push_check_state(RESET)
		set(CMAKE_REQUIRED_LIBRARIES ${CMAKE_DL_LIBS})
		check_cxx_symbol_exists(dlopen "dlfcn.h" HAVE_DLOPEN)
	cmake_pop_check_state()

	if (HAVE_DLOPEN)
		add_library(dlfcn INTERFACE)
		target_link_libraries(dlfcn INTERFACE ${CMAKE_DL_LIBS})
		set(Dlfcn_LIBRARIES dlfcn)
	endif()
endif()

find_package_handle_standard_args(Dlfcn
  REQUIRED_VARS Dlfcn_LIBRARIES
)
