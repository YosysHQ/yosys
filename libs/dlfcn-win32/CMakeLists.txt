if (WIN32 OR MSYS)
	add_library(dlfcn STATIC EXCLUDE_FROM_ALL
		dlfcn.cc
		dlfcn.h
	)
	target_include_directories(dlfcn PUBLIC
		${CMAKE_CURRENT_SOURCE_DIR}
	)
endif()
