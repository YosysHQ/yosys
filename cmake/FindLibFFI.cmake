#
#	CMake Find Foreing Function Interface library by Parra Studios
#	CMake script to find FFI library.
#
#	Copyright (C) 2016 - 2024 Vicente Eduardo Ferrer Garcia <vic798@gmail.com>
#
#	Licensed under the Apache License, Version 2.0 (the "License");
#	you may not use this file except in compliance with the License.
#	You may obtain a copy of the License at
#
#		http://www.apache.org/licenses/LICENSE-2.0
#
#	Unless required by applicable law or agreed to in writing, software
#	distributed under the License is distributed on an "AS IS" BASIS,
#	WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#	See the License for the specific language governing permissions and
#	limitations under the License.
#

# Find FFI library and include paths
#
# LIBFFI_FOUND - True if FFI library was found
# LIBFFI_INCLUDE_DIR - FFI headers path
# LIBFFI_LIBRARY - List of FFI libraries

# Prevent vervosity if already included
if(LIBFFI_INCLUDE_DIRS)
	set(LIBFFI_FIND_QUITELY TRUE)
endif()

include(FindPackageHandleStandardArgs)

set(LIBFFI_SUFFIXES
	ffi
	x86_64-linux-gnu
	aarch64-linux-gnu
	arm-linux-gnueabi
	arm-linux-gnueabihf
	i386-linux-gnu
	mips64el-linux-gnuabi64
	mipsel-linux-gnu
	powerpc64le-linux-gnu
	s390x-linux-gnu
)

find_library(LIBFFI_LIBRARY
	NAMES ffi libffi
	PATHS /usr /usr/lib /usr/local /opt/local
	PATH_SUFFIXES lib lib64 ${LIBFFI_SUFFIXES}
)

if(APPLE)
	execute_process(COMMAND brew --prefix libffi OUTPUT_VARIABLE LIBFFI_PREFIXES)
else()
	# TODO: Windows?
	set(LIBFFI_PREFIXES)
endif()

if(NOT LIBFFI_INCLUDE_DIR)
	find_path(LIBFFI_INCLUDE_DIR ffi.h
		PATHS /usr /usr/include /usr/local /opt/local /usr/include/ffi
		PATH_SUFFIXES ${LIBFFI_SUFFIXES}
		HINT LIBFFI_PREFIXES
	)
endif()

# Try to load by using PkgConfig
if(NOT LIBFFI_LIBRARY OR NOT LIBFFI_INCLUDE_DIR)
	# Find package configuration module
	find_package(PkgConfig)

	# Find module
	pkg_check_modules(PC_LIBFFI QUIET libffi)

	# Find include path
	find_path(LIBFFI_INCLUDE_DIR ffi.h HINTS ${PC_LIBFFI_INCLUDEDIR} ${PC_LIBFFI_INCLUDE_DIRS})

	# Find library
	find_library(LIBFFI_LIBRARY NAMES ffi HINTS ${PC_LIBFFI_LIBDIR} ${PC_LIBFFI_LIBRARY_DIRS})
endif()

# Define FFI cmake module
find_package_handle_standard_args(LibFFI DEFAULT_MSG LIBFFI_LIBRARY LIBFFI_INCLUDE_DIR)

# Mark cmake module as advanced
mark_as_advanced(LIBFFI_INCLUDE_DIR LIBFFI_LIBRARY)
