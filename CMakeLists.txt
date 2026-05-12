cmake_minimum_required(VERSION 3.27)
project(yosys C CXX)

set(CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake" ${CMAKE_MODULE_PATH})
include(CMakeDependentOption)
include(FeatureSummary)
include(Condition)
include(CheckLibcFeatures)
include(PkgConfig)
include(PmgenCommand)
include(YosysVersion)
include(YosysInstallDirs)
include(YosysConfigScript)
include(YosysComponent)
include(YosysLinkTarget)
include(YosysAbc)

# Build options.
set(YOSYS_COMPILER_LAUNCHER "" CACHE STRING "Compiler launcher (ccache, sccache)")
option(YOSYS_ENABLE_COVERAGE "Enable code coverage" OFF)
option(YOSYS_ENABLE_PROFILING "Enable instruction profiling" OFF)

set(YOSYS_PROGRAM_PREFIX "" CACHE STRING "Name prefix for programs, libraries, and data")
set(YOSYS_COMPONENTS "everything" CACHE STRING "List of components to build (use pass names)")
set(YOSYS_ABC_EXECUTABLE "" CACHE FILEPATH
	"Path to the ABC executable (empty for vendored, 'INTEGRATED-NOTFOUND' for in-process)")

option(YOSYS_DISABLE_THREADS "Disable threading" OFF)
option(YOSYS_WITHOUT_ABC "Disable ABC support (not recommended)" OFF)
option(YOSYS_WITHOUT_ZLIB "Disable zlib integration" OFF)
option(YOSYS_WITHOUT_LIBFFI "Disable libffi integration" OFF)
option(YOSYS_WITHOUT_READLINE "Disable readline integration" OFF)
option(YOSYS_WITHOUT_EDITLINE "Disable editline integration" OFF)
option(YOSYS_WITHOUT_TCL "Disable Tcl integration" OFF)
option(YOSYS_WITH_PYTHON "Enable Python integration" OFF)

option(YOSYS_INSTALL_DRIVER "Install Yosys executable" ON)
option(YOSYS_INSTALL_LIBRARY "Install libyosys library" OFF)
option(BUILD_SHARED_LIBS "Build libyosys as a shared library" ON)
cmake_dependent_option(YOSYS_INSTALL_PYTHON "Install Python extension module" OFF YOSYS_WITH_PYTHON OFF)

# Configure compiler.
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED YES)

if (CMAKE_SYSTEM_NAME STREQUAL "WASI")
	add_compile_options(
		-fwasm-exceptions -mllvm -wasm-use-legacy-eh=false
		-D_WASI_EMULATED_PROCESS_CLOCKS
	)
	add_link_options(
		-fwasm-exceptions -mllvm -wasm-use-legacy-eh=false -lunwind
		-lwasi-emulated-process-clocks
		-Wl,-z,stack-size=1048576
	)
endif()

set(CMAKE_C_COMPILER_LAUNCHER "${YOSYS_COMPILER_LAUNCHER}")
set(CMAKE_CXX_COMPILER_LAUNCHER "${YOSYS_COMPILER_LAUNCHER}")

if (YOSYS_ENABLE_COVERAGE)
	if (CMAKE_CXX_COMPILER_ID MATCHES "GNU")
		set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} --coverage")
	else()
		message(FATAL_ERROR "Code coverage is not supported on ${CMAKE_CXX_COMPILER_ID} compiler")
	endif()
endif()

if (YOSYS_ENABLE_PROFILING)
	if (CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
		set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pg")
	else()
		message(FATAL_ERROR "Instruction profiling is not supported on ${CMAKE_CXX_COMPILER_ID} compiler")
	endif()
endif()

if (CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
	set(CMAKE_CXX_FLAGS_DEBUG "-Og -ggdb")
	set(CMAKE_CXX_FLAGS_RELEASE "-O3")
	set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O3 -ggdb")
	set(CMAKE_CXX_FLAGS_MINSIZEREL "-Os")
elseif (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
	set(CMAKE_CXX_FLAGS_DEBUG "/Od /DEBUG")
	set(CMAKE_CXX_FLAGS_RELEASE "/O2")
	set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "/O2 /DEBUG")
	set(CMAKE_CXX_FLAGS_MINSIZEREL "/Os")
	add_definitions(-D_CRT_SECURE_NO_WARNINGS)
else()
	# We have to do this because CMake adds `-DNDEBUG` in release builds by default, and there's
	# no particularly good way to prevent this without also erasing optimization flags.
	# If you see this message, reproduce the block above with the flags supported by your compiler.
	message(FATAL_ERROR "${CMAKE_CXX_COMPILER_ID} compiler is not supported")
endif()

if (NOT CMAKE_C_COMPILER_ID STREQUAL CMAKE_CXX_COMPILER_ID)
	message(FATAL_ERROR "C and C++ compilers must be provided by the same vendor")
endif()
set(CMAKE_C_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG}")
set(CMAKE_C_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE}")
set(CMAKE_C_FLAGS_RELWITHDEBINFO "${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")
set(CMAKE_C_FLAGS_MINSIZEREL "${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")

if (MINGW AND CMAKE_CXX_COMPILER_ID STREQUAL "GNU" AND CMAKE_CXX_COMPILER_VERSION VERSION_LESS "16.0.0")
	# GCC 15.2 refuses to construct an import directory for yosys.exe/libyosys.dll with:
	#   .../ld.exe: error: export ordinal too large: 67035
	# The cause is unknown.
	message(WARNING "MinGW GCC is supported starting with version 16.0.0")
endif()

# Required dependencies.
find_package(FLEX)
set_package_properties(FLEX PROPERTIES
	URL "https://github.com/westes/flex"
	DESCRIPTION "The Fast Lexical Analyzer"
	PURPOSE "Compiling the Verilog lexer"
	TYPE REQUIRED
)

find_package(BISON)
set_package_properties(BISON PROPERTIES
	URL "https://www.gnu.org/software/bison/"
	DESCRIPTION "The Yacc-compatible Parser Generator"
	PURPOSE "Compiling the Verilog parser"
	TYPE REQUIRED
)

find_package(Python3 3.7 COMPONENTS Interpreter)
set_package_properties(Python3 PROPERTIES
	URL "https://www.python.org/"
	DESCRIPTION "Dynamic programming language (Interpreter)"
	PURPOSE "Generating data files\n   Running external SMT2 solvers"
	TYPE REQUIRED
)

# Optional dependencies.
check_glob()
check_system()
check_popen()
find_package(Threads QUIET)
check_pthread_create()
find_package(Dlfcn QUIET)

find_package(PkgConfig)
set_package_properties(PkgConfig PROPERTIES
	URL "https://www.freedesktop.org/wiki/Software/pkg-config/"
	DESCRIPTION "Library metadata manager"
	PURPOSE "Discovering dependencies"
	TYPE RECOMMENDED
)

pkg_config_import(zlib)
set_package_properties(zlib PROPERTIES
	URL "https://github.com/madler/zlib"
	DESCRIPTION "A massively spiffy yet delicately unobtrusive compression library"
	PURPOSE "Handling Gzip and FST file formats"
)

pkg_config_import(libffi)
set_package_properties(libffi PROPERTIES
	URL "https://sourceware.org/libffi/"
	DESCRIPTION "A Portable Foreign Function Interface Library"
	PURPOSE "Implementing Verilog DPI-C"
)

pkg_config_import(editline MODULES libedit)
set_package_properties(editline PROPERTIES
	URL "https://www.thrysoee.dk/editline/"
	DESCRIPTION "Line editing and history library (BSD)"
	PURPOSE "Enhancing the command prompt"
	TYPE RECOMMENDED
)

pkg_config_import(readline)
set_package_properties(readline PROPERTIES
	URL "https://tiswww.case.edu/php/chet/readline/rltop.html"
	DESCRIPTION "Line editing and history library (GPL)"
	PURPOSE "Enhancing the command prompt"
	TYPE RECOMMENDED
)

# See https://core.tcl-lang.org/tips/doc/trunk/tip/538.md
pkg_config_import(tcl MODULES tcl)
set_package_properties(tcl PROPERTIES
	URL "https://www.tcl-lang.org/"
	DESCRIPTION "Dynamic programming language"
	PURPOSE "Parsing SDC constraint files\n   Binding Yosys API"
)

if (tcl_FOUND)
	get_target_property(tcl_options PkgConfig::tcl INTERFACE_COMPILE_OPTIONS)
	if (tcl_options MATCHES "TCL_WITH_EXTERNAL_TOMMATH")
		pkg_config_import(libtommath)
		set_package_properties(libtommath PROPERTIES
			URL "https://www.libtom.net/LibTomMath/"
			DESCRIPTION "Multiple-precision integer library"
			PURPOSE "Required by this build of Tcl"
			TYPE REQUIRED
		)
		# Unfortunately the pkg-config file for Tcl includes libtommath as a private dependency,
		# while it should be public since it is exposed in the public API and necessary for its use.
		target_link_libraries(PkgConfig::tcl INTERFACE PkgConfig::libtommath)
	else()
		# Vendored within Tcl itself.
		set(libtommath_FOUND TRUE)
	endif()
endif()

if (YOSYS_WITH_PYTHON)
	find_package(Python3Embed REQUIRED)
	set_property(GLOBAL PROPERTY _CMAKE_Python3Embed_REQUIRED_VERSION "== ${Python3_VERSION}")
	set_package_properties(Python3Embed PROPERTIES
		URL "https://www.python.org/"
		DESCRIPTION "Dynamic programming language (Embedding)"
		PURPOSE "Binding Yosys API"
	)

	find_package(PyosysEnv REQUIRED)
	set_package_properties(PyosysEnv PROPERTIES
		DESCRIPTION "Pyosys wrapper generator environment"
		PURPOSE "Either 'uv' or 'pybind11>3,<4 cxxheaderparser'"
	)
endif()

find_package(GTest)
set_package_properties(GTest PROPERTIES
	URL "https://google.github.io/googletest/"
	DESCRIPTION "C++ testing and mocking framework by Google"
	PURPOSE "Running unit tests"
	TYPE RECOMMENDED
)

# Configure features based on dependency availability.
message(VERBOSE "Conditional features:")
condition(YOSYS_ENABLE_GLOB HAVE_GLOB)
condition(YOSYS_ENABLE_SPAWN HAVE_SYSTEM AND HAVE_POPEN)
condition(YOSYS_ENABLE_THREADS Threads_FOUND AND HAVE_PTHREAD_CREATE AND NOT YOSYS_DISABLE_THREADS)
condition(YOSYS_ENABLE_PLUGINS Dlfcn_FOUND)
condition(YOSYS_ENABLE_ABC NOT YOSYS_WITHOUT_ABC)
condition(YOSYS_ENABLE_ZLIB zlib_FOUND AND NOT YOSYS_WITHOUT_ZLIB)
condition(YOSYS_ENABLE_LIBFFI Dlfcn_FOUND AND libffi_FOUND AND NOT YOSYS_WITHOUT_LIBFFI)
condition(YOSYS_ENABLE_READLINE readline_FOUND AND NOT YOSYS_WITHOUT_READLINE)
condition(YOSYS_ENABLE_EDITLINE editline_FOUND AND NOT YOSYS_WITHOUT_EDITLINE AND NOT YOSYS_ENABLE_READLINE)
condition(YOSYS_ENABLE_TCL tcl_FOUND AND libtommath_FOUND AND NOT YOSYS_WITHOUT_TCL)
condition(YOSYS_ENABLE_PYTHON Python3Embed_FOUND AND PyosysEnv_FOUND AND YOSYS_WITH_PYTHON)

# Describe dependencies and features
# CMake 4.0 would let us use proper conditions, but that's too new for now.
add_feature_info(have_glob YOSYS_ENABLE_GLOB "Glob expansion in filenames")
add_feature_info(have_spawn YOSYS_ENABLE_SPAWN "Passes that invoke external tools")
add_feature_info(have_threads YOSYS_ENABLE_THREADS "Multithreaded netlist operations")
add_feature_info(have_plugins YOSYS_ENABLE_PLUGINS "Dynamically loadable binary plugins")
add_feature_info(with_abc YOSYS_ENABLE_ABC "Production-quality logic synthesis flow")
add_feature_info(with_zlib YOSYS_ENABLE_ZLIB "Transparent Gzip decompression and FST file format support")
add_feature_info(with_libffi YOSYS_ENABLE_LIBFFI "Verilog DPI-C foreign function interface")
add_feature_info(with_readline YOSYS_ENABLE_READLINE "Using readline for prompt editing and history")
add_feature_info(with_editline YOSYS_ENABLE_EDITLINE "Using editline for prompt editing and history")
add_feature_info(with_tcl YOSYS_ENABLE_TCL "Tcl scripting and SDC parsing")
add_feature_info(with_python YOSYS_ENABLE_PYTHON "Python scripting and embedding")
message(STATUS "")
feature_summary(WHAT PACKAGES_FOUND
	DEFAULT_DESCRIPTION)
feature_summary(WHAT REQUIRED_PACKAGES_NOT_FOUND
	DEFAULT_DESCRIPTION QUIET_ON_EMPTY FATAL_ON_MISSING_REQUIRED_PACKAGES
)
feature_summary(WHAT PACKAGES_NOT_FOUND
	DEFAULT_DESCRIPTION QUIET_ON_EMPTY
)
feature_summary(WHAT ENABLED_FEATURES
	DEFAULT_DESCRIPTION QUIET_ON_EMPTY)
feature_summary(WHAT DISABLED_FEATURES
	DEFAULT_DESCRIPTION QUIET_ON_EMPTY)

if (YOSYS_ENABLE_ABC AND NOT YOSYS_ENABLE_SPAWN AND NOT YOSYS_ABC_EXECUTABLE STREQUAL "INTEGRATED-NOTFOUND")
	message(WARNING "ABC support on this platform forces -DYOSYS_ABC_EXECUTABLE=INTEGRATED-NOTFOUND")
	set(YOSYS_ABC_EXECUTABLE "INTEGRATED-NOTFOUND" CACHE FILEPATH "" FORCE)
endif()

set(YOSYS_LINK_ABC 0)
if (YOSYS_ENABLE_ABC)
	if (YOSYS_ABC_EXECUTABLE STREQUAL "INTEGRATED-NOTFOUND")
		set(YOSYS_LINK_ABC 1)
		message(STATUS "Building ABC: (integrated)")
	elseif (YOSYS_ABC_EXECUTABLE STREQUAL "")
		set(abc_filename ${YOSYS_PROGRAM_PREFIX}yosys-abc${CMAKE_EXECUTABLE_SUFFIX})
		message(STATUS "Building ABC: ${YOSYS_INSTALL_FULL_BINDIR}/${abc_filename}")
	else()
		message(STATUS "External ABC: ${YOSYS_ABC_EXECUTABLE}")
	endif()
endif()

# Ensure invalid dependencies fail at configuration time.
set(CMAKE_LINK_LIBRARIES_ONLY_TARGETS ON)

# Configure compiler flags.
set(CMAKE_POSITION_INDEPENDENT_CODE ON)
set(yosys_core_definitions -D_YOSYS_)
if (CMAKE_BUILD_TYPE MATCHES "^Debug|RelWithDebInfo$")
	list(APPEND yosys_core_definitions -DDEBUG)
endif()

# Determine project version.
yosys_extract_version()
set(yosys_version_definitions
	"-DYOSYS_VER=\"${YOSYS_VERSION}\""
	"-DYOSYS_MAJOR=${YOSYS_VERSION_MAJOR}"
	"-DYOSYS_MINOR=${YOSYS_VERSION_MINOR}"
	"-DYOSYS_COMMIT=${YOSYS_VERSION_COMMIT}"
)

# Pseudo-library that injects common compilation options into every Yosys component.
add_library(yosys_common INTERFACE)
target_compile_definitions(yosys_common INTERFACE
	${yosys_core_definitions}
)
target_include_directories(yosys_common INTERFACE
	${CMAKE_SOURCE_DIR}
	${CMAKE_BINARY_DIR}
)

# Two pseudo-components used for dependency tracking only.
yosys_core(essentials BOOTSTRAP)
yosys_core(everything BOOTSTRAP)

# All of the source code.
add_subdirectory(libs)
add_subdirectory(kernel)
add_subdirectory(passes)
add_subdirectory(frontends)
add_subdirectory(backends)
add_subdirectory(techlibs)
if (YOSYS_ENABLE_PYTHON)
	add_subdirectory(pyosys)
endif()

# ABC submodule.
if (YOSYS_ENABLE_ABC)
	set(YOSYS_ABC_INSTALL NO)
	if (YOSYS_ABC_EXECUTABLE STREQUAL "")
		set(YOSYS_ABC_INSTALL YES)
	endif()
	yosys_abc_target(libyosys-abc yosys-abc
		INCLUDE_IN_ALL_IF ${YOSYS_ABC_INSTALL}
	)
endif()

# Compute a transitive closure of enabled components.
yosys_expand_components(library_components essentials ${YOSYS_COMPONENTS})
yosys_expand_components(driver_components driver ${YOSYS_COMPONENTS})

# Main Yosys executable (compiler driver).
yosys_cxx_executable(yosys
	OUTPUT_NAME yosys
	INCLUDE_IN_ALL_IF ${YOSYS_INSTALL_DRIVER}
)
yosys_link_components(yosys PRIVATE ${driver_components})
if (MINGW)
	target_link_options(yosys PRIVATE LINKER:--export-all-symbols)
	set_target_properties(yosys PROPERTIES
		# Final name: `yosys.exe.a` (linked to explicitly)
		IMPORT_PREFIX ""
		IMPORT_SUFFIX ".exe.a"
	)
	if (YOSYS_INSTALL_DRIVER)
		install(FILES ${CMAKE_BINARY_DIR}/yosys.exe.a DESTINATION ${YOSYS_INSTALL_LIBDIR})
	endif()
endif()

# Yosys components as a library.
if (BUILD_SHARED_LIBS)
	set(libyosys_type SHARED)
else()
	set(libyosys_type STATIC)
endif()
yosys_cxx_library(libyosys ${libyosys_type}
	OUTPUT_NAME libyosys
	INCLUDE_IN_ALL_IF ${YOSYS_INSTALL_LIBRARY}
)
yosys_link_components(libyosys PRIVATE ${library_components})
add_library(Yosys::libyosys ALIAS libyosys)
if (MINGW)
	set_target_properties(libyosys PROPERTIES
		# Final name: `libyosys.dll.a` (linked to via `-lyosys`)
		IMPORT_PREFIX ""
	)
endif()

# Yosys data files (mainly headers and technological libraries).
if (YOSYS_INSTALL_DRIVER OR YOSYS_INSTALL_LIBRARY)
	yosys_install_component_data(${library_components} DESTINATION ${YOSYS_INSTALL_DATADIR})
endif()

# Python binary extension (for using Yosys as a Python library).
if (YOSYS_ENABLE_PYTHON)
	yosys_cxx_library(pyosys SHARED
		OUTPUT_NAME pyosys
		INCLUDE_IN_ALL_IF ${YOSYS_INSTALL_PYTHON}
	)
	yosys_link_components(pyosys PRIVATE ${library_components})

	if (YOSYS_INSTALL_PYTHON)
		string(REPLACE "-" "_" PYOSYS_MODULE_PREFIX "${YOSYS_PROGRAM_PREFIX}")
		set(PYOSYS_INSTALL_DIR ${Python3_SITEARCH}/${PYOSYS_MODULE_PREFIX}pyosys)
		install(FILES pyosys/modinit.py
			RENAME __init__.py
			DESTINATION ${PYOSYS_INSTALL_DIR}
		)
		install(TARGETS pyosys
			RENAME libyosys${CMAKE_SHARED_LIBRARY_SUFFIX}
			DESTINATION ${PYOSYS_INSTALL_DIR}
		)
		if (YOSYS_ABC_EXECUTABLE STREQUAL "")
			# If ABC is vendored it needs to be installed as a part of pyosys.
			install(TARGETS yosys-abc
				DESTINATION ${PYOSYS_INSTALL_DIR}
			)
		endif()
		yosys_install_component_data(${library_components} DESTINATION ${PYOSYS_INSTALL_DIR}/share)
	endif()
endif()

# Plugin build tool.
yosys_config_script(BUILD)
yosys_config_script(INSTALL)

# Tests.
add_subdirectory(tests/unit)
# TODO(cmake): other tests

# Utilities.
yosys_expand_components(all_components everything QUIET)
list(TRANSFORM all_components PREPEND "COMMAND;${CMAKE_COMMAND};-E;echo;" OUTPUT_VARIABLE echo_all_components)
add_custom_target(print-yosys-components
	${echo_all_components}
	VERBATIM
)

math(EXPR YOSYS_VERSION_MINOR_next "${YOSYS_VERSION_MINOR} + 1")
add_custom_target(increment-minor-version
	COMMAND ${CMAKE_COMMAND} -E echo
		"set(YOSYS_VERSION_MAJOR ${YOSYS_VERSION_MAJOR})"
		> ${CMAKE_SOURCE_DIR}/cmake/YosysVersionData.cmake
	COMMAND ${CMAKE_COMMAND} -E echo
		"set(YOSYS_VERSION_MINOR ${YOSYS_VERSION_MINOR_next})"
		>> ${CMAKE_SOURCE_DIR}/cmake/YosysVersionData.cmake
	VERBATIM
)
