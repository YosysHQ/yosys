if (CMAKE_BINARY_DIR STREQUAL CMAKE_SOURCE_DIR)
	set(rm "rm -rf")
	if (WIN32)
		set(rm "del /s /q")
	endif()
	message(FATAL_ERROR
		"In-tree builds are not supported. Instead, run:\n"
		"${rm} CMakeCache.txt CMakeFiles ; cmake -B build <options>"
	)
endif()

cmake_minimum_required(VERSION 3.28)
project(yosys LANGUAGES C CXX)

set(CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake" ${CMAKE_MODULE_PATH})
include(CMakeDependentOption)
include(FeatureSummary)
include(CheckPIESupported)

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
include(YosysAbcSubmodule)
include(YosysVerific)
include(UseHomebrew)

# Fix for using Clang from nixpkgs
# see https://github.com/YosysHQ/yosys/pull/5936#issuecomment-4637319568
set(CMAKE_CXX_SCAN_FOR_MODULES NO)

# Build options.
set(YOSYS_COMPILER_LAUNCHER "" CACHE STRING "Compiler launcher (ccache, sccache)")
option(YOSYS_ENABLE_COVERAGE "Enable code coverage" OFF)
option(YOSYS_ENABLE_PROFILING "Enable instruction profiling" OFF)
option(YOSYS_ENABLE_FUNCTIONAL_TESTS "Enable running functional tests" OFF)

set(YOSYS_PROGRAM_PREFIX "" CACHE STRING "Name prefix for programs, libraries, and data")
set(YOSYS_COMPONENTS "everything" CACHE STRING "List of components to build (use pass names)")
option(BUILD_SHARED_LIBS "Build libyosys as a shared library" ON)

option(YOSYS_DISABLE_THREADS "Disable threading" OFF)
set(YOSYS_ABC_EXECUTABLE "" CACHE FILEPATH
	"Path to the ABC executable (empty for vendored, 'INTEGRATED-NOTFOUND' for in-process)")
option(YOSYS_WITHOUT_ABC "Disable ABC support (not recommended)" OFF)
option(YOSYS_WITHOUT_ZLIB "Disable zlib integration" OFF)
option(YOSYS_WITHOUT_LIBFFI "Disable libffi integration" OFF)
option(YOSYS_WITHOUT_READLINE "Disable readline integration" ON)
option(YOSYS_WITHOUT_EDITLINE "Disable editline integration" OFF)
option(YOSYS_WITHOUT_TCL "Disable Tcl integration" OFF)
option(YOSYS_WITH_PYTHON "Enable Python integration" OFF)

set(YOSYS_VERIFIC_DIR "" CACHE FILEPATH "Path to the Verific source code (empty to disable)")
set(YOSYS_VERIFIC_COMPONENTS "" CACHE STRING
	"List of Verific components to link (empty for autodetect)")
set(YOSYS_VERIFIC_FEATURES "" CACHE STRING
	"List of Yosys Verific frontend features to enable (empty for autodetect)")

option(YOSYS_INSTALL_DRIVER "Install Yosys executable" ON)
option(YOSYS_INSTALL_LIBRARY "Install libyosys library" OFF)
cmake_dependent_option(YOSYS_INSTALL_PYTHON "Install Python extension module" OFF
	YOSYS_WITH_PYTHON OFF)
set(YOSYS_INSTALL_PYTHON_SITEDIR "" CACHE STRING "Path to Python package installation directory")

# This option is something of a hack to make Python wheels buildable in an environment that has
# the `Development.Module` component, but not `Development.Embed` (e.g. cibuildwheel). It is only
# present to be used in the wheel build and is not supported otherwise.
cmake_dependent_option(YOSYS_BUILD_PYTHON_ONLY "Build only Pyosys components" ON
	"NOT (YOSYS_INSTALL_DRIVER OR YOSYS_INSTALL_LIBRARY) AND YOSYS_INSTALL_PYTHON" OFF)
mark_as_advanced(YOSYS_BUILD_PYTHON_ONLY)

# Configure compiler.
set(CMAKE_EXPORT_COMPILE_COMMANDS YES)

if (YOSYS_COMPILER_LAUNCHER)
	set(CMAKE_C_COMPILER_LAUNCHER "${YOSYS_COMPILER_LAUNCHER}")
	set(CMAKE_CXX_COMPILER_LAUNCHER "${YOSYS_COMPILER_LAUNCHER}")
endif()

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED YES)

set(CMAKE_POSITION_INDEPENDENT_CODE ON)
check_pie_supported() # opportunistically enable PIE

if (CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
	set(CMAKE_CXX_FLAGS_DEBUG "-Og -ggdb")
	set(CMAKE_CXX_FLAGS_RELEASE "-O3")
	set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O3 -ggdb")
	set(CMAKE_CXX_FLAGS_MINSIZEREL "-Os")
	set(CMAKE_CXX_FLAGS_SANITIZE "-O1 -fno-omit-frame-pointer -fno-optimize-sibling-calls")
	if ("${SANITIZE}" MATCHES "memory")
		set(CMAKE_CXX_FLAGS_SANITIZE "${CMAKE_CXX_FLAGS_SANITIZE} -fsanitize-memory-track-origins")
	endif()
	set(no_abc_options
		"$<$<AND:$<NOT:$<BOOL:$<TARGET_PROPERTY:YOSYS_IS_ABC>>>,$<CONFIG:Sanitize>>:-fsanitize=${SANITIZE}>"
		"$<$<NOT:$<BOOL:$<TARGET_PROPERTY:YOSYS_IS_ABC>>>:-Wall;-Wextra;-Werror=unused-variable>"
	)
	add_compile_options("${no_abc_options}")
	add_link_options("${no_abc_options}")
elseif (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
	set(CMAKE_CXX_FLAGS_DEBUG "/Od /DEBUG")
	set(CMAKE_CXX_FLAGS_RELEASE "/O2")
	set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "/O2 /DEBUG")
	set(CMAKE_CXX_FLAGS_MINSIZEREL "/Os")
	add_compile_options(/Zc:__cplusplus)
	add_compile_definitions(
		_CRT_NONSTDC_NO_DEPRECATE
		_CRT_SECURE_NO_WARNINGS
	)
else()
	# We have to do this because CMake adds `-DNDEBUG` in release builds by default, and there's
	# no particularly good way to prevent this without also erasing optimization flags.
	# If you see this message, reproduce the block above with the flags supported by your compiler.
	message(FATAL_ERROR "${CMAKE_CXX_COMPILER_ID} compiler is not supported")
endif()

if (YOSYS_ENABLE_COVERAGE)
	if (CMAKE_CXX_COMPILER_ID MATCHES "GNU")
		set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} --coverage")
	elseif (CMAKE_CXX_COMPILER_ID MATCHES "Clang")
		set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fprofile-instr-generate -fcoverage-mapping")
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

if (NOT CMAKE_C_COMPILER_ID STREQUAL CMAKE_CXX_COMPILER_ID)
	message(FATAL_ERROR "C and C++ compilers must be provided by the same vendor")
endif()
set(CMAKE_C_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG}")
set(CMAKE_C_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE}")
set(CMAKE_C_FLAGS_RELWITHDEBINFO "${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")
set(CMAKE_C_FLAGS_MINSIZEREL "${CMAKE_CXX_FLAGS_MINSIZEREL}")
set(CMAKE_C_FLAGS_SANITIZE "${CMAKE_CXX_FLAGS_SANITIZE}")

if (CMAKE_SYSTEM_NAME STREQUAL "WASI")
	add_compile_options(
		-fwasm-exceptions -mllvm -wasm-use-legacy-eh=false
		-D_WASI_EMULATED_PROCESS_CLOCKS
	)
	add_link_options(
		-fwasm-exceptions -mllvm -wasm-use-legacy-eh=false -lunwind
		-lwasi-emulated-process-clocks
		-Wl,--stack-first,-z,stack-size=8388608
	)
endif()

if (MINGW AND CMAKE_CXX_COMPILER_ID STREQUAL "GNU" AND CMAKE_CXX_COMPILER_VERSION VERSION_LESS "16.0.0")
	# GCC 15.2 sometimes refuses to construct an import directory for yosys.exe/libyosys.dll with:
	#   .../ld.exe: error: export ordinal too large: 67035
	# The cause is unknown.
	message(WARNING "MinGW GCC is supported starting with version 16.0.0")
endif()

# Required dependencies.
if (APPLE)
	# In practice, we can't expect paths to Homebrew packages to be configured.
	use_homebrew()
endif()

find_package(FLEX 2.6)
set_package_properties(FLEX PROPERTIES
	URL "https://github.com/westes/flex"
	DESCRIPTION "The Fast Lexical Analyzer"
	PURPOSE "Compiling the Verilog lexer"
	TYPE REQUIRED
)

find_package(BISON 3.6)
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
	find_package(Python3Devel REQUIRED)
	set_property(GLOBAL PROPERTY _CMAKE_Python3Devel_REQUIRED_VERSION "== ${Python3_VERSION}")
	set_package_properties(Python3Devel PROPERTIES
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

include(SilimateConfig)

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
condition(YOSYS_ENABLE_PYTHON Python3Devel_FOUND AND PyosysEnv_FOUND AND YOSYS_WITH_PYTHON)
condition(YOSYS_ENABLE_VERIFIC YOSYS_VERIFIC_DIR AND zlib_FOUND)

include(SilimateVerific)

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
add_feature_info(with_verific YOSYS_ENABLE_VERIFIC "Verific frontend integration")
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

# Describe project version.
yosys_extract_version()

# Describe ABC integration.
if (YOSYS_ENABLE_ABC AND NOT YOSYS_ENABLE_SPAWN AND NOT YOSYS_ABC_EXECUTABLE STREQUAL "INTEGRATED-NOTFOUND")
	message(WARNING "ABC support on this platform forces -DYOSYS_ABC_EXECUTABLE=INTEGRATED-NOTFOUND")
	set(YOSYS_ABC_EXECUTABLE "INTEGRATED-NOTFOUND" CACHE FILEPATH "" FORCE)
endif()

set(YOSYS_LINK_ABC 0)
if (YOSYS_ENABLE_ABC)
	if (NOT YOSYS_ABC_EXECUTABLE AND NOT YOSYS_SKIP_ABC_SUBMODULE_CHECK)
		yosys_check_abc_submodule()
	endif()
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

# Ensure invalid dependencies fail at configuration time, not link time.
set(CMAKE_LINK_LIBRARIES_ONLY_TARGETS ON)

# Pseudo-library that injects common compilation options into every Yosys component.
add_library(yosys_common INTERFACE)
target_compile_definitions(yosys_common INTERFACE
	_YOSYS_
	$<$<CONFIG:Debug,RelWithDebInfo>:DEBUG>
)
target_include_directories(yosys_common INTERFACE
	${CMAKE_SOURCE_DIR}
	${CMAKE_BINARY_DIR}
)
if (SANITIZE)
	target_compile_options(yosys_common INTERFACE
		${sanitize_options}
	)
endif()

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
if (YOSYS_ENABLE_ABC AND NOT YOSYS_ABC_EXECUTABLE)
	set(YOSYS_ABC_INSTALL NO)
	if (YOSYS_ABC_EXECUTABLE STREQUAL "" AND (YOSYS_INSTALL_DRIVER OR YOSYS_INSTALL_LIBRARY))
		set(YOSYS_ABC_INSTALL YES)
	endif()
	yosys_abc_target(libyosys-abc yosys-abc
		INSTALL_IF ${YOSYS_ABC_INSTALL}
	)
endif()

# Compute a transitive closure of enabled components.
yosys_expand_components(library_components essentials ${YOSYS_COMPONENTS})
if (NOT YOSYS_BUILD_PYTHON_ONLY)
	yosys_expand_components(driver_components driver ${YOSYS_COMPONENTS})
endif()

# Main Yosys executable (compiler driver).
if (NOT YOSYS_BUILD_PYTHON_ONLY)
	yosys_cxx_executable(yosys
		OUTPUT_NAME yosys
		INSTALL_IF ${YOSYS_INSTALL_DRIVER}
	)
	yosys_link_components(yosys PRIVATE ${driver_components})
	set_property(TARGET yosys PROPERTY ENABLE_EXPORTS ON)
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

	target_compile_options(yosys PRIVATE -fsanitize=undefined)
endif()

# Yosys components as a library.
if (NOT YOSYS_BUILD_PYTHON_ONLY)
	if (BUILD_SHARED_LIBS)
		set(libyosys_type SHARED)
	else()
		set(libyosys_type STATIC)
	endif()
	yosys_cxx_library(libyosys ${libyosys_type}
		OUTPUT_NAME libyosys
		INSTALL_IF ${YOSYS_INSTALL_LIBRARY}
	)
	yosys_link_components(libyosys PRIVATE ${library_components})
	add_library(Yosys::libyosys ALIAS libyosys)
	if (MINGW)
		set_target_properties(libyosys PROPERTIES
			# Final name: `libyosys.dll.a` (linked to via `-lyosys`)
			IMPORT_PREFIX ""
		)
	endif()
endif()

# Yosys data files (mainly headers and technological libraries).
if (YOSYS_INSTALL_DRIVER OR YOSYS_INSTALL_LIBRARY)
	yosys_install_component_data(${library_components} DESTINATION ${YOSYS_INSTALL_DATADIR})
endif()

# Python binary extension (for using Yosys as a Python library).
if (YOSYS_ENABLE_PYTHON)
	yosys_cxx_library(pyosys MODULE
		OUTPUT_NAME pyosys
	)
	yosys_link_components(pyosys PRIVATE ${library_components})
	set_target_properties(pyosys PROPERTIES EXCLUDE_FROM_ALL FALSE) # build but not install
	if (YOSYS_ENABLE_ABC AND YOSYS_ABC_EXECUTABLE STREQUAL "")
		add_dependencies(pyosys yosys-abc)
	endif()

	if (YOSYS_INSTALL_PYTHON)
		string(REPLACE "-" "_" PYOSYS_MODULE_PREFIX "${YOSYS_PROGRAM_PREFIX}")
		if (YOSYS_INSTALL_PYTHON_SITEDIR STREQUAL "")
			set(YOSYS_INSTALL_PYTHON_SITEDIR ${Python3_SITEARCH})
		endif()
		set(pyosys_install_dir ${YOSYS_INSTALL_PYTHON_SITEDIR}/${PYOSYS_MODULE_PREFIX}pyosys)
		install(FILES pyosys/modinit.py
			RENAME __init__.py
			DESTINATION ${pyosys_install_dir}
		)
		install(FILES $<TARGET_FILE:pyosys>
			RENAME libyosys${CMAKE_SHARED_MODULE_SUFFIX}
			DESTINATION ${pyosys_install_dir}
		)
		if (YOSYS_ENABLE_ABC AND YOSYS_ABC_EXECUTABLE STREQUAL "")
			# If ABC is vendored it needs to be installed as a part of pyosys.
			install(TARGETS yosys-abc
				DESTINATION ${pyosys_install_dir}
			)
		endif()
		yosys_install_component_data(${library_components} DESTINATION ${pyosys_install_dir}/share)
	endif()
endif()

# Plugin build tool.
yosys_config_script(BUILD)
if (YOSYS_INSTALL_DRIVER OR YOSYS_INSTALL_LIBRARY)
	yosys_config_script(INSTALL)
endif()

# Configuration for Makefile-based steps.
# (The use of `${makefile_vars}` in `add_custom_{target,command}()` adds dependencies for
# all of the targets specified via `$<TARGET_FILE:tgt>`.)
set(makefile_vars
	BUILD_DIR=${CMAKE_BINARY_DIR}
	PROGRAM_PREFIX=${YOSYS_PROGRAM_PREFIX}
	ABC=$<IF:$<TARGET_EXISTS:yosys-abc>,$<TARGET_FILE:yosys-abc>,${YOSYS_ABC_EXECUTABLE}>
	YOSYS=$<TARGET_FILE:yosys>
	YOSYS_CONFIG=${CMAKE_BINARY_DIR}/${YOSYS_PROGRAM_PREFIX}yosys-config
	YOSYS_FILTERLIB=$<$<TARGET_EXISTS:yosys-filterlib>:$<TARGET_FILE:yosys-filterlib>>
	YOSYS_SMTBMC=${CMAKE_BINARY_DIR}/${YOSYS_PROGRAM_PREFIX}yosys-smtbmc
	YOSYS_WITNESS=${CMAKE_BINARY_DIR}/${YOSYS_PROGRAM_PREFIX}yosys-witness
)
set(makefile_depends
	# abc is implied via $<TARGET_FILE>
	# yosys is implied via $<TARGET_FILE>
	# yosys-filterlib is implied via $<TARGET_FILE>
	$<$<TARGET_EXISTS:yosys-smtbmc>:yosys-smtbmc>
	$<$<TARGET_EXISTS:yosys-witness>:yosys-witness>
)

if (NOT YOSYS_BUILD_PYTHON_ONLY)
	# Tests.
	add_subdirectory(tests/unit)

	add_custom_target(test-unit
		COMMAND ${CMAKE_CTEST_COMMAND} --test-dir tests/unit --output-on-failure
		WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
	)

	add_custom_target(test-vanilla
		COMMAND make vanilla-test ${makefile_vars}
			ENABLE_FUNCTIONAL_TESTS=$<IF:$<BOOL:${YOSYS_ENABLE_FUNCTIONAL_TESTS}>,1,0>
		WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tests
		DEPENDS ${makefile_depends}
		USES_TERMINAL
		JOB_SERVER_AWARE TRUE
	)

	add_custom_target(test-functional
		COMMAND make functional ${makefile_vars}
			ENABLE_FUNCTIONAL_TESTS=$<IF:$<BOOL:${YOSYS_ENABLE_FUNCTIONAL_TESTS}>,1,0>
		WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/tests
		DEPENDS ${makefile_depends}
		USES_TERMINAL
		JOB_SERVER_AWARE TRUE
	)

	add_custom_target(test
		DEPENDS test-unit test-vanilla
	)

	# Docs.
	add_custom_target(docs-prepare
		COMMAND make gen ${makefile_vars}
		WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/docs
		DEPENDS ${makefile_depends}
		JOB_SERVER_AWARE TRUE
	)
	foreach (format html latexpdf)
		add_custom_target(docs-${format}
			COMMAND make ${format}
			WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/docs
			DEPENDS docs-prepare
		)
	endforeach()
	add_custom_target(test-docs
		COMMAND make test ${makefile_vars}
		WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/docs
		DEPENDS ${makefile_depends}
		JOB_SERVER_AWARE TRUE
	)
endif()

# Utilities.
add_custom_target(print-version
	COMMAND ${CMAKE_COMMAND} -E echo ${YOSYS_VERSION}
	VERBATIM
)

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
