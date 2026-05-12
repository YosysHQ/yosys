add_custom_command(
	DEPENDS
		${CMAKE_CURRENT_SOURCE_DIR}/generator.py
		${CMAKE_CURRENT_SOURCE_DIR}/wrappers_tpl.cc
	OUTPUT
		${CMAKE_CURRENT_BINARY_DIR}/wrappers.cc
		${CMAKE_CURRENT_BINARY_DIR}/wrappers.inc.cc
	DEPFILE
		${CMAKE_CURRENT_BINARY_DIR}/wrappers.cc.d
	COMMAND
		${CMAKE_COMMAND} -E env
			CCACHE=${CMAKE_CXX_COMPILER_LAUNCHER}
			CXX=${CMAKE_CXX_COMPILER}
			CXX_STD=c++${CMAKE_CXX_STANDARD}
		-- ${PyosysEnv_PYTHON}
			${CMAKE_CURRENT_SOURCE_DIR}/generator.py
			${CMAKE_CURRENT_BINARY_DIR}/wrappers.cc
			--build-dir ${CMAKE_BINARY_DIR}
	VERBATIM
	COMMENT "Generating Python wrappers"
)
yosys_core(pyosys
	wrappers.cc
	INCLUDE_DIRS
		${pybind11_INCLUDE_DIR}
	LIBRARIES
		$<${YOSYS_ENABLE_PYTHON}:Python3::Python>
	ESSENTIAL
)
