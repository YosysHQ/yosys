# We need a *third* `FindPython`-style call in this codebase because the host
# `Python3_EXECUTABLE` may not have pybind11 and cxxheaderparser installed,
# and installing it can be onerous. To work around this problem we try to detect
# whether the host interpreter has the necessary dependencies first, and if it
# does not, fall back to using `uv`.

foreach (strategy host uv fail)
	if (strategy STREQUAL "host")
		set(PyosysEnv_PYTHON Python3_EXECUTABLE)
	elseif (strategy STREQUAL "uv")
		set(PyosysEnv_PYTHON uv run --no-project --with pybind11>3,<4 --with cxxheaderparser python)
	else()
		set(PyosysEnv_PYTHON)
		break()
	endif()

	execute_process(
		COMMAND ${PyosysEnv_PYTHON} -m pybind11 --includes
		RESULT_VARIABLE result
		OUTPUT_VARIABLE output
		OUTPUT_STRIP_TRAILING_WHITESPACE
		ERROR_QUIET
	)
	if (result EQUAL 0)
		string(REGEX REPLACE " ?-I" ";" pybind11_INCLUDE_DIR "${output}")
		list(FILTER pybind11_INCLUDE_DIR INCLUDE REGEX "/pybind11/")

		execute_process(
			COMMAND ${PyosysEnv_PYTHON} ${CMAKE_SOURCE_DIR}/pyosys/generator.py --help
			RESULT_VARIABLE result
			OUTPUT_QUIET
			ERROR_QUIET
		)
		if (result EQUAL 0)
			break()
		endif()
	endif()
endforeach()

find_package_handle_standard_args(PyosysEnv
  REQUIRED_VARS PyosysEnv_PYTHON pybind11_INCLUDE_DIR
)
