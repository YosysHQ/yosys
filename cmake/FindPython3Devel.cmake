# Wrapper to improve behavior of `FindPython3` during cross-compilation.
# Does not entirely fix the problem; CMake 4.0 introduces `Python_ARTIFACTS_PREFIX`, which will.

# Stash the package found status
get_property(packages_found GLOBAL PROPERTY PACKAGES_FOUND)
get_property(packages_not_found GLOBAL PROPERTY PACKAGES_NOT_FOUND)
get_property(required_version GLOBAL PROPERTY _CMAKE_Python3_REQUIRED_VERSION)

# A hack to make pyosys buildable in wheel-only environments.
# `Interpreter` is a part of the component set to ensure that a Python implementation without
# an interpreter that's earlier in the search order won't be selected instead of the desired one.
# (This is awful and should be removed once CMake 4.0 is here.)
if (YOSYS_BUILD_PYTHON_ONLY)
	set(components Interpreter Development.Module)
else()
	set(components Interpreter Development)
endif()

# The `EXACT` specifier prevents the situation of `FindPython3` discovering a newer libpython-dev
# than the interpreter found in the past, rejecting it because it is too new, and giving up.
find_package(Python3 EXACT ${Python3_VERSION} COMPONENTS ${components})
if (Python3_Development.Embed_FOUND OR Python3_Development.Module_FOUND)
	set(Python3Devel_FOUND YES)
endif()

set_property(GLOBAL PROPERTY PACKAGES_FOUND "${packages_found}")
set_property(GLOBAL PROPERTY PACKAGES_NOT_FOUND "${packages_not_found}")
set_property(GLOBAL PROPERTY _CMAKE_Python3_REQUIRED_VERSION "${required_version}")
