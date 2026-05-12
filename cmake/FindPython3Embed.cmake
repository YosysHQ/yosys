# Wrapper to improve behavior of `FindPython3` during cross-compilation.
# Does not entirely fix the problem; CMake 4.0 introduces `Python_ARTIFACTS_PREFIX`, which will.

# Stash the package found status
get_property(packages_found GLOBAL PROPERTY PACKAGES_FOUND)
get_property(packages_not_found GLOBAL PROPERTY PACKAGES_NOT_FOUND)
get_property(required_version GLOBAL PROPERTY _CMAKE_Python3_REQUIRED_VERSION)

# The `EXACT` specifier prevents the situation of `FindPython3` discovering a newer libpython-dev
# than the interpreter found in the past, rejecting it because it is too new, and giving up.
find_package(Python3 EXACT ${Python3_VERSION} COMPONENTS Development.Embed)
set(Python3Embed_FOUND ${Python3_Development.Embed_FOUND})

set_property(GLOBAL PROPERTY PACKAGES_FOUND "${packages_found}")
set_property(GLOBAL PROPERTY PACKAGES_NOT_FOUND "${packages_not_found}")
set_property(GLOBAL PROPERTY _CMAKE_Python3_REQUIRED_VERSION "${required_version}")
