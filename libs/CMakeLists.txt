add_subdirectory(bigint)
add_subdirectory(cxxopts)
add_subdirectory(dlfcn-win32)
add_subdirectory(ezsat)
add_subdirectory(fst)
add_subdirectory(json11)
add_subdirectory(minisat)
add_subdirectory(sha1)
add_subdirectory(subcircuit)

# Link yosys slang
set(_old_BUILD_SHARED_LIBS "${BUILD_SHARED_LIBS}")
set(BUILD_SHARED_LIBS OFF)
set(BUILD_AS_PLUGIN OFF)
set(YOSYS_SLANG_OBJECT_LIBRARY ON)
add_subdirectory(yosys-slang)
set(BUILD_SHARED_LIBS "${_old_BUILD_SHARED_LIBS}")
set_target_properties(yosys-slang PROPERTIES
    YOSYS_IS_ABC ON # Do not error on warning
    YOSYS_COMPONENT YES
    YOSYS_REQUIRES ""
    YOSYS_ENABLE_IF TRUE
)
target_link_libraries(yosys-slang PUBLIC yosys_common)
add_library(yosys_read_slang ALIAS yosys-slang)
set_property(TARGET yosys_everything APPEND PROPERTY YOSYS_REQUIRES read_slang)
