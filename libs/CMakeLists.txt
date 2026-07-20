add_subdirectory(bigint)
add_subdirectory(cxxopts)
add_subdirectory(dlfcn-win32)
add_subdirectory(ezsat)
add_subdirectory(fst)
add_subdirectory(json11)
add_subdirectory(minisat)
add_subdirectory(sha1)
add_subdirectory(subcircuit)

add_library(symfpu INTERFACE)
target_include_directories(symfpu INTERFACE
    ${CMAKE_CURRENT_SOURCE_DIR}
)

block()
    set(BUILD_SHARED_LIBS OFF)
    include(FetchContent)
    set(FETCHCONTENT_FULLY_DISCONNECTED ON)

    if(NOT YOSYS_USE_BUNDLED_LIBS)
        find_package(fmt 12.2 QUIET)
    endif()
    if(fmt_FOUND)
        set(SLANG_USE_SYSTEM_FMT ON)
    else()
        option(FMT_INSTALL OFF)
        FetchContent_Declare(
            fmt
            EXCLUDE_FROM_ALL
            SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/fmt
        )
        FetchContent_MakeAvailable(fmt)
    endif()

    if(NOT YOSYS_USE_BUNDLED_LIBS)
        find_package(tomlplusplus 3.4 QUIET)
    endif()
    if(tomlplusplus_FOUND)
        set(SLANG_USE_SYSTEM_TOMLPLUSPLUS ON)
    else()
        FetchContent_Declare(
            tomlplusplus
            EXCLUDE_FROM_ALL
            SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/tomlplusplus
        )
        FetchContent_MakeAvailable(tomlplusplus)
    endif()

    if(NOT YOSYS_USE_BUNDLED_LIBS)
        find_package(Boost 1.87.0 CONFIG QUIET)
    endif()
    if(Boost_FOUND)
        set(SLANG_USE_SYSTEM_BOOST ON)
    else()
        FetchContent_Declare(
            boost_regex
            EXCLUDE_FROM_ALL
            SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/boost_regex
            SOURCE_SUBDIR _no_build_
        )
        FetchContent_MakeAvailable(boost_regex)
    endif()

    if (NOT YOSYS_WITHOUT_SLANG)
        set(SLANG_USE_MIMALLOC OFF)
        add_subdirectory(slang)
        # Headers autodetect based on <boost/config.hpp> but when version
        # does exist but does not match requirements it becomes problematic
        if(NOT Boost_FOUND)
            target_compile_definitions(slang_slang PRIVATE BOOST_REGEX_STANDALONE)
        endif()
        if (SLANG_INCLUDE_TOOLS)
            # Temporary to prevent build issues
            set_target_properties(slang_tidy_obj_lib PROPERTIES YOSYS_IS_ABC ON)

            install(TARGETS slang_driver RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
            install(TARGETS slang_hier RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
            install(TARGETS slang_reflect RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
            install(TARGETS slang_tidy RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
        endif()
    endif()
endblock()
