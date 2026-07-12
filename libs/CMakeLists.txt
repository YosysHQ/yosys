add_subdirectory(bigint)
add_subdirectory(cxxopts)
add_subdirectory(dlfcn-win32)
add_subdirectory(ezsat)
add_subdirectory(fst)
add_subdirectory(json11)
add_subdirectory(minisat)
add_subdirectory(sha1)
add_subdirectory(subcircuit)
block()
    set(BUILD_SHARED_LIBS OFF)
    set(CMAKE_FIND_PACKAGE_TARGETS_GLOBAL TRUE)
    include(FetchContent)
    set(FETCHCONTENT_FULLY_DISCONNECTED ON)

    option(FMT_INSTALL OFF)
    find_package(fmt QUIET)
    if(NOT fmt_FOUND)
        FetchContent_Declare(
            fmt
            EXCLUDE_FROM_ALL
            SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/fmt
        )
        FetchContent_MakeAvailable(fmt)
    endif()

    find_package(tomlplusplus QUIET)
    if(NOT tomlplusplus_FOUND)
        FetchContent_Declare(
            tomlplusplus
            EXCLUDE_FROM_ALL
            SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/tomlplusplus
        )
        FetchContent_MakeAvailable(tomlplusplus)
    endif()

    if (NOT YOSYS_WITHOUT_SLANG)
        find_package(Boost QUIET COMPONENTS regex)
        if(NOT Boost_FOUND)
            FetchContent_Declare(
                boost_regex
                EXCLUDE_FROM_ALL
                SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/boost_regex
                SOURCE_SUBDIR _no_build_
            )
            FetchContent_MakeAvailable(boost_regex)
        endif()

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
