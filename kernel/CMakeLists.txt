add_library(yosys_kernel INTERFACE)

#if(CMAKE_PROJECT_VERSION_PATCH GREATER 0)
#    set(YOSYS_VERSION "${CMAKE_PROJECT_VERSION_MAJOR}.${CMAKE_PROJECT_VERSION_MINOR}+${CMAKE_PROJECT_VERSION_PATCH}")
#else()
#    set(YOSYS_VERSION "${CMAKE_PROJECT_VERSION_MAJOR}.${CMAKE_PROJECT_VERSION_MINOR}")
#endif()

find_package(Git)
if(Git_FOUND)
    execute_process(
        COMMAND ${GIT_EXECUTABLE} rev-parse --short=9 HEAD
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        OUTPUT_VARIABLE CURRENT_GIT_VERSION
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    set(YOSYS_GIT_VERSION "git sha1 ${CURRENT_GIT_VERSION}, ")
endif()

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/version.cc.in ${CMAKE_CURRENT_BINARY_DIR}/version.cc)

target_sources(yosys_kernel INTERFACE
    binding.cc
    binding.h
    bitpattern.h
    calc.cc
    cellaigs.cc
    cellaigs.h
    celledges.cc
    celledges.h
    celltypes.h
    compute_graph.h
    consteval.h
    constids.inc
    cost.cc
    cost.h
    driver.cc
    drivertools.cc
    drivertools.h
    ff.cc
    ff.h
    ffinit.h
    ffmerge.cc
    ffmerge.h
    fmt.cc
    fmt.h
    fstdata.cc
    fstdata.h
    functional.cc
    functional.h
    hashlib.h
    json.cc
    json.h
    log.cc
    log.h
    macc.h
    mem.cc
    mem.h
    modtools.h
    qcsat.cc
    qcsat.h
    register.cc
    register.h
    rtlil.cc
    rtlil.h
    satgen.cc
    satgen.h
    scopeinfo.cc
    scopeinfo.h
    sexpr.cc
    sexpr.h
    sigtools.h
    tclapi.cc
    timinginfo.h
    topo_scc.h
    utils.h
    ${CMAKE_CURRENT_BINARY_DIR}/version.cc
    yosys.cc
    yosys_common.h
    yosys.h
    yw.cc
    yw.h
)

target_link_libraries(yosys PRIVATE yosys_kernel)
