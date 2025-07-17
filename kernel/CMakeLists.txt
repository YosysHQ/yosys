

#if(CMAKE_PROJECT_VERSION_PATCH GREATER 0)
#    set(YOSYS_VERSION "${CMAKE_PROJECT_VERSION_MAJOR}.${CMAKE_PROJECT_VERSION_MINOR}+${CMAKE_PROJECT_VERSION_PATCH}")
#else()
#    set(YOSYS_VERSION "${CMAKE_PROJECT_VERSION_MAJOR}.${CMAKE_PROJECT_VERSION_MINOR}")
#endif()

find_package(Git)
if(Git_FOUND)
    execute_process(
        COMMAND ${GIT_EXECUTABLE} rev-parse --short=9 HEAD
        WORKING_DIRECTORY ${yosys_SOURCE_DIR}
        OUTPUT_VARIABLE CURRENT_GIT_VERSION
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    set(YOSYS_GIT_VERSION "git sha1 ${CURRENT_GIT_VERSION}, ")
endif()

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/version.cc.in ${CMAKE_CURRENT_BINARY_DIR}/version.cc)
set_property(SOURCE log.cc APPEND PROPERTY COMPILE_DEFINITIONS YOSYS_SRC="${PROJECT_SOURCE_DIR}")

add_library(yosys_kernel OBJECT
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
    # driver.cc
    drivertools.cc
    drivertools.h
    ff.cc
    ff.h
    ffinit.h
    ffmerge.cc
    ffmerge.h
    fmt.cc
    fmt.h
    functional.cc
    functional.h
    gzip.cc
    gzip.h
    hashlib.h
    io.cc
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

if (ENABLE_ZLIB)
target_sources(yosys_kernel PRIVATE
    fstdata.cc
    fstdata.h
)
endif()

add_dependencies(yosys_kernel yosys_techlib_common)

target_link_libraries(yosys_obj PUBLIC yosys_kernel)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_kernel>)
