add_library(yosys_backends_functional INTERFACE)

target_sources(yosys_backends_functional INTERFACE
    cxx.cc
    smtlib.cc
    smtlib_rosette.cc
    test_generic.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_functional)
