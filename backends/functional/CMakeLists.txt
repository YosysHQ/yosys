

add_library(yosys_backends_functional OBJECT
    cxx.cc
    smtlib.cc
    smtlib_rosette.cc
    test_generic.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_backends_functional)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_backends_functional>)
