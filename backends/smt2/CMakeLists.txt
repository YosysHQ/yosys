

add_library(yosys_backends_smt2 OBJECT
    smt2.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_backends_smt2)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_backends_smt2>)

add_share_file("share/python3" "smtio.py")
add_share_file("share/python3" "ywio.py")
