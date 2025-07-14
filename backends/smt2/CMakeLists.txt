

add_library(yosys_backends_smt2 OBJECT
    smt2.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_smt2)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_smt2>)

add_share_file("share/python3" "smtio.py")
add_share_file("share/python3" "ywio.py")
