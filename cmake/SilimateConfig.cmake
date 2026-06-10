# Always force disable GNU Readline, GPL trap library
set(YOSYS_ENABLE_READLINE OFF)
set(YOSYS_VERIFIC_DIR ${PROJECT_SOURCE_DIR}/verific)
set(YOSYS_WITH_PYTHON ON)

add_library(verific INTERFACE)
