# Always force disable GNU Readline, GPL trap library
set(YOSYS_ENABLE_READLINE OFF CACHE INTERNAL "")
# Silimate fork has Verific in top-level directory
set(YOSYS_VERIFIC_DIR ${PROJECT_SOURCE_DIR}/verific)
# Pyosys is the primary interface for the Silimate fork
set(YOSYS_WITH_PYTHON ON CACHE BOOL "" FORCE)

add_library(verific INTERFACE)
