#
#   yosys -- Yosys Open SYnthesis Suite
#
#   Copyright (C) 2017  Sebastian Wallat <sebastian.wallat@rub.de>
#
#   Permission to use, copy, modify, and/or distribute this software for any
#   purpose with or without fee is hereby granted, provided that the above
#   copyright notice and this permission notice appear in all copies.
#
#   THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
#   WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
#   MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
#   ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
#   WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
#   ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
#   OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

set(SOURCE_FILES ${SOURCE_FILES} ${CMAKE_CURRENT_LIST_DIR}/synth_intel.cc)


file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/)
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/max10/)
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/cycloneiv/)
add_custom_target(copy-altera-intel-files ALL
                  BYPRODUCTS
#                   ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/lpm_functions.v
                   ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/max10/cells_comb_max10.v
                   ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/max10/cells_map_max10.v
#                   ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/max10/cells_arith_max10.v
                   ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/cycloneiv/cells_comb_cycloneiv.v
                   ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/cycloneiv/cells_map_cycloneiv.v
#                   COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/lpm_functions.v ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/
                   COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/max10/cells_comb_max10.v ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/max10/
                   COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/max10/cells_map_max10.v ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/max10/
#                   COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/max10/cells_arith_max10.v ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/max10/
                   COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/cycloneiv/cells_comb_cycloneiv.v ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/cycloneiv/
                   COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/cycloneiv/cells_map_cycloneiv.v ${CMAKE_CURRENT_BINARY_DIR}/share/altera_intel/cycloneiv/
                   DEPENDS
#                   ${CMAKE_CURRENT_LIST_DIR}/lpm_functions.v
                   ${CMAKE_CURRENT_LIST_DIR}/max10/cells_comb_max10.v
                   ${CMAKE_CURRENT_LIST_DIR}/max10/cells_map_max10.v
#                   ${CMAKE_CURRENT_LIST_DIR}/max10/cells_arith_max10.v
                   ${CMAKE_CURRENT_LIST_DIR}/cycloneiv/cells_comb_cycloneiv.v
                   ${CMAKE_CURRENT_LIST_DIR}/cycloneiv/cells_map_cycloneiv.v
                   WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}
                   COMMENT "Generating ${CMAKE_CURRENT_BINARY_DIR}/share/python3")