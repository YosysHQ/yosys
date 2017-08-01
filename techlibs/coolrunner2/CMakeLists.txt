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

set(SOURCE_FILES ${SOURCE_FILES}
    ${CMAKE_CURRENT_LIST_DIR}/synth_coolrunner2.cc
    ${CMAKE_CURRENT_LIST_DIR}/coolrunner2_sop.cc
    )


file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/share/coolrunner2/)
add_custom_target(copy-coolrunner2-files ALL
                  BYPRODUCTS
                  ${CMAKE_CURRENT_BINARY_DIR}/share/coolrunner2/cells_latch.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/coolrunner2/cells_sim.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/coolrunner2/xc2_dff.lib
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/cells_latch.v ${CMAKE_CURRENT_BINARY_DIR}/share/coolrunner2/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/cells_sim.v ${CMAKE_CURRENT_BINARY_DIR}/share/coolrunner2/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/xc2_dff.lib ${CMAKE_CURRENT_BINARY_DIR}/share/coolrunner2/
                  DEPENDS
                  ${CMAKE_CURRENT_LIST_DIR}/cells_latch.v
                  ${CMAKE_CURRENT_LIST_DIR}/cells_sim.v
                  ${CMAKE_CURRENT_LIST_DIR}/xc2_dff.lib
                  WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}
                  COMMENT "Generating ${CMAKE_CURRENT_BINARY_DIR}/share/coolrunner2")