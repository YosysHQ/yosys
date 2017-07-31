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
    ${CMAKE_CURRENT_LIST_DIR}/synth_ice40.cc
    ${CMAKE_CURRENT_LIST_DIR}/ice40_ffssr.cc
    ${CMAKE_CURRENT_LIST_DIR}/ice40_ffinit.cc
    ${CMAKE_CURRENT_LIST_DIR}/ice40_opt.cc
    )

file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/)
add_custom_target(generate-ice40-files ALL
                  BYPRODUCTS ${CMAKE_CURRENT_LIST_DIR}/brams_init.mk ${CMAKE_CURRENT_LIST_DIR}/brams_init1.vh ${CMAKE_CURRENT_LIST_DIR}/brams_init2.vh ${CMAKE_CURRENT_LIST_DIR}/brams_init3.vh
                  COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_LIST_DIR}/brams_init.py
                  COMMAND mv ${CMAKE_CURRENT_LIST_DIR}/brams_init1.vh ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/
                  COMMAND mv ${CMAKE_CURRENT_LIST_DIR}/brams_init2.vh ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/
                  COMMAND mv ${CMAKE_CURRENT_LIST_DIR}/brams_init3.vh ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/
                  DEPENDS ${CMAKE_CURRENT_LIST_DIR}/brams_init.py
                  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
                  COMMENT "Generating share/ice40/brams_init1.vh share/ice40/brams_init2.vh share/ice40/brams_init3.vh"
                  )
add_custom_target(copy-ice40-files ALL
                  BYPRODUCTS
                  ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/cells_map.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/cells_sim.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/arith_map.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/latches_map.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/brams.txt
                  ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/brams_map.v
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/cells_map.v ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/cells_sim.v ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/arith_map.v ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/latches_map.v ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/brams_map.v ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/brams.txt ${CMAKE_CURRENT_BINARY_DIR}/share/ice40/
                  DEPENDS
                  ${CMAKE_CURRENT_LIST_DIR}/cells_map.v
                  ${CMAKE_CURRENT_LIST_DIR}/cells_sim.v
                  ${CMAKE_CURRENT_LIST_DIR}/arith_map.v
                  ${CMAKE_CURRENT_LIST_DIR}/latches_map.v
                  ${CMAKE_CURRENT_LIST_DIR}/brams_map.v
                  ${CMAKE_CURRENT_LIST_DIR}/brams.txt
                  WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}
                  COMMENT "Generating ${CMAKE_CURRENT_BINARY_DIR}/share/ice40"
                  )



