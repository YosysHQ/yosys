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
    ${CMAKE_CURRENT_LIST_DIR}/synth_xilinx.cc
    )

file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/)
add_custom_target(generate-xilinx-files ALL
                  BYPRODUCTS
                  ${CMAKE_CURRENT_LIST_DIR}/brams_init_36.vh
                  ${CMAKE_CURRENT_LIST_DIR}/brams_init_32.vh
                  ${CMAKE_CURRENT_LIST_DIR}/brams_init_18.vh
                  ${CMAKE_CURRENT_LIST_DIR}/brams_init_16.vh
                  COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_LIST_DIR}/brams_init.py
                  COMMAND mv ${CMAKE_CURRENT_LIST_DIR}/brams_init_36.vh ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND mv ${CMAKE_CURRENT_LIST_DIR}/brams_init_32.vh ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND mv ${CMAKE_CURRENT_LIST_DIR}/brams_init_18.vh ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND mv ${CMAKE_CURRENT_LIST_DIR}/brams_init_16.vh ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  DEPENDS ${CMAKE_CURRENT_LIST_DIR}/brams_init.py
                  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
                  COMMENT "Generating share/xilinx/brams_init_36.vh share/xilinx/brams_init_32.vh share/xilinx/brams_init_18.vh share/xilinx/brams_init_16.vh"
                  )
add_custom_target(copy-xilinx-files ALL
                  BYPRODUCTS
                  ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/cells_map.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/cells_sim.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/cells_xtra.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/arith_map.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/brams.txt
                  ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/brams_map.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/brams_bb.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/drams.txt
                  ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/drams_map.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/drams_bb.v
                  ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/lut2lut.v
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/cells_map.v ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/cells_sim.v ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/cells_xtra.v ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/arith_map.v ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/brams_map.v ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/brams_bb.v ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/brams.txt ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/drams_map.v ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/drams_bb.v ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/drams.txt ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/lut2lut.v ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx/
                  DEPENDS
                  ${CMAKE_CURRENT_LIST_DIR}/cells_map.v
                  ${CMAKE_CURRENT_LIST_DIR}/cells_sim.v
                  ${CMAKE_CURRENT_LIST_DIR}/cells_xtra.v
                  ${CMAKE_CURRENT_LIST_DIR}/arith_map.v
                  ${CMAKE_CURRENT_LIST_DIR}/brams_map.v
                  ${CMAKE_CURRENT_LIST_DIR}/brams_bb.v
                  ${CMAKE_CURRENT_LIST_DIR}/brams.txt
                  ${CMAKE_CURRENT_LIST_DIR}/drams_map.v
                  ${CMAKE_CURRENT_LIST_DIR}/drams_bb.v
                  ${CMAKE_CURRENT_LIST_DIR}/drams.txt
                  ${CMAKE_CURRENT_LIST_DIR}/lut2lut.v
                  WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}
                  COMMENT "Generating ${CMAKE_CURRENT_BINARY_DIR}/share/xilinx"
                  )




