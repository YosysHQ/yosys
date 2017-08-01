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

set(SOURCE_FILES ${SOURCE_FILES} ${CMAKE_CURRENT_LIST_DIR}/smt2.cc)
if (NOT MINGW AND NOT BUILD_EMSCRIPTEN)
add_custom_target(${PROJECT_NAME}-smtbmc ALL
                  BYPRODUCTS ${CMAKE_CURRENT_BINARY_DIR}/yosys-smtbmc
                  COMMAND sed \'s|\#\#yosys-sys-path\#\#|sys.path += [os.path.dirname(__file__) + p for p in [\"/share/python3\", \"/../share/yosys/python3\"]]|;\'< ${CMAKE_SOURCE_DIR}/backends/smt2/smtbmc.py > ${CMAKE_CURRENT_BINARY_DIR}/yosys-smtbmc
                  DEPENDS ${CMAKE_SOURCE_DIR}/backends/smt2/smtbmc.py
                  WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}
                  COMMENT "Generating yosys-smtbmc"
                  )
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/yosys-smtbmc DESTINATION ${CMAKE_INSTALL_BINDIR} PERMISSIONS OWNER_EXECUTE OWNER_WRITE OWNER_READ
GROUP_EXECUTE GROUP_READ WORLD_READ WORLD_EXECUTE)
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/share/)
add_custom_target(custom-python3-executable ALL
                BYPRODUCTS
                ${CMAKE_CURRENT_BINARY_DIR}/share/python3
                COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_LIST_DIR}/smtio.py ${CMAKE_CURRENT_BINARY_DIR}/share/python3
                DEPENDS ${CMAKE_CURRENT_LIST_DIR}/smtio.py
                WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}
                COMMENT "Generating ${CMAKE_CURRENT_BINARY_DIR}/share/python3")
endif(NOT MINGW AND NOT BUILD_EMSCRIPTEN)
