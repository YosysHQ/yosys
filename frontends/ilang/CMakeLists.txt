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

#Flex/Bison calls
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/frontends/ilang/)
bison_target(ilang_parser ${CMAKE_CURRENT_LIST_DIR}/ilang_parser.y ${CMAKE_CURRENT_BINARY_DIR}/frontends/ilang/ilang_parser.tab.cc DEFINES_FILE
             ${CMAKE_CURRENT_BINARY_DIR}/frontends/ilang/ilang_parser.tab.h)
flex_target(ilang_lexer ${CMAKE_CURRENT_LIST_DIR}/ilang_lexer.l ${CMAKE_CURRENT_BINARY_DIR}/frontends/ilang/ilang_lexer.cc)
ADD_FLEX_BISON_DEPENDENCY(ilang_lexer ilang_parser)
set(SOURCE_FILES
    ${SOURCE_FILES}
    ${BISON_ilang_parser_OUTPUTS}
    ${FLEX_ilang_lexer_OUTPUTS}
    ${CMAKE_CURRENT_LIST_DIR}/ilang_frontend.cc
    )