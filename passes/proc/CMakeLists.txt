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
    ${CMAKE_CURRENT_LIST_DIR}/proc.cc
    ${CMAKE_CURRENT_LIST_DIR}/proc_clean.cc
    ${CMAKE_CURRENT_LIST_DIR}/proc_rmdead.cc
    ${CMAKE_CURRENT_LIST_DIR}/proc_init.cc
    ${CMAKE_CURRENT_LIST_DIR}/proc_arst.cc
    ${CMAKE_CURRENT_LIST_DIR}/proc_mux.cc
    ${CMAKE_CURRENT_LIST_DIR}/proc_dlatch.cc
    ${CMAKE_CURRENT_LIST_DIR}/proc_dff.cc
    )