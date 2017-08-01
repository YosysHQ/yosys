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
#

option(SANITIZE_CFI "Enable ControlFlowIntegritySanitizer for sanitized targets." Off)

set(FLAG_CANDIDATES
    # Clang 3.2+ use this version. The no-omit-frame-pointer option is optional.
    "-g -flto -fsanitize=cfi"
    "-g -flto"
)


#if (SANITIZE_CFI AND (SANITIZE_THREAD OR SANITIZE_MEMORY))
#    message(FATAL_ERROR "AddressSanitizer is not compatible with "
#        "ThreadSanitizer or MemorySanitizer.")
#endif ()


include(sanitize-helpers)

if (SANITIZE_CFI)
    sanitizer_check_compiler_flags("${FLAG_CANDIDATES}" "ControlFlowIntegritySanitizer"
        "CFISan")

    find_program(CSISan_WRAPPER "csisan-wrapper" PATHS ${CMAKE_MODULE_PATH})
	mark_as_advanced(CSISan_WRAPPER)
endif ()

function (add_sanitize_cfi TARGET)
    if (NOT SANITIZE_CFI)
        return()
    endif ()

    saitizer_add_flags(${TARGET} "ControlFlowIntegritySanitizer" "CFISan")
endfunction ()
