// -------------------------------------------------------
// Written by Mohamed Gaber in 2025 <me@donn.website>
// -------------------------------------------------------
// This header is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.
//
// In jurisdictions that recognize copyright laws, the author or authors
// of this software dedicate any and all copyright interest in the
// software to the public domain. We make this dedication for the benefit
// of the public at large and to the detriment of our heirs and
// successors. We intend this dedication to be an overt act of
// relinquishment in perpetuity of all present and future rights to this
// software under copyright law.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.
//
// For more information, please refer to <https://unlicense.org/>
// -------------------------------------------------------
//
// pybind11 bridging header from objects supporting write() and flush()
// to iostream, unbuffered
//
#include <ostream>
#include <pybind11/pybind11.h>

namespace pybind11 {

#ifdef PYTHON_OSTREAM_NO_PROPAGATE_EXC
#include <cstdio>

#define PYTHON_OSTREAM_HANDLE_EXC(e, retval) {
    fprintf(stderr, "%s\n", e.what()); \
    return retval; \
}
#else
#define PYTHON_OSTREAM_HANDLE_EXC(e, retval) throw
#endif

class python_ostream : public std::ostream, public std::basic_streambuf<char> {
public:
    using traits_type = std::char_traits<char>;

    python_ostream(object writable): std::ostream(this), writable_(writable) {
    #ifndef PYTHON_OSTREAM_NO_PROPAGATE_EXC
        exceptions(std::ios::failbit | std::ios::badbit);
    #endif
    };

    int sync() override {
        gil_scoped_acquire ga;
        try {
            writable_.attr("flush")();
            return 0;
        } catch (error_already_set &e) {
            PYTHON_OSTREAM_HANDLE_EXC(e, -1);
        }
    }

    std::streamsize xsputn(const char *s, std::streamsize count) override {
        gil_scoped_acquire ga;
        try {
            auto result = writable_.attr("write")(str(s, count));
            return cast<std::streamsize>(result);
        } catch (error_already_set &e) {
            PYTHON_OSTREAM_HANDLE_EXC(e, 0);
        }
    }

    int overflow(int ch = traits_type::eof()) override {
        if (ch == traits_type::eof()) {
            return traits_type::eof();
        }
        try {
            gil_scoped_acquire ga;
            char target = ch;
            auto written = cast<std::streamsize>(writable_.attr("write")(str(&target, 1)));
            if (written == 0) { // can only be 0 or 1
                return traits_type::eof();
            }
        } catch (error_already_set &e) {
            PYTHON_OSTREAM_HANDLE_EXC(e, traits_type::eof());
        }
        return ch;
    }
private:
    object writable_; // keep reference while this object is alive
};

#undef PYTHON_OSTREAM_EXC
} // namespace pybind11
