#include <string>
#include <unistd.h>
#include "kernel/yosys_common.h"

#ifndef YOSYS_GZIP_H
#define YOSYS_GZIP_H

YOSYS_NAMESPACE_BEGIN

#ifdef YOSYS_ENABLE_ZLIB

namespace Zlib {
#include <zlib.h>
} // namespace

/*
An output stream that uses a stringbuf to buffer data internally,
using zlib to write gzip-compressed data every time the stream is flushed.
*/
class gzip_ostream : public std::ostream {
public:
    gzip_ostream();
    bool open(const std::string &filename);
private:
    class gzip_streambuf : public std::stringbuf {
    public:
        gzip_streambuf();
        bool open(const std::string &filename);
        virtual int sync() override;
        virtual ~gzip_streambuf();
    private:
        static const int buffer_size = 4096;  // Size of the internal buffer
        char buffer[buffer_size];             // Internal buffer for compressed data
        Zlib::gzFile gzf = nullptr;                 // Handle to the gzip file
    };

    gzip_streambuf outbuf;  // The stream buffer instance
};
#endif // YOSYS_ENABLE_ZLIB

std::istream* uncompressed(std::ifstream* f, const std::string filename);

YOSYS_NAMESPACE_END

#endif // YOSYS_GZIP_H
