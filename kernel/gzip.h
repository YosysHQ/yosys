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

/*
An input stream that uses zlib to read gzip-compressed data from a file,
buffering the decompressed data internally using a stringbuf.
*/
class gzip_istream final : public std::istream {
public:
    gzip_istream() : std::istream(&inbuf) {}

    bool open(const std::string& filename) {
        return inbuf.open(filename);
    }

private:
    class gzip_streambuf final : public std::streambuf {
    public:
        gzip_streambuf() : gzf(nullptr) {}

        bool open(const std::string& filename) {
            if (gzf) {
                Zlib::gzclose(gzf);
            }
            gzf = Zlib::gzopen(filename.c_str(), "rb");
            if (!gzf) {
                return false;
            }
            // Set up the get buffer
            setg(buffer,        // beginning of buffer
                 buffer,        // current position
                 buffer);       // end position (initially empty)
            return true;
        }
        virtual ~gzip_streambuf() {
            if (gzf) {
                Zlib::gzclose(gzf);
            }
        }

    protected:
        // Called when the buffer is empty and more input is needed
        virtual int_type underflow() override {
            if (gzf == nullptr) {
                return traits_type::eof();
            }
            int bytes_read = Zlib::gzread(gzf, buffer, buffer_size);
            if (bytes_read <= 0) {
                // An error occurred during reading
                int err;
                const char* error_msg = Zlib::gzerror(gzf, &err);
				if (err != Z_STREAM_END)
					log_error("%s", error_msg);
                return traits_type::eof();
            }

            // Reset buffer pointers
            setg(buffer,        // beginning of buffer
                 buffer,        // current position
                 buffer + bytes_read); // end position
            return traits_type::to_int_type(buffer[0]);
        }

    private:
        static const int buffer_size = 4096;
        char buffer[buffer_size];
        Zlib::gzFile gzf;
    };

    gzip_streambuf inbuf;  // The stream buffer instance
};

#endif // YOSYS_ENABLE_ZLIB

std::istream* uncompressed(std::ifstream* f, const std::string filename);

YOSYS_NAMESPACE_END

#endif // YOSYS_GZIP_H
