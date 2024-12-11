#include "kernel/yosys_common.h"
#include <string>

#ifndef YOSYS_IO_H
#define YOSYS_IO_H

#ifdef YOSYS_ENABLE_ZLIB
#include <zlib.h>
#endif

YOSYS_NAMESPACE_BEGIN

inline std::string vstringf(const char *fmt, va_list ap)
{
	// For the common case of strings shorter than 128, save a heap
	// allocation by using a stack allocated buffer.
	const int kBufSize = 128;
	char buf[kBufSize];
	buf[0] = '\0';
	va_list apc;
	va_copy(apc, ap);
	int n = vsnprintf(buf, kBufSize, fmt, apc);
	va_end(apc);
	if (n < kBufSize)
		return std::string(buf);

	std::string string;
	char *str = NULL;
#if defined(_WIN32) || defined(__CYGWIN__)
	int sz = 2 * kBufSize, rc;
	while (1) {
		va_copy(apc, ap);
		str = (char *)realloc(str, sz);
		rc = vsnprintf(str, sz, fmt, apc);
		va_end(apc);
		if (rc >= 0 && rc < sz)
			break;
		sz *= 2;
	}
	if (str != NULL) {
		string = str;
		free(str);
	}
	return string;
#else
	if (vasprintf(&str, fmt, ap) < 0)
		str = NULL;
	if (str != NULL) {
		string = str;
		free(str);
	}
	return string;
#endif
}

std::string stringf(const char *fmt, ...) YS_ATTRIBUTE(format(printf, 1, 2));

inline std::string stringf(const char *fmt, ...)
{
	std::string string;
	va_list ap;

	va_start(ap, fmt);
	string = vstringf(fmt, ap);
	va_end(ap);

	return string;
}

#ifdef YOSYS_ENABLE_ZLIB
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
        gzFile gzf = nullptr;                 // Handle to the gzip file
    };

    gzip_streambuf outbuf;  // The stream buffer instance
};
#endif // YOSYS_ENABLE_ZLIB

std::istream* uncompressed(std::ifstream* f, const std::string filename);

YOSYS_NAMESPACE_END

#endif // YOSYS_IO_H
