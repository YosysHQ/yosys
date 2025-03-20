#include <string>
#include "kernel/yosys_common.h"

#ifndef YOSYS_GZIP_H
#define YOSYS_GZIP_H

YOSYS_NAMESPACE_BEGIN

#ifdef YOSYS_ENABLE_ZLIB

namespace Zlib {
#include <zlib.h>
}

/*
An output stream that uses a stringbuf to buffer data internally,
using zlib to write gzip-compressed data every time the stream is flushed.
*/
class gzip_ostream : public std::ostream {
public:
	gzip_ostream(): std::ostream(nullptr) {
		rdbuf(&outbuf);
	}
	bool open(const std::string &filename) {
		return outbuf.open(filename);
	}
private:
	class obuf : public std::stringbuf {
	public:
		obuf();
		bool open(const std::string &filename);
		virtual int sync() override;
		virtual ~obuf();
	private:
		static const int buffer_size = 4096;
		char buffer[buffer_size];             // Internal buffer for compressed data
		Zlib::gzFile gzf = nullptr;                 // Handle to the gzip file
	};

	obuf outbuf;  // The stream buffer instance
};

/*
An input stream that uses zlib to read gzip-compressed data from a file,
buffering the decompressed data internally using its own buffer.
*/
class gzip_istream final : public std::istream {
public:
	gzip_istream() : std::istream(&inbuf) {}
	bool open(const std::string& filename) {
		return inbuf.open(filename);
	}
private:
	class ibuf final : public std::streambuf {
	public:
		ibuf() : gzf(nullptr) {}
		bool open(const std::string& filename);
		virtual ~ibuf();

	protected:
		// Called when the buffer is empty and more input is needed
		virtual int_type underflow() override;
	private:
		static const int buffer_size = 8192;
		char buffer[buffer_size];
		Zlib::gzFile gzf;
	};

	ibuf inbuf;  // The stream buffer instance
};

#endif // YOSYS_ENABLE_ZLIB

std::istream* uncompressed(const std::string filename, std::ios_base::openmode mode = std::ios_base::in);

YOSYS_NAMESPACE_END

#endif // YOSYS_GZIP_H
