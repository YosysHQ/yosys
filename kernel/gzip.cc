#include "kernel/yosys_common.h"
#include "kernel/log.h"
#include "kernel/gzip.h"
#include <iostream>
#include <dirent.h>
#include <string>
#include <cstdarg>
#include <cstdio>

YOSYS_NAMESPACE_BEGIN


#ifdef YOSYS_ENABLE_ZLIB

PRIVATE_NAMESPACE_BEGIN

using namespace Zlib;

static const size_t GZ_BUFFER_SIZE = 8192;
static void decompress_gzip(const std::string &filename, std::stringstream &out)
{
    char buffer[GZ_BUFFER_SIZE];
    int bytes_read;
    gzFile gzf = gzopen(filename.c_str(), "rb");
    while(!gzeof(gzf)) {
        bytes_read = gzread(gzf, reinterpret_cast<void *>(buffer), GZ_BUFFER_SIZE);
        out.write(buffer, bytes_read);
    }
    gzclose(gzf);
}

PRIVATE_NAMESPACE_END

gzip_ostream::gzip_ostream() : std::ostream(nullptr) {
    rdbuf(&outbuf);
}

bool gzip_ostream::open(const std::string &filename) {
    return outbuf.open(filename);
}

gzip_ostream::gzip_streambuf::gzip_streambuf() {
    setp(buffer, buffer + buffer_size - 1);
}

bool gzip_ostream::gzip_streambuf::open(const std::string &filename) {
    gzf = gzopen(filename.c_str(), "wb");
    return gzf != nullptr;
}

int gzip_ostream::gzip_streambuf::sync() {
    int num = pptr() - pbase();
    if (num > 0) {
        if (gzwrite(gzf, reinterpret_cast<const void*>(pbase()), num) != num) {
            return -1;
        }
        pbump(-num);
    }
    return 0;
}

gzip_ostream::gzip_streambuf::~gzip_streambuf() {
    if (gzf) {
        sync();
        gzclose(gzf);
    }
}

#endif // YOSYS_ENABLE_ZLIB


// Takes a successfully opened ifstream. If it's gzipped, returns an istream
// over a buffer of the file fully decompressed in memory. Otherwise,
// returns the original ifstream, rewound to the start.
std::istream* uncompressed(std::ifstream* f, const std::string filename) {
	if (!f)
		return nullptr;
	// Check for gzip magic
	unsigned char magic[3];
	int n = 0;
	while (n < 3)
	{
		int c = f->get();
		if (c != EOF) {
			magic[n] = (unsigned char) c;
		}
		n++;
	}
	if (n == 3 && magic[0] == 0x1f && magic[1] == 0x8b) {
#ifdef YOSYS_ENABLE_ZLIB
		log("Found gzip magic in file `%s', decompressing using zlib.\n", filename.c_str());
		if (magic[2] != 8)
			log_cmd_error("gzip file `%s' uses unsupported compression type %02x\n",
				filename.c_str(), unsigned(magic[2]));
		delete f;
		// std::stringstream *df = new std::stringstream();
		// decompress_gzip(filename, *df);
		gzip_istream* s = new gzip_istream();
		return s->open(filename.c_str()) ? s : nullptr;
#else
		log_cmd_error("File `%s' is a gzip file, but Yosys is compiled without zlib.\n", filename.c_str());
#endif // YOSYS_ENABLE_ZLIB
	} else {
		f->clear();
		f->seekg(0, std::ios::beg);
		return f;
	}
}

YOSYS_NAMESPACE_END
