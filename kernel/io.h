#include <string>
#include <stdarg.h>
#include "kernel/yosys_common.h"

#ifndef YOSYS_IO_H
#define YOSYS_IO_H

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

int readsome(std::istream &f, char *s, int n);
std::string next_token(std::string &text, const char *sep = " \t\r\n", bool long_strings = false);
std::vector<std::string> split_tokens(const std::string &text, const char *sep = " \t\r\n");
bool patmatch(const char *pattern, const char *string);
#if !defined(YOSYS_DISABLE_SPAWN)
int run_command(const std::string &command, std::function<void(const std::string&)> process_line = std::function<void(const std::string&)>());
#endif
std::string get_base_tmpdir();
std::string make_temp_file(std::string template_str = get_base_tmpdir() + "/yosys_XXXXXX");
std::string make_temp_dir(std::string template_str = get_base_tmpdir() + "/yosys_XXXXXX");
bool check_file_exists(const std::string& filename, bool is_exec = false);
bool check_directory_exists(const std::string& dirname, bool is_exec = false);
bool is_absolute_path(std::string filename);
void remove_directory(std::string dirname);
bool create_directory(const std::string& dirname);
std::string escape_filename_spaces(const std::string& filename);

YOSYS_NAMESPACE_END

#endif // YOSYS_IO_H
