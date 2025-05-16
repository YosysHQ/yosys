#include "kernel/yosys_common.h"
#include "kernel/log.h"
#include <iostream>
#include <string>

#if !defined(WIN32)
#include <dirent.h>
#include <unistd.h>
#else
#include <io.h>
#endif

YOSYS_NAMESPACE_BEGIN

// Set of utilities for handling files

int readsome(std::istream &f, char *s, int n)
{
	int rc = int(f.readsome(s, n));

	// f.readsome() sometimes returns 0 on a non-empty stream..
	if (rc == 0) {
		int c = f.get();
		if (c != EOF) {
			*s = c;
			rc = 1;
		}
	}

	return rc;
}

std::string next_token(std::string &text, const char *sep, bool long_strings)
{
	size_t pos_begin = text.find_first_not_of(sep);

	if (pos_begin == std::string::npos)
		pos_begin = text.size();

	if (long_strings && pos_begin != text.size() && text[pos_begin] == '"') {
		std::string sep_string = sep;
		for (size_t i = pos_begin+1; i < text.size(); i++) {
			if (text[i] == '"' && (i+1 == text.size() || sep_string.find(text[i+1]) != std::string::npos)) {
				std::string token = text.substr(pos_begin, i-pos_begin+1);
				text = text.substr(i+1);
				return token;
			}
			if (i+1 < text.size() && text[i] == '"' && text[i+1] == ';' && (i+2 == text.size() || sep_string.find(text[i+2]) != std::string::npos)) {
				std::string token = text.substr(pos_begin, i-pos_begin+1);
				text = text.substr(i+2);
				return token + ";";
			}
		}
	}

	size_t pos_end = text.find_first_of(sep, pos_begin);

	if (pos_end == std::string::npos)
		pos_end = text.size();

	std::string token = text.substr(pos_begin, pos_end-pos_begin);
	text = text.substr(pos_end);
	return token;
}

std::vector<std::string> split_tokens(const std::string &text, const char *sep)
{
	std::vector<std::string> tokens;
	std::string current_token;
	for (char c : text) {
		if (strchr(sep, c)) {
			if (!current_token.empty()) {
				tokens.push_back(current_token);
				current_token.clear();
			}
		} else
			current_token += c;
	}
	if (!current_token.empty()) {
		tokens.push_back(current_token);
		current_token.clear();
	}
	return tokens;
}

// this is very similar to fnmatch(). the exact rules used by this
// function are:
//
//    ?        matches any character except
//    *        matches any sequence of characters
//    [...]    matches any of the characters in the list
//    [!..]    matches any of the characters not in the list
//
// a backslash may be used to escape the next characters in the
// pattern. each special character can also simply match itself.
//
bool patmatch(const char *pattern, const char *string)
{
	if (*pattern == 0)
		return *string == 0;

	if (*pattern == '\\') {
		if (pattern[1] == string[0] && patmatch(pattern+2, string+1))
			return true;
	}

	if (*pattern == '?') {
		if (*string == 0)
			return false;
		return patmatch(pattern+1, string+1);
	}

	if (*pattern == '*') {
		while (*string) {
			if (patmatch(pattern+1, string++))
				return true;
		}
		return pattern[1] == 0;
	}

	if (*pattern == '[') {
		bool found_match = false;
		bool inverted_list = pattern[1] == '!';
		const char *p = pattern + (inverted_list ? 1 : 0);

		while (*++p) {
			if (*p == ']') {
				if (found_match != inverted_list && patmatch(p+1, string+1))
					return true;
				break;
			}

			if (*p == '\\') {
				if (*++p == *string)
					found_match = true;
			} else
			if (*p == *string)
				found_match = true;
		}
	}

	if (*pattern == *string)
		return patmatch(pattern+1, string+1);

	return false;
}

std::string get_base_tmpdir()
{
	static std::string tmpdir;

	if (!tmpdir.empty()) {
		return tmpdir;
	}

#if defined(_WIN32)
#  ifdef __MINGW32__
	char longpath[MAX_PATH + 1];
	char shortpath[MAX_PATH + 1];
#  else
	WCHAR longpath[MAX_PATH + 1];
	TCHAR shortpath[MAX_PATH + 1];
#  endif
	if (!GetTempPath(MAX_PATH+1, longpath))
		log_error("GetTempPath() failed.\n");
	if (!GetShortPathName(longpath, shortpath, MAX_PATH + 1))
		log_error("GetShortPathName() failed.\n");
	for (int i = 0; shortpath[i]; i++)
		tmpdir += char(shortpath[i]);
#else
	char * var = std::getenv("TMPDIR");
	if (var && strlen(var)!=0) {
		tmpdir.assign(var);
		// We return the directory name without the trailing '/'
		while (!tmpdir.empty() && (tmpdir.back() == '/')) {
			tmpdir.pop_back();
		}
	} else {
		tmpdir.assign("/tmp");
	}
#endif
	return tmpdir;
}

std::string make_temp_file(std::string template_str)
{
	size_t pos = template_str.rfind("XXXXXX");
	log_assert(pos != std::string::npos);
#if defined(__wasm)
	static size_t index = 0;
	template_str.replace(pos, 6, stringf("%06zu", index++));
#elif defined(_WIN32)
#ifndef YOSYS_WIN32_UNIX_DIR
	std::replace(template_str.begin(), template_str.end(), '/', '\\');
#endif
	while (1) {
		for (int i = 0; i < 6; i++) {
			static std::string y = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
			static uint32_t x = 314159265 ^ uint32_t(time(NULL));
			x ^= x << 13, x ^= x >> 17, x ^= x << 5;
			template_str[pos+i] = y[x % y.size()];
		}
		if (_access(template_str.c_str(), 0) != 0)
			break;
	}
#else
	int suffixlen = template_str.size() - pos - 6;

	char *p = strdup(template_str.c_str());
	close(mkstemps(p, suffixlen));
	template_str = p;
	free(p);
#endif

	return template_str;
}

std::string make_temp_dir(std::string template_str)
{
#if defined(_WIN32)
	template_str = make_temp_file(template_str);
	mkdir(template_str.c_str());
	return template_str;
#elif defined(__wasm)
	template_str = make_temp_file(template_str);
	mkdir(template_str.c_str(), 0777);
	return template_str;
#else
#  ifndef NDEBUG
	size_t pos = template_str.rfind("XXXXXX");
	log_assert(pos != std::string::npos);

	int suffixlen = template_str.size() - pos - 6;
	log_assert(suffixlen == 0);
#  endif

	char *p = strdup(template_str.c_str());
	log_assert(p);
	char *res = mkdtemp(p);
	if (!res)
		log_error("mkdtemp failed for '%s': %s [Error %d]\n",
			p, strerror(errno), errno);
	template_str = p;
	free(p);

	return template_str;
#endif
}

bool check_is_directory(const std::string& dirname)
{
#if defined(_WIN32)
	struct _stat info;
	auto dirname_ = dirname;

	/* On old versions of Visual Studio and current versions on MinGW,
	   _stat will fail if the path ends with a trailing slash. */
	if (dirname.back() == '/' || dirname.back() == '\\') {
		dirname_ = dirname.substr(0, dirname.length() - 1);
	}

	if (_stat(dirname_.c_str(), &info) != 0)
	{
		return false;
	}
	return (info.st_mode & _S_IFDIR) != 0;
#else
	struct stat info;
	if (stat(dirname.c_str(), &info) != 0)
	{
		return false;
	}
	return (info.st_mode & S_IFDIR) != 0;
#endif
}

#ifdef _WIN32
bool check_accessible(const std::string& filename, bool)
{
	return _access(filename.c_str(), 0) == 0;
}
#else
bool check_accessible(const std::string& filename, bool is_exec)
{
	return access(filename.c_str(), is_exec ? X_OK : F_OK) == 0;
}
#endif

bool check_file_exists(const std::string& filename, bool is_exec)
{
	return check_accessible(filename, is_exec) && !check_is_directory(filename);
}
bool check_directory_exists(const std::string& filename, bool is_exec)
{
	return check_accessible(filename, is_exec) && check_is_directory(filename);
}

bool is_absolute_path(std::string filename)
{
#ifdef _WIN32
	return filename[0] == '/' || filename[0] == '\\' || (filename[0] != 0 && filename[1] == ':');
#else
	return filename[0] == '/';
#endif
}

void remove_directory(std::string dirname)
{
#ifdef _WIN32
	run_command(stringf("rmdir /s /q \"%s\"", dirname.c_str()));
#else
	struct stat stbuf;
	struct dirent **namelist;
	int n = scandir(dirname.c_str(), &namelist, nullptr, alphasort);
	log_assert(n >= 0);
	for (int i = 0; i < n; i++) {
		if (strcmp(namelist[i]->d_name, ".") && strcmp(namelist[i]->d_name, "..")) {
			std::string buffer = stringf("%s/%s", dirname.c_str(), namelist[i]->d_name);
			if (!stat(buffer.c_str(), &stbuf) && S_ISREG(stbuf.st_mode)) {
				remove(buffer.c_str());
			} else
				remove_directory(buffer);
		}
		free(namelist[i]);
	}
	free(namelist);
	rmdir(dirname.c_str());
#endif
}

bool create_directory(const std::string& dirname)
{
#if defined(_WIN32)
	int ret = _mkdir(dirname.c_str());
#else
	mode_t mode = 0755;
	int ret = mkdir(dirname.c_str(), mode);
#endif
	if (ret == 0)
		return true;

	switch (errno)
	{
	case ENOENT:
		// parent didn't exist, try to create it
		{
			std::string::size_type pos = dirname.find_last_of('/');
			if (pos == std::string::npos)
#if defined(_WIN32)
				pos = dirname.find_last_of('\\');
			if (pos == std::string::npos)
#endif
				return false;
			if (!create_directory( dirname.substr(0, pos) ))
				return false;
		}
		// now, try to create again
#if defined(_WIN32)
		return 0 == _mkdir(dirname.c_str());
#else
		return 0 == mkdir(dirname.c_str(), mode);
#endif

	case EEXIST:
		// done!
		return check_directory_exists(dirname);

	default:
		return false;
	}
}

std::string escape_filename_spaces(const std::string& filename)
{
	std::string out;
	out.reserve(filename.size());
	for (auto c : filename)
	{
		if (c == ' ')
			out += "\\ ";
		else
			out.push_back(c);
	}
	return out;
}

YOSYS_NAMESPACE_END
