#ifndef VERILOG_LOCATION_H
#define VERILOG_LOCATION_H

#include <memory>
#include <string>
#include <stack>
#include <string>
#include <sstream>

/**
 * Provide frontend-wide location tracking like what bison generates
 * but using shared_ptr for filename
 */

struct Position {
	std::shared_ptr<std::string> filename;
	int line;
	int column;

	Position(std::shared_ptr<std::string> filename, int line = 1, int column = 1)
		: filename(filename), line(line), column(column) {}
	Position() = default;
	Position(const Position& other) = default;
	Position& operator=(const Position& other) = default;

	void advance() { ++column; }
	void columns(int count = 1) {
		column += count;
	}

	void lines(int count = 1) {
		line += count;
		column = 1;
	}
	std::string to_string() const  {
		std::ostringstream oss;
		if (filename && !filename->empty()) {
			oss << *filename << ":";
		}
		oss << line << ":" << column;
		return oss.str();
	}
};

struct Location {
	Position begin;
	Position end;

	Location() = default;
	Location(const Position& b, const Position& e)
		: begin(b), end(e) {}
	Location(const Location& other) = default;
	Location& operator=(const Location& other) = default;

	void step() { begin = end; }

	void columns(int count = 1) {
		end.columns(count);
	}

	void lines(int count = 1) {
		end.lines(count);
	}
	std::string to_string() const {
		std::ostringstream oss;
		bool same_file = (!begin.filename && !end.filename) ||
						(begin.filename && end.filename &&
						*begin.filename == *end.filename);

		if (same_file) {
			if (begin.filename && !begin.filename->empty())
				oss << *begin.filename << ":";

			if (begin.line == end.line) {
				if (begin.column == end.column) {
					oss << begin.line << ":" << begin.column;
				} else {
					oss << begin.line << ":" << begin.column
						<< "-" << end.column;
				}
			} else {
				oss << begin.line << ":" << begin.column
					<< "-" << end.line << ":" << end.column;
			}
		} else {
			oss << begin.to_string() << "-" << end.to_string();
		}

		return oss.str();
	}
};

static inline std::ostream& operator<<(std::ostream& os, const Location& loc) {
	return os << loc.to_string();
}

#endif
