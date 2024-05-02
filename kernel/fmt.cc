/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  whitequark <whitequark@whitequark.org>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "libs/bigint/BigUnsigned.hh"
#include "kernel/fmt.h"

USING_YOSYS_NAMESPACE

void Fmt::append_literal(const std::string &str) {
	FmtPart part = {};
	part.type = FmtPart::LITERAL;
	part.str = str;
	parts.push_back(part);
}

void Fmt::parse_rtlil(const RTLIL::Cell *cell) {
	std::string fmt = cell->getParam(ID(FORMAT)).decode_string();
	RTLIL::SigSpec args = cell->getPort(ID(ARGS));
	parts.clear();

	FmtPart part;
	for (size_t i = 0; i < fmt.size(); i++) {
		if (fmt.substr(i, 2) == "}}") {
			part.str += '}';
			++i;
		} else if (fmt.substr(i, 2) == "{{") {
			part.str += '{';
			++i;
		} else if (fmt[i] == '}') {
			log_assert(false && "Unexpected '}' in format string");
		} else if (fmt[i] == '{') {
			if (!part.str.empty()) {
				part.type = FmtPart::LITERAL;
				parts.push_back(part);
				part = {};
			}

			if (++i == fmt.size())
				log_assert(false && "Unexpected end in format substitution");

			size_t arg_size = 0;
			for (; i < fmt.size(); i++) {
				if (fmt[i] >= '0' && fmt[i] <= '9') {
					arg_size *= 10;
					arg_size += fmt[i] - '0';
				} else if (fmt[i] == ':') {
					++i;
					break;
				} else {
					log_assert(false && "Unexpected character in format substitution");
				}
			}
			if (i == fmt.size())
				log_assert(false && "Unexpected end in format substitution");

			if ((size_t)args.size() < arg_size)
				log_assert(false && "Format part overruns arguments");
			part.sig = args.extract(0, arg_size);
			args.remove(0, arg_size);

			if (fmt[i] == 'U') {
				part.type = FmtPart::UNICHAR;
				++i;
				goto success;
			}

			if (fmt[i] == '>')
				part.justify = FmtPart::RIGHT;
			else if (fmt[i] == '<')
				part.justify = FmtPart::LEFT;
			else if (fmt[i] == '=')
				part.justify = FmtPart::NUMERIC;
			else
				log_assert(false && "Unexpected justification in format substitution");
			if (++i == fmt.size())
				log_assert(false && "Unexpected end in format substitution");

			part.padding = fmt[i];
			if (++i == fmt.size())
				log_assert(false && "Unexpected end in format substitution");

			for (; i < fmt.size(); i++) {
				if (fmt[i] >= '0' && fmt[i] <= '9') {
					part.width *= 10;
					part.width += fmt[i] - '0';
					continue;
				} else if (fmt[i] == 'b') {
					part.type = FmtPart::INTEGER;
					part.base = 2;
				} else if (fmt[i] == 'o') {
					part.type = FmtPart::INTEGER;
					part.base = 8;
				} else if (fmt[i] == 'd') {
					part.type = FmtPart::INTEGER;
					part.base = 10;
				} else if (fmt[i] == 'h') {
					part.type = FmtPart::INTEGER;
					part.base = 16;
				} else if (fmt[i] == 'H') {
					part.type = FmtPart::INTEGER;
					part.base = 16;
					part.hex_upper = true;
				} else if (fmt[i] == 'c') {
					part.type = FmtPart::STRING;
				} else if (fmt[i] == 't') {
					part.type = FmtPart::VLOG_TIME;
				} else if (fmt[i] == 'r') {
					part.type = FmtPart::VLOG_TIME;
					part.realtime = true;
				} else {
					log_assert(false && "Unexpected character in format substitution");
				}
				++i;
				break;
			}
			if (i == fmt.size())
				log_assert(false && "Unexpected end in format substitution");

			if (part.type == FmtPart::INTEGER) {
				if (fmt[i] == '-') {
					part.sign = FmtPart::MINUS;
					if (++i == fmt.size())
						log_assert(false && "Unexpected end in format substitution");
				} else if (fmt[i] == '+') {
					part.sign = FmtPart::PLUS_MINUS;
					if (++i == fmt.size())
						log_assert(false && "Unexpected end in format substitution");
				} else if (fmt[i] == ' ') {
					part.sign = FmtPart::SPACE_MINUS;
					if (++i == fmt.size())
						log_assert(false && "Unexpected end in format substitution");
				} else {
					// also accept no sign character and treat like MINUS for compatibility
				}

				if (fmt[i] == '#') {
					part.show_base = true;
					++i;
				}
				if (fmt[i] == '_') {
					part.group = true;
					++i;
				}

				if (fmt[i] == 'u')
					part.signed_ = false;
				else if (fmt[i] == 's')
					part.signed_ = true;
				else
					log_assert(false && "Unexpected character in format substitution");
				if (++i == fmt.size())
					log_assert(false && "Unexpected end in format substitution");
			}

		success:
			if (fmt[i] != '}')
				log_assert(false && "Expected '}' after format substitution");

			parts.push_back(part);
			part = {};
		} else {
			part.str += fmt[i];
		}
	}
	if (!part.str.empty()) {
		part.type = FmtPart::LITERAL;
		parts.push_back(part);
	}
}

void Fmt::emit_rtlil(RTLIL::Cell *cell) const {
	std::string fmt;
	RTLIL::SigSpec args;

	for (auto &part : parts) {
		switch (part.type) {
			case FmtPart::LITERAL:
				for (char c : part.str) {
					if (c == '{')
						fmt += "{{";
					else if (c == '}')
						fmt += "}}";
					else
						fmt += c;
				}
				break;

			case FmtPart::UNICHAR:
				log_assert(part.sig.size() <= 32);
				fmt += "{U}";
				break;

			case FmtPart::VLOG_TIME:
				log_assert(part.sig.size() == 0);
				YS_FALLTHROUGH
			case FmtPart::STRING:
				log_assert(part.sig.size() % 8 == 0);
				YS_FALLTHROUGH
			case FmtPart::INTEGER:
				args.append(part.sig);
				fmt += '{';
				fmt += std::to_string(part.sig.size());
				fmt += ':';
				if (part.justify == FmtPart::RIGHT)
					fmt += '>';
				else if (part.justify == FmtPart::LEFT)
					fmt += '<';
				else if (part.justify == FmtPart::NUMERIC)
					fmt += '=';
				else log_abort();
				log_assert(part.width == 0 || part.padding != '\0');
				fmt += part.padding != '\0' ? part.padding : ' ';
				if (part.width > 0)
					fmt += std::to_string(part.width);
				if (part.type == FmtPart::INTEGER) {
					switch (part.base) {
						case  2: fmt += 'b'; break;
						case  8: fmt += 'o'; break;
						case 10: fmt += 'd'; break;
						case 16: fmt += part.hex_upper ? 'H' : 'h'; break;
						default: log_abort();
					}
					switch (part.sign) {
						case FmtPart::MINUS:       fmt += '-'; break;
						case FmtPart::PLUS_MINUS:  fmt += '+'; break;
						case FmtPart::SPACE_MINUS: fmt += ' '; break;
					}
					fmt += part.show_base ? "#" : "";
					fmt += part.group ? "_" : "";
					fmt += part.signed_ ? 's' : 'u';
				} else if (part.type == FmtPart::STRING) {
					fmt += 'c';
				} else if (part.type == FmtPart::VLOG_TIME) {
					if (part.realtime)
						fmt += 'r';
					else
						fmt += 't';
				} else log_abort();
				fmt += '}';
				break;

			default: log_abort();
		}
	}

	cell->setParam(ID(FORMAT), fmt);
	cell->setParam(ID(ARGS_WIDTH), args.size());
	cell->setPort(ID(ARGS), args);
}

static size_t compute_required_decimal_places(size_t size, bool signed_)
{
	BigUnsigned max;
	if (!signed_)
		max.setBit(size, true);
	else
		max.setBit(size - 1, true);
	size_t places = 0;
	while (!max.isZero()) {
		places++;
		max /= 10;
	}
	if (signed_)
		places++;
	return places;
}

static size_t compute_required_nondecimal_places(size_t size, unsigned base)
{
	log_assert(base != 10);
	BigUnsigned max;
	max.setBit(size - 1, true);
	size_t places = 0;
	while (!max.isZero()) {
		places++;
		max /= base;
	}
	return places;
}

// Only called for integers, either when:
//
// (a) passed without a format string (e.g. "$display(a);"), or
//
// (b) the corresponding format specifier has no leading zero, e.g. "%b",
// "%20h", "%-10d".
//
// In these cases, for binary/octal/hex, we always zero-pad to the size of the
// signal; i.e. whether "%h" or "%10h" or "%-20h" is used, if the corresponding
// signal is 32'h1234, "00001234" will always be a substring of the output.
//
// For case (a), we have no specified width, so there is nothing more to do.
//
// For case (b), because we are only called with no leading zero on the
// specifier, any specified width beyond the signal size is therefore space
// padding, whatever the justification.
//
// For decimal, we do no zero-padding, instead space-padding to the size
// required for the signal's largest value.  This is per other Verilog
// implementations, and intuitively makes sense as decimal representations lack
// a discrete mapping of digits to bit groups.  Decimals may also show sign and
// must accommodate this, whereas other representations do not.
void Fmt::apply_verilog_automatic_sizing_and_add(FmtPart &part)
{
	if (part.base == 10) {
		size_t places = compute_required_decimal_places(part.sig.size(), part.signed_);
		part.padding = ' ';
		part.width = std::max(part.width, places);
		parts.push_back(part);
		return;
	}

	part.padding = '0';

	size_t places = compute_required_nondecimal_places(part.sig.size(), part.base);
	if (part.width < places) {
		part.justify = FmtPart::RIGHT;
		part.width = places;
		parts.push_back(part);
	} else if (part.width == places) {
		parts.push_back(part);
	} else if (part.width > places) {
		auto gap = std::string(part.width - places, ' ');
		part.width = places;

		if (part.justify == FmtPart::RIGHT) {
			append_literal(gap);
			parts.push_back(part);
		} else {
			part.justify = FmtPart::RIGHT;
			parts.push_back(part);
			append_literal(gap);
		}
	}
}

void Fmt::parse_verilog(const std::vector<VerilogFmtArg> &args, bool sformat_like, int default_base, RTLIL::IdString task_name, RTLIL::IdString module_name)
{
	parts.clear();

	auto arg = args.begin();
	for (; arg != args.end(); ++arg) {
		switch (arg->type) {
			case VerilogFmtArg::INTEGER: {
				FmtPart part = {};
				part.type = FmtPart::INTEGER;
				part.sig = arg->sig;
				part.base = default_base;
				part.signed_ = arg->signed_;
				apply_verilog_automatic_sizing_and_add(part);
				break;
			}

			case VerilogFmtArg::TIME: {
				FmtPart part = {};
				part.type = FmtPart::VLOG_TIME;
				part.realtime = arg->realtime;
				part.padding = ' ';
				part.width = 20;
				parts.push_back(part);
				break;
			}

			case VerilogFmtArg::STRING: {
				if (arg == args.begin() || !sformat_like) {
					const auto fmtarg = arg;
					const std::string &fmt = fmtarg->str;
					FmtPart part = {};
					for (size_t i = 0; i < fmt.size(); i++) {
						if (fmt[i] != '%') {
							part.str += fmt[i];
						} else if (fmt.substr(i, 2) == "%%") {
							i++;
							part.str += '%';
						} else if (fmt.substr(i, 2) == "%l" || fmt.substr(i, 2) == "%L") {
							i++;
							part.str += module_name.str();
						} else if (fmt.substr(i, 2) == "%m" || fmt.substr(i, 2) == "%M") {
							i++;
							part.str += module_name.str();
						} else {
							if (!part.str.empty()) {
								part.type = FmtPart::LITERAL;
								parts.push_back(part);
								part = {};
							}
							if (++i == fmt.size()) {
								log_file_error(fmtarg->filename, fmtarg->first_line, "System task `%s' called with incomplete format specifier in argument %zu.\n", task_name.c_str(), fmtarg - args.begin() + 1);
							}

							if (++arg == args.end()) {
								log_file_error(fmtarg->filename, fmtarg->first_line, "System task `%s' called with fewer arguments than the format specifiers in argument %zu require.\n", task_name.c_str(), fmtarg - args.begin() + 1);
							}
							part.sig = arg->sig;
							part.signed_ = arg->signed_;

							for (; i < fmt.size(); i++) {
								if (fmt[i] == '-') {
									// left justify; not in IEEE 1800-2017 or verilator but iverilog has it
									part.justify = FmtPart::LEFT;
								} else if (fmt[i] == '+') {
									// always show sign; not in IEEE 1800-2017 or verilator but iverilog has it
									part.sign = FmtPart::PLUS_MINUS;
								} else break;
							}
							if (i == fmt.size()) {
								log_file_error(fmtarg->filename, fmtarg->first_line, "System task `%s' called with incomplete format specifier in argument %zu.\n", task_name.c_str(), fmtarg - args.begin() + 1);
							}

							bool has_leading_zero = false, has_width = false;
							for (; i < fmt.size(); i++) {
								if (fmt[i] >= '0' && fmt[i] <= '9') {
									if (fmt[i] == '0' && !has_width) {
										has_leading_zero = true;
									} else {
										has_width = true;
										part.width *= 10;
										part.width += fmt[i] - '0';
									}
									continue;
								} else if (fmt[i] == 'b' || fmt[i] == 'B') {
									part.type = FmtPart::INTEGER;
									part.base =  2;
								} else if (fmt[i] == 'o' || fmt[i] == 'O') {
									part.type = FmtPart::INTEGER;
									part.base =  8;
								} else if (fmt[i] == 'd' || fmt[i] == 'D') {
									part.type = FmtPart::INTEGER;
									part.base = 10;
								} else if (fmt[i] == 'h' || fmt[i] == 'H' ||
								           fmt[i] == 'x' || fmt[i] == 'X') {
									// hex digits always printed in lowercase for %h%x as well as %H%X
									part.type = FmtPart::INTEGER;
									part.base = 16;
								} else if (fmt[i] == 'c' || fmt[i] == 'C') {
									part.type = FmtPart::STRING;
									part.sig.extend_u0(8);
									// %10c and %010c not fully defined in IEEE 1800-2017 and do different things in iverilog
								} else if (fmt[i] == 's' || fmt[i] == 'S') {
									part.type = FmtPart::STRING;
									if ((part.sig.size() % 8) != 0)
										part.sig.extend_u0((part.sig.size() + 7) / 8 * 8);
									// %10s and %010s not fully defined in IEEE 1800-2017 and do the same thing in iverilog
									part.padding = ' ';
								} else if (fmt[i] == 't' || fmt[i] == 'T') {
									if (arg->type == VerilogFmtArg::TIME) {
										part.type = FmtPart::VLOG_TIME;
										part.realtime = arg->realtime;
										if (!has_width && !has_leading_zero)
											part.width = 20;
									} else {
										log_file_error(fmtarg->filename, fmtarg->first_line, "System task `%s' called with format character `%c' in argument %zu, but the argument is not $time or $realtime.\n", task_name.c_str(), fmt[i], fmtarg - args.begin() + 1);
									}
								} else {
									log_file_error(fmtarg->filename, fmtarg->first_line, "System task `%s' called with unrecognized format character `%c' in argument %zu.\n", task_name.c_str(), fmt[i], fmtarg - args.begin() + 1);
								}
								break;
							}
							if (i == fmt.size()) {
								log_file_error(fmtarg->filename, fmtarg->first_line, "System task `%s' called with incomplete format specifier in argument %zu.\n", task_name.c_str(), fmtarg - args.begin() + 1);
							}

							if (part.padding == '\0') {
								if (has_leading_zero && part.justify == FmtPart::RIGHT) {
									part.padding = '0';
									part.justify = FmtPart::NUMERIC;
								} else {
									part.padding = ' ';
								}
							}

							if (part.type == FmtPart::INTEGER && part.base != 10 && part.sign != FmtPart::MINUS)
								log_file_error(fmtarg->filename, fmtarg->first_line, "System task `%s' called with invalid format specifier in argument %zu.\n", task_name.c_str(), fmtarg - args.begin() + 1);

							if (part.base != 10)
								part.signed_ = false;
							if (part.type == FmtPart::INTEGER && !has_leading_zero)
								apply_verilog_automatic_sizing_and_add(part);
							else
								parts.push_back(part);
							part = {};
						}
					}
					if (!part.str.empty()) {
						part.type = FmtPart::LITERAL;
						parts.push_back(part);
					}
				} else {
					FmtPart part = {};
					part.type = FmtPart::LITERAL;
					part.str = arg->str;
					parts.push_back(part);
				}
				break;
			}

			default: log_abort();
		}
	}
}

std::vector<VerilogFmtArg> Fmt::emit_verilog() const
{
	std::vector<VerilogFmtArg> args;
	VerilogFmtArg fmt = {};
	fmt.type = VerilogFmtArg::STRING;

	for (auto &part : parts) {
		switch (part.type) {
			case FmtPart::LITERAL:
				for (char c : part.str) {
					if (c == '%')
						fmt.str += "%%";
					else
						fmt.str += c;
				}
				break;

			case FmtPart::INTEGER: {
				VerilogFmtArg arg = {};
				arg.type = VerilogFmtArg::INTEGER;
				arg.sig = part.sig;
				arg.signed_ = part.signed_;
				args.push_back(arg);

				fmt.str += '%';
				if (part.sign == FmtPart::PLUS_MINUS || part.sign == FmtPart::SPACE_MINUS)
					fmt.str += '+'; // treat space/minus as plus/minus
				if (part.justify == FmtPart::LEFT)
					fmt.str += '-';
				if (part.width == 0) {
					fmt.str += '0';
				} else if (part.width > 0) {
					if (part.base != 10 || part.padding == '0')
						fmt.str += '0';
					fmt.str += std::to_string(part.width);
				}
				switch (part.base) {
					case  2: fmt.str += 'b'; break;
					case  8: fmt.str += 'o'; break;
					case 10: fmt.str += 'd'; break;
					case 16: fmt.str += 'h'; break; // treat uppercase hex as lowercase
					default: log_abort();
				}
				break;
			}

			case FmtPart::STRING: {
				VerilogFmtArg arg;
				arg.type = VerilogFmtArg::INTEGER;
				arg.sig = part.sig;
				args.push_back(arg);

				fmt.str += '%';
				if (part.justify == FmtPart::LEFT)
					fmt.str += '-';
				if (part.sig.size() == 8) {
					if (part.width > 0) {
						if (part.padding == '0')
							fmt.str += part.padding;
						fmt.str += std::to_string(part.width);
					}
					fmt.str += 'c';
				} else {
					log_assert(part.sig.size() % 8 == 0);
					if (part.width > 0) {
						fmt.str += std::to_string(part.width);
					}
					fmt.str += 's';
				}
				break;
			}

			case FmtPart::UNICHAR: {
				VerilogFmtArg arg;
				arg.type = VerilogFmtArg::INTEGER;
				arg.sig = part.sig.extract(0, 7); // only ASCII
				args.push_back(arg);

				fmt.str += "%c";
				break;
			}

			case FmtPart::VLOG_TIME: {
				VerilogFmtArg arg;
				arg.type = VerilogFmtArg::TIME;
				if (part.realtime)
					arg.realtime = true;
				args.push_back(arg);

				fmt.str += '%';
				log_assert(part.sign == FmtPart::MINUS || part.sign == FmtPart::PLUS_MINUS);
				if (part.sign == FmtPart::PLUS_MINUS)
					fmt.str += '+';
				if (part.justify == FmtPart::LEFT)
					fmt.str += '-';
				if (part.padding == '0' && part.width > 0)
					fmt.str += '0';
				fmt.str += std::to_string(part.width);
				fmt.str += 't';
				break;
			}

			default: log_abort();
		}
	}

	args.insert(args.begin(), fmt);
	return args;
}

std::string escape_cxx_string(const std::string &input)
{
	std::string output = "\"";
	for (auto c : input) {
		if (::isprint(c)) {
			if (c == '\\')
				output.push_back('\\');
			output.push_back(c);
		} else {
			char l = c & 0xf, h = (c >> 4) & 0xf;
			output.append("\\x");
			output.push_back((h < 10 ? '0' + h : 'a' + h - 10));
			output.push_back((l < 10 ? '0' + l : 'a' + l - 10));
		}
	}
	output.push_back('"');
	if (output.find('\0') != std::string::npos) {
		output.insert(0, "std::string {");
		output.append(stringf(", %zu}", input.size()));
	}
	return output;
}

void Fmt::emit_cxxrtl(std::ostream &os, std::string indent, std::function<void(const RTLIL::SigSpec &)> emit_sig, const std::string &context) const
{
	os << indent << "std::string buf;\n";
	for (auto &part : parts) {
		os << indent << "buf += fmt_part { ";
		os << "fmt_part::";
		switch (part.type) {
			case FmtPart::LITERAL:   os << "LITERAL";   break;
			case FmtPart::INTEGER:   os << "INTEGER";   break;
			case FmtPart::STRING:    os << "STRING";    break;
			case FmtPart::UNICHAR:   os << "UNICHAR";   break;
			case FmtPart::VLOG_TIME: os << "VLOG_TIME"; break;
		}
		os << ", ";
		os << escape_cxx_string(part.str) << ", ";
		os << "fmt_part::";
		switch (part.justify) {
			case FmtPart::LEFT:    os << "LEFT";    break;
			case FmtPart::RIGHT:   os << "RIGHT";   break;
			case FmtPart::NUMERIC: os << "NUMERIC"; break;
		}
		os << ", ";
		os << "(char)" << (int)part.padding << ", ";
		os << part.width << ", ";
		os << part.base << ", ";
		os << part.signed_ << ", ";
		os << "fmt_part::";
		switch (part.sign) {
			case FmtPart::MINUS:       os << "MINUS";       break;
			case FmtPart::PLUS_MINUS:  os << "PLUS_MINUS";  break;
			case FmtPart::SPACE_MINUS: os << "SPACE_MINUS"; break;
		}
		os << ", ";
		os << part.hex_upper << ", ";
		os << part.show_base << ", ";
		os << part.group << ", ";
		os << part.realtime;
		os << " }.render(";
		emit_sig(part.sig);
		os << ", " << context << ");\n";
	}
	os << indent << "return buf;\n";
}

std::string Fmt::render() const
{
	std::string str;

	for (auto &part : parts) {
		switch (part.type) {
			case FmtPart::LITERAL:
				str += part.str;
				break;

			case FmtPart::UNICHAR: {
				RTLIL::Const value = part.sig.as_const();
				uint32_t codepoint = value.as_int();
				if (codepoint >= 0x10000)
					str += (char)(0xf0 |  (codepoint >> 18));
				else if (codepoint >= 0x800)
					str += (char)(0xe0 |  (codepoint >> 12));
				else if (codepoint >= 0x80)
					str += (char)(0xc0 |  (codepoint >>  6));
				else
					str += (char)codepoint;
				if (codepoint >= 0x10000)
					str += (char)(0x80 | ((codepoint >> 12) & 0x3f));
				if (codepoint >= 0x800)
					str += (char)(0x80 | ((codepoint >>  6) & 0x3f));
				if (codepoint >= 0x80)
					str += (char)(0x80 | ((codepoint >>  0) & 0x3f));
				break;
			}

			case FmtPart::INTEGER:
			case FmtPart::STRING:
			case FmtPart::VLOG_TIME: {
				std::string buf;
				std::string prefix;
				if (part.type == FmtPart::INTEGER) {
					RTLIL::Const value = part.sig.as_const();
					bool has_x = false, all_x = true, has_z = false, all_z = true;
					for (State bit : value) {
						if (bit == State::Sx)
							has_x = true;
						else
							all_x = false;
						if (bit == State::Sz)
							has_z = true;
						else
							all_z = false;
					}

					if (!has_z && !has_x && part.signed_ && value[value.size() - 1]) {
						prefix = "-";
						value = RTLIL::const_neg(value, {}, part.signed_, {}, value.size() + 1);
					} else {
						switch (part.sign) {
							case FmtPart::MINUS:       break;
							case FmtPart::PLUS_MINUS:  prefix = "+"; break;
							case FmtPart::SPACE_MINUS: prefix = " "; break;
						}
					}

					if (part.base != 10) {
						size_t minimum_size = 1;
						for (size_t index = 0; index < (size_t)value.size(); index++)
							if (value[index] != State::S0)
								minimum_size = index + 1;
						value = value.extract(0, minimum_size);
					}

					if (part.base == 2) {
						if (part.show_base)
							prefix += "0b";
						for (size_t index = 0; index < (size_t)value.size(); index++) {
							if (part.group && index > 0 && index % 4 == 0)
								buf += '_';
							RTLIL::State bit = value[index];
							if (bit == State::Sx)
								buf += 'x';
							else if (bit == State::Sz)
								buf += 'z';
							else if (bit == State::S1)
								buf += '1';
							else /* if (bit == State::S0) */
								buf += '0';
						}
					} else if (part.base == 8 || part.base == 16) {
						if (part.show_base)
							prefix += (part.base == 16) ? (part.hex_upper ? "0X" : "0x") : "0o";
						size_t step = (part.base == 16) ? 4 : 3;
						for (size_t index = 0; index < (size_t)value.size(); index += step) {
							if (part.group && index > 0 && index % (4 * step) == 0)
								buf += '_';
							RTLIL::Const subvalue = value.extract(index, min(step, value.size() - index));
							bool has_x = false, all_x = true, has_z = false, all_z = true;
							for (State bit : subvalue) {
								if (bit == State::Sx)
									has_x = true;
								else
									all_x = false;
								if (bit == State::Sz)
									has_z = true;
								else
									all_z = false;
							}
							if (all_x)
								buf += 'x';
							else if (all_z)
								buf += 'z';
							else if (has_x)
								buf += 'X';
							else if (has_z)
								buf += 'Z';
							else
								buf += (part.hex_upper ? "0123456789ABCDEF" : "0123456789abcdef")[subvalue.as_int()];
						}
					} else if (part.base == 10) {
						if (part.show_base)
							prefix += "0d";
						if (all_x)
							buf += 'x';
						else if (all_z)
							buf += 'z';
						else if (has_x)
							buf += 'X';
						else if (has_z)
							buf += 'Z';
						else {
							log_assert(value.is_fully_def());
							if (value.is_fully_zero())
								buf += '0';
							size_t index = 0;
							while (!value.is_fully_zero())	{
								if (part.group && index > 0 && index % 3 == 0)
									buf += '_';
								buf += '0' + RTLIL::const_mod(value, 10, false, false, 4).as_int();
								value = RTLIL::const_div(value, 10, false, false, value.size());
								index++;
							}
						}
					} else log_abort();
					if (part.justify == FmtPart::NUMERIC && part.group && part.padding == '0') {
						int group_size = part.base == 10 ? 3 : 4;
						while (prefix.size() + buf.size() < part.width) {
							if (buf.size() % (group_size + 1) == group_size)
								buf += '_';
							buf += '0';
						}
					}
					std::reverse(buf.begin(), buf.end());
				} else if (part.type == FmtPart::STRING) {
					buf = part.sig.as_const().decode_string();
				} else if (part.type == FmtPart::VLOG_TIME) {
					// We only render() during initial, so time is always zero.
					buf = "0";
				}

				log_assert(part.width == 0 || part.padding != '\0');
				if (prefix.size() + buf.size() < part.width) {
					size_t pad_width = part.width - prefix.size() - buf.size();
					switch (part.justify) {
						case FmtPart::LEFT:
							str += prefix;
							str += buf;
							str += std::string(pad_width, part.padding);
							break;
						case FmtPart::RIGHT:
							str += std::string(pad_width, part.padding);
							str += prefix;
							str += buf;
							break;
						case FmtPart::NUMERIC:
							str += prefix;
							str += std::string(pad_width, part.padding);
							str += buf;
							break;
					}
				} else {
					str += prefix;
					str += buf;
				}
				break;
			}
		}
	}

	return str;
}
