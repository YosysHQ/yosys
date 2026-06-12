/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
 *  ---
 *
 *  A handwritten recursive-descent parser for the RTLIL text representation.
 *
 */

#include "kernel/register.h"
#include "kernel/log.h"
#include "kernel/utils.h"
#include "kernel/twine.h"
#include <charconv>
#include <deque>
#include <optional>

YOSYS_NAMESPACE_BEGIN

struct RTLILFrontendWorker {
	// Forbid constants of more than 1 Gb.
	// This will help us not explode on malicious RTLIL.
	static constexpr int MAX_CONST_WIDTH = 1024 * 1024 * 1024;

	std::istream *f = nullptr;
	RTLIL::Design *design;
	bool flag_nooverwrite = false;
	bool flag_overwrite = false;
	bool flag_lib = false;
	bool flag_legalize = false;

	int line_num;
	std::string line_buf;
	// Substring of line_buf. Always newline-terminated, thus never empty.
	std::string_view line;

	RTLIL::Module *current_module;
	dict<RTLIL::IdString, RTLIL::Const> attrbuf;
	std::vector<std::vector<RTLIL::SwitchRule*>*> switch_stack;
	std::vector<RTLIL::CaseRule*> case_stack;

	// Remap from file-local twine ids (as they appear in the `twines` block
	// and on cell/wire src attrs) to ids in design->twines. Filled by
	// parse_twines; consumed by parse_attribute. Parser-side ids retained
	// during parse_twines are tracked here so they can be released at
	// end-of-parse — only the cell/wire references should survive.
	dict<size_t, TwineRef> twine_remap;
	std::vector<TwineRef> twine_parser_holds;

	template <typename... Args>
	[[noreturn]]
	void error(FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
	{
		log_error("Parser error in line %d: %s\n", line_num, fmt.format(args...));
	}

	template <typename... Args>
	void warning(FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
	{
		log_warning("In line %d: %s\n", line_num, fmt.format(args...));
	}

	// May return an empty line if the stream is not good().
	void advance_to_next_nonempty_line()
	{
		if (!f->good()) {
			line = "\n";
			return;
		}
		while (true) {
			std::getline(*f, line_buf);
			line_num++;
			if (line_buf.empty() || line_buf[line_buf.size() - 1] != '\n')
				line_buf += '\n';
			line = line_buf;
			consume_whitespace_and_comments();
			if (line[0] != '\n' || !f->good())
				break;
		}
	}

	void consume_whitespace_and_comments()
	{
		while (true) {
			switch (line[0]) {
			case ' ':
			case '\t':
				line = line.substr(1);
				break;
			case '#':
				line = "\n";
				return;
			default:
				return;
			}
		}
	}

	bool try_parse_keyword(std::string_view keyword)
	{
		int keyword_size = keyword.size();
		if (keyword != line.substr(0, keyword_size))
			return false;
		// This index is safe because `line` is always newline-terminated
		// and `keyword` never contains a newline.
		char ch = line[keyword_size];
		if (ch >= 'a' && ch <= 'z')
			return false;
		line = line.substr(keyword_size);
		consume_whitespace_and_comments();
		return true;
	}

	std::string error_token()
	{
		std::string result;
		for (char ch : line) {
			if (ch == '\n' || ch == ' ' || ch == '\t')
				break;
			result += ch;
		}
		return result;
	}

	void expect_keyword(std::string_view keyword)
	{
		if (!try_parse_keyword(keyword))
			error("Expected token `%s', got `%s'.", keyword, error_token());
	}

	bool try_parse_char(char ch)
	{
		if (line[0] != ch)
			return false;
		line = line.substr(1);
		consume_whitespace_and_comments();
		return true;
	}

	void expect_char(char ch)
	{
		if (!try_parse_char(ch))
			error("Expected `%c', got `%s'.", ch, error_token());
	}

	bool try_parse_eol()
	{
		if (line[0] != '\n')
			return false;
		advance_to_next_nonempty_line();
		return true;
	}

	void expect_eol()
	{
		if (!try_parse_eol())
			error("Expected EOL, got `%s'.", error_token());
	}

	std::optional<std::string> try_parse_id()
	{
		char ch = line[0];
		if (ch != '\\' && ch != '$')
			return std::nullopt;
		int idx = 1;
		while (true) {
			ch = line[idx];
			if (ch <= ' ' && (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r'))
				break;
			++idx;
		}
		std::string result(line.substr(0, idx));
		line = line.substr(idx);
		consume_whitespace_and_comments();
		return result;
	}

	std::string parse_id()
	{
		std::optional<std::string> id = try_parse_id();
		if (!id.has_value())
			error("Expected ID, got `%s'.", error_token());
		return std::move(*id);
	}

	long long parse_integer()
	{
		long long result = parse_integer_alone();
		consume_whitespace_and_comments();
		return result;
	}

	long long parse_integer_alone()
	{
		int idx = 0;
		if (line[idx] == '-')
			++idx;
		while (true) {
			char ch = line[idx];
			if (ch < '0' || ch > '9')
				break;
			++idx;
		}
		long long result;
		if (std::from_chars(line.data(), line.data() + idx, result, 10).ec != std::errc{})
			error("Invalid integer `%s'.", error_token());
		line = line.substr(idx);
		return result;
	}

	std::string parse_string()
	{
		if (line[0] != '\"')
			error("Expected string, got `%s'.", error_token());
		std::string str;
		int idx = 1;
		while (true) {
			int start_idx = idx;
			char ch;
			while (true) {
				ch = line[idx];
				if (ch == '"' || ch == '\n' || ch == '\\' || ch == 0)
					break;
				++idx;
			}
			str.append(line.data() + start_idx, line.data() + idx);
			++idx;
			if (ch == '"')
				break;
			if (ch == 0)
				error("Null byte in string literal: `%s'.", line);
			if (ch == '\n')
				error("Unterminated string literal: `%s'.", line);
			ch = line[idx++];
			if (ch == 'n') {
				ch = '\n';
			} else if (ch == 't') {
				ch = '\t';
			} else if (ch >= '0' && ch <= '7') {
				int v = ch - '0';
				char next_ch = line[idx + 1];
				if (next_ch >= '0' && next_ch <= '7') {
					++idx;
					v = v*8 + (next_ch - '0');
					next_ch = line[idx + 1];
					if (next_ch >= '0' && next_ch <= '7') {
						++idx;
						v = v*8 + (next_ch - '0');
					}
				}
				ch = v;
			}
			str += ch;
		}
		line = line.substr(idx);
		consume_whitespace_and_comments();
		return str;
	}

	RTLIL::Const parse_const()
	{
		if (line[0] == '"')
			return RTLIL::Const(parse_string());

		bool negative_value = line[0] == '-';
		long long width = parse_integer_alone();
		// Can't test value<0 here because we need to stop parsing after '-0'
		if (negative_value || line[0] != '\'') {
			if (width < INT_MIN || width > INT_MAX)
				error("Integer %lld out of range before `%s'.", width, error_token());
			consume_whitespace_and_comments();
			return RTLIL::Const(width);
		}

		int idx = 1;
		bool is_signed = line[1] == 's';
		if (is_signed)
			++idx;

		std::vector<RTLIL::State> bits;
		if (width > MAX_CONST_WIDTH)
			error("Constant width %lld out of range before `%s`.", width, error_token());
		bits.reserve(width);
		int start_idx = idx;
		while (true) {
			RTLIL::State bit;
			switch (line[idx]) {
			case '0': bit = RTLIL::S0; break;
			case '1': bit = RTLIL::S1; break;
			case 'x': bit = RTLIL::Sx; break;
			case 'z': bit = RTLIL::Sz; break;
			case 'm': bit = RTLIL::Sm; break;
			case '-': bit = RTLIL::Sa; break;
			default: goto done;
			}
			bits.push_back(bit);
			++idx;
		}
	done:
		if (start_idx < idx)
			std::reverse(bits.begin(), bits.end());

		if (GetSize(bits) > width)
			bits.resize(width);
		else if (GetSize(bits) < width) {
			RTLIL::State extbit = RTLIL::Sx;
			if (!bits.empty()) {
				extbit = bits.back();
				if (extbit == RTLIL::S1)
					extbit = RTLIL::S0;
			}
			bits.resize(width, extbit);
		}

		RTLIL::Const val(std::move(bits));
		if (is_signed)
			val.flags |= RTLIL::CONST_FLAG_SIGNED;
		line = line.substr(idx);
		consume_whitespace_and_comments();
		return val;
	}

	RTLIL::Wire *legalize_wire(RTLIL::IdString id)
	{
		int wires_size = current_module->wires_size();
		if (wires_size == 0)
			error("No wires found for legalization");
		int hash = hash_ops<RTLIL::IdString>::hash(id).yield();
		RTLIL::Wire *wire = current_module->wire_at(abs(hash % wires_size));
		log("Legalizing wire `%s' to `%s'.\n", log_id(id), design->twines.unescaped_str(wire->name.ref()));
		return wire;
	}

	RTLIL::SigSpec parse_sigspec()
	{
		RTLIL::SigSpec sig;

		if (try_parse_char('{')) {
			std::vector<SigSpec> parts;
			while (!try_parse_char('}'))
				parts.push_back(parse_sigspec());
			for (auto it = parts.rbegin(); it != parts.rend(); ++it)
				sig.append(std::move(*it));
		} else {
			// We could add a special path for parsing IdStrings that must already exist,
			// as here.
			// We don't need to addref/release in this case.
			std::optional<RTLIL::IdString> id = try_parse_id();
			if (id.has_value()) {
				RTLIL::Wire *wire = current_module->wire(design->twines.lookup(id->str()));
				if (wire == nullptr) {
					if (flag_legalize)
						wire = legalize_wire(*id);
					else {
						// for (auto wire : current_module->wires())
						// 	design->twines.dump(wire->meta_->name);
						error("Wire `%s' not found.", *id);
					}
				}
				sig = RTLIL::SigSpec(wire);
			} else {
				sig = RTLIL::SigSpec(parse_const());
			}
		}

		while (try_parse_char('[')) {
			int left = parse_integer();
			if (left >= sig.size() || left < 0) {
				if (flag_legalize) {
					int legalized;
					if (sig.size() == 0)
						legalized = 0;
					else
						legalized = std::max(0, std::min(left, sig.size() - 1));
					log("Legalizing bit index %d to %d.\n", left, legalized);
					left = legalized;
				} else {
					error("bit index %d out of range", left);
				}
			}
			if (try_parse_char(':')) {
				int right = parse_integer();
				if (right < 0) {
					if (flag_legalize) {
						log("Legalizing bit index %d to %d.\n", right, 0);
						right = 0;
					} else
						error("bit index %d out of range", right);
				}
				if (left < right) {
					if (flag_legalize) {
						log("Legalizing bit index %d to %d.\n", left, right);
						left = right;
					} else
						error("invalid slice [%d:%d]", left, right);
				}
				if (flag_legalize && left >= sig.size())
					log("Legalizing slice %d:%d by igoring it\n", left, right);
				else
					sig = sig.extract(right, left - right + 1);
			} else {
				if (flag_legalize && left >= sig.size())
					log("Legalizing slice %d by igoring it\n", left);
				else
					sig = sig.extract(left);
			}
			expect_char(']');
		}

		return sig;
	}

	void parse_module()
	{
		TwineRef module_name = design->twines.add(parse_id());
		expect_eol();

		bool delete_current_module = false;
		if (design->has(module_name)) {
			RTLIL::Module *existing_mod = design->module(module_name);
			if (!flag_overwrite && (flag_lib || (attrbuf.count(ID::blackbox) && attrbuf.at(ID::blackbox).as_bool()))) {
				log("Ignoring blackbox re-definition of module %s.\n", module_name);
				delete_current_module = true;
			} else if (!flag_nooverwrite && !flag_overwrite && !existing_mod->get_bool_attribute(ID::blackbox)) {
				error("RTLIL error: redefinition of module %s.", module_name);
			} else if (flag_nooverwrite) {
				log("Ignoring re-definition of module %s.\n", module_name);
				delete_current_module = true;
			} else {
				log("Replacing existing%s module %s.\n", existing_mod->get_bool_attribute(ID::blackbox) ? " blackbox" : "", module_name);
				design->remove(existing_mod);
			}
		}

		current_module = new RTLIL::Module;
		current_module->design = design;
		current_module->meta_->name = module_name;
		if (delete_current_module) {
			// Module is about to be discarded — drop its src attribute
			// rather than push it into a pool we'll never reach.
			attrbuf.erase(ID::src);
			current_module->attributes = std::move(attrbuf);
		} else {
			design->add(current_module);
			current_module->absorb_attrs(std::move(attrbuf));
		}

		while (true)
		{
			if (try_parse_keyword("attribute")) {
				parse_attribute();
				continue;
			}
			if (try_parse_keyword("parameter")) {
				parse_parameter();
				continue;
			}
			if (try_parse_keyword("connect")) {
				parse_connect();
				continue;
			}
			if (try_parse_keyword("wire")) {
				parse_wire();
				continue;
			}
			if (try_parse_keyword("cell")) {
				parse_cell();
				continue;
			}
			if (try_parse_keyword("memory")) {
				parse_memory();
				continue;
			}
			if (try_parse_keyword("process")) {
				parse_process();
				continue;
			}
			if (try_parse_keyword("end")) {
				expect_eol();
				break;
			}
			error("Unexpected token in module body: %s", error_token());
		}

		if (attrbuf.size() != 0)
			error("dangling attribute");
		current_module->fixup_ports();
		if (delete_current_module)
			delete current_module;
		else if (flag_lib)
			current_module->makeblackbox();
		current_module = nullptr;
	}

	void parse_attribute()
	{
		RTLIL::IdString id = parse_id();
		RTLIL::Const c = parse_const();
		// The '|' separator inside a src attribute is a Yosys-internal
		// merge convention emitted only by the legacy strpool path or by
		// a `dump -resolve-src`; no external tool should be producing it.
		// Warn so the producer learns to emit one path:line.col per
		// attribute. We don't try to repair the value — the user's input
		// is wrong and silently interning it would hide that.
		if (id == RTLIL::ID::src && (c.flags & RTLIL::CONST_FLAG_STRING)) {
			std::string raw = c.decode_string();
			if (raw.find('|') != std::string::npos) {
				log_warning("line %d: src attribute %s contains '|' separators. "
						"That convention is Yosys-internal; the producing tool "
						"should emit a single path:line.col per attribute and "
						"let Yosys merge through the twine pool.\n",
						line_num, raw.c_str());
			}
		}
		attrbuf.insert({std::move(id), std::move(c)});
		expect_eol();
	}

	// Parses a `twines` ... `end` block. Builds twine_remap so subsequent
	// cell/wire src "@N" references (which use file-local ids) translate
	// to ids in design->twines. The destination pool may already be
	// non-empty (multi-file load) — interned/concated nodes are dedup'd
	// against the existing pool by the pool itself.
	void parse_twines()
	{
		dict<size_t, Twine> file_twines;
		expect_eol();
		while (true) {
			if (try_parse_keyword("end"))
				break;
			if (try_parse_keyword("leaf")) {
				size_t file_id = parse_integer();
				std::string text = parse_string();
				expect_eol();
				file_twines[file_id] = Twine{text};
				continue;
			}
			if (try_parse_keyword("suffix")) {
				size_t file_id = parse_integer();
				size_t file_parent = parse_integer();
				std::string tail = parse_string();
				expect_eol();
				if (twine_remap.count(file_parent) == 0)
					error("Unknown parent twine @%zu for suffix at line %d", file_parent, line_num);
				file_twines[file_id] = Twine{Twine::Suffix{twine_remap[file_parent], tail}};
				continue;
			}
			if (try_parse_keyword("concat")) {
				size_t file_id = parse_integer();
				std::vector<TwineRef> children;
				while (!try_parse_eol()) {
					size_t child_id = parse_integer();
					if (twine_remap.count(child_id) == 0)
						error("Unknown child twine @%zu for concat at line %d", child_id, line_num);
					children.push_back(twine_remap[child_id]);
				}
				file_twines[file_id] = Twine{children};
				continue;
			}
			error("Expected `leaf`, `suffix` or `concat` inside twines block, got `%s'.",
					error_token());
		}
		expect_eol();
		for (auto &p : file_twines) {
			twine_remap[p.first] = design->twines.add(std::move(p.second));
		}
	}

	// Release the per-file parser refs gathered during parse_twines. Call
	// once the entire file has been parsed and every cell/wire that ever
	// referred to a file_id has already adopted the corresponding local_id.
	void release_twine_parser_holds()
	{
		twine_parser_holds.clear();
		twine_remap.clear();
	}

	void parse_parameter()
	{
		RTLIL::IdString id = parse_id();
		current_module->avail_parameters(id);
		if (try_parse_eol())
			return;
		RTLIL::Const c = parse_const();
		current_module->parameter_default_values.insert({std::move(id), std::move(c)});
		expect_eol();
	}

	void parse_wire()
	{
		RTLIL::Wire *wire;
		int width = 1;
		int start_offset = 0;
		int port_id = 0;
		bool port_input = false;
		bool port_output = false;
		bool upto = false;
		bool is_signed = false;

		while (true)
		{
			std::optional<RTLIL::IdString> id = try_parse_id();
			if (id.has_value()) {
				TwineRef wire_name = design->twines.lookup(id->str());
				if (wire_name == Twine::Null)
					wire_name = design->twines.add(Twine{id->str()});
				if (current_module->wire(wire_name) != nullptr) {
				  if (flag_legalize) {
						log("Legalizing redefinition of wire %s.\n", *id);
						pool<RTLIL::Wire*> wires = {current_module->wire(wire_name)};
						current_module->remove(wires);
					} else
						error("RTLIL error: redefinition of wire %s.", *id);
				}
				wire = current_module->addWire(Twine{id->str()});
				break;
			}
			if (try_parse_keyword("width"))
				width = parse_integer();
			else if (try_parse_keyword("upto"))
				upto = true;
			else if (try_parse_keyword("signed"))
				is_signed = true;
			else if (try_parse_keyword("offset"))
				start_offset = parse_integer();
			else if (try_parse_keyword("input")) {
				port_id = parse_integer();
				port_input = true;
			} else if (try_parse_keyword("output")) {
				port_id = parse_integer();
				port_output = true;
			} else if (try_parse_keyword("inout")) {
				port_id = parse_integer();
				port_input = true;
				port_output = true;
			} else if (try_parse_eol())
				error("Missing wire ID");
			else
				error("Unexpected wire option: %s", error_token());
		}

		wire->absorb_attrs(std::move(attrbuf));
		wire->width = width;
		wire->upto = upto;
		wire->start_offset = start_offset;
		wire->is_signed = is_signed;
		wire->port_id = port_id;
		wire->port_input = port_input;
		wire->port_output = port_output;
		expect_eol();
	}

	void parse_memory()
	{
		RTLIL::Memory *memory = new RTLIL::Memory;
		memory->module = current_module;
		memory->absorb_attrs(std::move(attrbuf));

		int width = 1;
		int start_offset = 0;
		int size = 0;
		TwineRef mem_name = Twine::Null;
		while (true)
		{
			std::optional<RTLIL::IdString> id = try_parse_id();
			if (id.has_value()) {
				mem_name = design->twines.lookup(id->str());
				if (mem_name == Twine::Null)
					mem_name = design->twines.add(Twine{id->str()});
				if (current_module->memories.count(mem_name) != 0) {
					if (flag_legalize) {
						log("Legalizing redefinition of memory %s.\n", *id);
						current_module->remove(current_module->memories.at(mem_name));
					} else
						error("RTLIL error: redefinition of memory %s.", *id);
				}
				memory->meta_->name = mem_name;
				break;
			}
			if (try_parse_keyword("width"))
				width = parse_integer();
			else if (try_parse_keyword("size"))
				size = parse_integer();
			else if (try_parse_keyword("offset"))
				start_offset = parse_integer();
			else if (try_parse_eol())
				error("Missing memory ID");
			else
				error("Unexpected memory option: %s", error_token());
		}
		memory->width = width;
		memory->start_offset = start_offset;
		memory->size = size;
		current_module->memories.insert({mem_name, memory});
		expect_eol();
	}

	void legalize_width_parameter(RTLIL::Cell *cell, TwineRef port_name)
	{
		std::string width_param_name = design->twines.str(port_name) + "_WIDTH";
		if (cell->parameters.count(RTLIL::IdString(width_param_name)) == 0)
			return;
		RTLIL::Const &param = cell->parameters.at(RTLIL::IdString(width_param_name));
		if (param.as_int() != 0)
			return;
		cell->parameters[RTLIL::IdString(width_param_name)] = RTLIL::Const(cell->getPort(port_name).size());
	}

	void parse_cell()
	{
		RTLIL::IdString cell_type = parse_id();
		std::string cell_name_str = parse_id();
		expect_eol();

		TwineRef cell_name_ref = design->twines.lookup(cell_name_str);
		if (cell_name_ref == Twine::Null)
			cell_name_ref = design->twines.add(Twine{cell_name_str});

		if (current_module->cell(cell_name_ref) != nullptr) {
			if (flag_legalize) {
				std::string new_name_str;
				int suffix = 1;
				do {
					new_name_str = cell_name_str + "_" + std::to_string(suffix);
					TwineRef test_ref = design->twines.lookup(new_name_str);
					if (test_ref == Twine::Null)
						test_ref = design->twines.add(Twine{new_name_str});
					++suffix;
					if (current_module->cell(test_ref) == nullptr)
						break;
				} while (true);
				log("Legalizing redefinition of cell %s by renaming to %s.\n", cell_name_str, new_name_str);
				cell_name_str = new_name_str;
				cell_name_ref = design->twines.lookup(cell_name_str);
				if (cell_name_ref == Twine::Null)
					cell_name_ref = design->twines.add(Twine{cell_name_str});
			} else
				error("RTLIL error: redefinition of cell %s.", cell_name_str);
		}
		RTLIL::Cell *cell = current_module->addCell(cell_name_ref, design->twines.add(Twine{cell_type.str()}));
		cell->absorb_attrs(std::move(attrbuf));

		while (true)
		{
			if (try_parse_keyword("parameter")) {
				bool is_signed = false;
				bool is_real = false;
				bool is_unsized = false;
				if (try_parse_keyword("signed")) {
					is_signed = true;
				} else if (try_parse_keyword("real")) {
					is_real = true;
				} else if (try_parse_keyword("unsized")) {
					is_unsized = true;
				}
				RTLIL::IdString param_name = parse_id();
				RTLIL::Const val = parse_const();
				if (is_signed)
					val.flags |= RTLIL::CONST_FLAG_SIGNED;
				if (is_real)
					val.flags |= RTLIL::CONST_FLAG_REAL;
				if (is_unsized)
					val.flags |= RTLIL::CONST_FLAG_UNSIZED;
				cell->parameters.insert({std::move(param_name), std::move(val)});
				expect_eol();
			} else if (try_parse_keyword("connect")) {
				std::string port_name_str = parse_id();
				TwineRef port_name = design->twines.lookup(port_name_str);
				if (port_name == Twine::Null)
					port_name = design->twines.add(Twine{port_name_str});
				if (cell->hasPort(port_name)) {
					if (flag_legalize)
						log("Legalizing redefinition of cell port %s.", port_name_str);
					else
						error("RTLIL error: redefinition of cell port %s.", port_name_str);
				}
				cell->setPort(port_name, parse_sigspec());
				if (flag_legalize)
					legalize_width_parameter(cell, port_name);
				expect_eol();
			} else if (try_parse_keyword("end")) {
				expect_eol();
				break;
			} else {
				error("Unexpected token in cell body: %s", error_token());
			}
		}
	}

	void parse_connect()
	{
		if (attrbuf.size() != 0)
			error("dangling attribute");
		RTLIL::SigSpec s1 = parse_sigspec();
		RTLIL::SigSpec s2 = parse_sigspec();
		if (flag_legalize) {
			int min_size = std::min(s1.size(), s2.size());
			s1 = s1.extract(0, min_size);
			s2 = s2.extract(0, min_size);
		}
		current_module->connect(std::move(s1), std::move(s2));
		expect_eol();
	}

	void parse_case_body(RTLIL::CaseRule *current_case)
	{
		while (true)
		{
			if (try_parse_keyword("attribute"))
				parse_attribute();
			else if (try_parse_keyword("switch"))
				parse_switch();
			else if (try_parse_keyword("assign")) {
				if (attrbuf.size() != 0)
					error("dangling attribute");
				// See https://github.com/YosysHQ/yosys/pull/4765 for discussion on this
				// warning
				if (!switch_stack.back()->empty())
					warning("case rule assign statements after switch statements may cause unexpected behaviour. "
						"The assign statement is reordered to come before all switch statements.");
				RTLIL::SigSpec s1 = parse_sigspec();
				RTLIL::SigSpec s2 = parse_sigspec();
				current_case->actions.push_back(RTLIL::SigSig(std::move(s1), std::move(s2)));
				expect_eol();
			} else
				return;
		}
	}

	void parse_switch()
	{
		RTLIL::SwitchRule *rule = new RTLIL::SwitchRule;
		rule->module = current_module;
		rule->signal = parse_sigspec();
		rule->absorb_attrs(std::move(attrbuf));
		switch_stack.back()->push_back(rule);
		expect_eol();

		while (true) {
			if (try_parse_keyword("attribute")) {
				parse_attribute();
				continue;
			}

			if (try_parse_keyword("end")) {
				expect_eol();
				break;
			}

			expect_keyword("case");
			RTLIL::CaseRule *case_rule = new RTLIL::CaseRule;
			case_rule->module = current_module;
			case_rule->absorb_attrs(std::move(attrbuf));
			rule->cases.push_back(case_rule);
			switch_stack.push_back(&case_rule->switches);
			case_stack.push_back(case_rule);

			if (!try_parse_eol()) {
				while (true) {
					case_rule->compare.push_back(parse_sigspec());
					if (try_parse_eol())
						break;
					expect_char(',');
				}
			}

			parse_case_body(case_rule);

			switch_stack.pop_back();
			case_stack.pop_back();
		}
	}

	void parse_process()
	{
		std::string proc_name_str = parse_id();
		expect_eol();

		TwineRef proc_name = design->twines.lookup(proc_name_str);
		if (proc_name == Twine::Null)
			proc_name = design->twines.add(Twine{proc_name_str});

		if (current_module->processes.count(proc_name) != 0) {
			if (flag_legalize) {
				log("Legalizing redefinition of process %s.\n", proc_name_str);
				current_module->remove(current_module->processes.at(proc_name));
			} else
				error("RTLIL error: redefinition of process %s.", proc_name_str);
		}
		RTLIL::Process *proc = current_module->addProcess(Twine{proc_name_str});
		proc->absorb_attrs(std::move(attrbuf));

		switch_stack.clear();
		switch_stack.push_back(&proc->root_case.switches);
		case_stack.clear();
		case_stack.push_back(&proc->root_case);

		parse_case_body(&proc->root_case);

		while (try_parse_keyword("sync"))
		{
			RTLIL::SyncRule *rule = new RTLIL::SyncRule;

			if (try_parse_keyword("low")) rule->type = RTLIL::ST0;
			else if (try_parse_keyword("high")) rule->type = RTLIL::ST1;
			else if (try_parse_keyword("posedge")) rule->type = RTLIL::STp;
			else if (try_parse_keyword("negedge")) rule->type = RTLIL::STn;
			else if (try_parse_keyword("edge")) rule->type = RTLIL::STe;
			else if (try_parse_keyword("always")) rule->type = RTLIL::STa;
			else if (try_parse_keyword("global")) rule->type = RTLIL::STg;
			else if (try_parse_keyword("init")) rule->type = RTLIL::STi;
			else error("Unexpected sync type: %s", error_token());

			if (rule->type != RTLIL::STa && rule->type != RTLIL::STg && rule->type != RTLIL::STi)
				rule->signal = parse_sigspec();
			proc->syncs.push_back(rule);
			expect_eol();

			bool attributes_in_update_list = false;
			while (true)
			{
				if (try_parse_keyword("update")) {
					RTLIL::SigSpec s1 = parse_sigspec();
					RTLIL::SigSpec s2 = parse_sigspec();
					rule->actions.push_back(RTLIL::SigSig(std::move(s1), std::move(s2)));
					expect_eol();
					continue;
				}

				if (try_parse_keyword("attribute")) {
					attributes_in_update_list = true;
					parse_attribute();
					continue;
				}

				if (!try_parse_keyword("memwr"))
					break;

				RTLIL::MemWriteAction act;
				act.module = current_module;
				design->absorb_attrs(&act, std::move(attrbuf));
				act.memid = parse_id();
				act.address = parse_sigspec();
				act.data = parse_sigspec();
				act.enable = parse_sigspec();
				act.priority_mask = parse_const();
				rule->mem_write_actions.push_back(act);
				// meta_idx_ is a weak ref — drop ours so the pushed copy
				// in the vector is the sole holder. Process::~Process
				// walks the tree to actually release.
				act.meta_ = nullptr;
				expect_eol();
			}
			// The old parser allowed dangling attributes before a "sync" to carry through
			// the "sync", so we will too, for now.
			if (attributes_in_update_list && attrbuf.size() > 0)
				error("dangling attribute");
		}

		expect_keyword("end");
		expect_eol();
	}

	RTLILFrontendWorker(RTLIL::Design *design) : design(design) {}

	void parse(std::istream *f)
	{
		this->f = f;
		line_num = 0;
		advance_to_next_nonempty_line();
		while (f->good())
		{
			if (try_parse_keyword("attribute")) {
				parse_attribute();
				continue;
			}
			if (try_parse_keyword("module")) {
				parse_module();
				continue;
			}
			if (try_parse_keyword("autoidx")) {
				autoidx = std::max<int>(autoidx, parse_integer());
				expect_eol();
				continue;
			}
			if (try_parse_keyword("twines")) {
				parse_twines();
				continue;
			}
			error("Unexpected token: %s", error_token());
		}
		if (attrbuf.size() != 0)
			error("dangling attribute");
		release_twine_parser_holds();
	}
};

struct RTLILFrontend : public Frontend {
	RTLILFrontend() : Frontend("rtlil", "read modules from RTLIL file") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    read_rtlil [filename]\n");
		log("\n");
		log("Load modules from an RTLIL file to the current design. (RTLIL is a text\n");
		log("representation of a design in yosys's internal format.)\n");
		log("\n");
		log("    -nooverwrite\n");
		log("        ignore re-definitions of modules. (the default behavior is to\n");
		log("        create an error message if the existing module is not a blackbox\n");
		log("        module, and overwrite the existing module if it is a blackbox module.)\n");
		log("\n");
		log("    -overwrite\n");
		log("        overwrite existing modules with the same name\n");
		log("\n");
		log("    -lib\n");
		log("        only create empty blackbox modules\n");
		log("\n");
		log("    -legalize\n");
		log("        prevent semantic errors (e.g. reference to unknown wire, redefinition of wire/cell)\n");
		log("        by deterministically rewriting the input into something valid. Useful when using\n");
		log("        fuzzing to generate random but valid RTLIL.\n");
		log("\n");
	}
	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		RTLILFrontendWorker worker(design);

		log_header(design, "Executing RTLIL frontend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-nooverwrite") {
				worker.flag_nooverwrite = true;
				worker.flag_overwrite = false;
				continue;
			}
			if (arg == "-overwrite") {
				worker.flag_nooverwrite = false;
				worker.flag_overwrite = true;
				continue;
			}
			if (arg == "-lib") {
				worker.flag_lib = true;
				continue;
			}
			if (arg == "-legalize") {
				worker.flag_legalize = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		log("Input filename: %s\n", filename);

		worker.parse(f);
	}
} RTLILFrontend;

YOSYS_NAMESPACE_END
