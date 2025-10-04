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

	int line_num;
	std::string line_buf;
	// Substring of line_buf. Always newline-terminated, thus never empty.
	std::string_view line;

	RTLIL::Module *current_module;
	dict<RTLIL::IdString, RTLIL::Const> attrbuf;
	std::vector<std::vector<RTLIL::SwitchRule*>*> switch_stack;
	std::vector<RTLIL::CaseRule*> case_stack;

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

	std::optional<RTLIL::IdString> try_parse_id()
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
		IdString result(line.substr(0, idx));
		line = line.substr(idx);
		consume_whitespace_and_comments();
		return result;
	}

	RTLIL::IdString parse_id()
	{
		std::optional<RTLIL::IdString> id = try_parse_id();
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

	RTLIL::SigSpec parse_sigspec()
	{
		if (try_parse_char('{')) {
			std::vector<SigSpec> parts;
			while (!try_parse_char('}'))
				parts.push_back(parse_sigspec());
			RTLIL::SigSpec sig;
			for (auto it = parts.rbegin(); it != parts.rend(); ++it)
				sig.append(std::move(*it));
			return sig;
		}

		RTLIL::SigSpec sig;

		// We could add a special path for parsing IdStrings that must already exist,
		// as here.
		// We don't need to addref/release in this case.
		std::optional<RTLIL::IdString> id = try_parse_id();
		if (id.has_value()) {
			RTLIL::Wire *wire = current_module->wire(*id);
			if (wire == nullptr)
				error("Wire `%s' not found.", *id);
			sig = RTLIL::SigSpec(wire);
		} else {
			sig = RTLIL::SigSpec(parse_const());
		}

		while (try_parse_char('[')) {
			int left = parse_integer();
			if (left >= sig.size() || left < 0)
				error("bit index %d out of range", left);
			if (try_parse_char(':')) {
				int right = parse_integer();
				if (right < 0)
					error("bit index %d out of range", right);
				if (left < right)
					error("invalid slice [%d:%d]", left, right);
				sig = sig.extract(right, left-right+1);
			} else {
				sig = sig.extract(left);
			}
			expect_char(']');
		}

		return sig;
	}

	void parse_module()
	{
		RTLIL::IdString module_name = parse_id();
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
		current_module->name = std::move(module_name);
		current_module->attributes = std::move(attrbuf);
		if (!delete_current_module)
			design->add(current_module);

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
		attrbuf.insert({std::move(id), std::move(c)});
		expect_eol();
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
				if (current_module->wire(*id) != nullptr)
					error("RTLIL error: redefinition of wire %s.", *id);
				wire = current_module->addWire(std::move(*id));
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

		wire->attributes = std::move(attrbuf);
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
		memory->attributes = std::move(attrbuf);

		int width = 1;
		int start_offset = 0;
		int size = 0;
		while (true)
		{
			std::optional<RTLIL::IdString> id = try_parse_id();
			if (id.has_value()) {
				if (current_module->memories.count(*id) != 0)
					error("RTLIL error: redefinition of memory %s.", *id);
				memory->name = std::move(*id);
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
		current_module->memories.insert({memory->name, memory});
		expect_eol();
	}

	void parse_cell()
	{
		RTLIL::IdString cell_type = parse_id();
		RTLIL::IdString cell_name = parse_id();
		expect_eol();

		if (current_module->cell(cell_name) != nullptr)
			error("RTLIL error: redefinition of cell %s.", cell_name);
		RTLIL::Cell *cell = current_module->addCell(cell_name, cell_type);
		cell->attributes = std::move(attrbuf);

		while (true)
		{
			if (try_parse_keyword("parameter")) {
				bool is_signed = false;
				bool is_real = false;
				if (try_parse_keyword("signed")) {
					is_signed = true;
				} else if (try_parse_keyword("real")) {
					is_real = true;
				}
				RTLIL::IdString param_name = parse_id();
				RTLIL::Const val = parse_const();
				if (is_signed)
					val.flags |= RTLIL::CONST_FLAG_SIGNED;
				if (is_real)
					val.flags |= RTLIL::CONST_FLAG_REAL;
				cell->parameters.insert({std::move(param_name), std::move(val)});
				expect_eol();
			} else if (try_parse_keyword("connect")) {
				RTLIL::IdString port_name = parse_id();
				if (cell->hasPort(port_name))
					error("RTLIL error: redefinition of cell port %s.", port_name);
				cell->setPort(std::move(port_name), parse_sigspec());
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
		rule->signal = parse_sigspec();
		rule->attributes = std::move(attrbuf);
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
			case_rule->attributes = std::move(attrbuf);
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
		RTLIL::IdString proc_name = parse_id();
		expect_eol();

		if (current_module->processes.count(proc_name) != 0)
			error("RTLIL error: redefinition of process %s.", proc_name);
		RTLIL::Process *proc = current_module->addProcess(std::move(proc_name));
		proc->attributes = std::move(attrbuf);

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
				act.attributes = std::move(attrbuf);
				act.memid = parse_id();
				act.address = parse_sigspec();
				act.data = parse_sigspec();
				act.enable = parse_sigspec();
				act.priority_mask = parse_const();
				rule->mem_write_actions.push_back(std::move(act));
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
			error("Unexpected token: %s", error_token());
		}
		if (attrbuf.size() != 0)
			error("dangling attribute");
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
			break;
		}
		extra_args(f, filename, args, argidx);

		log("Input filename: %s\n", filename);

		worker.parse(f);
	}
} RTLILFrontend;

YOSYS_NAMESPACE_END
