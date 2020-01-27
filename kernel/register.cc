/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#include "kernel/yosys.h"
#include "kernel/satgen.h"

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>

#ifdef YOSYS_ENABLE_ZLIB
#include <zlib.h>

PRIVATE_NAMESPACE_BEGIN
#define GZ_BUFFER_SIZE 8192
void decompress_gzip(const std::string &filename, std::stringstream &out)
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

/*
An output stream that uses a stringbuf to buffer data internally,
using zlib to write gzip-compressed data every time the stream is flushed.
*/
class gzip_ostream : public std::ostream  {
public:
	gzip_ostream() : std::ostream(nullptr)
	{
		rdbuf(&outbuf);
	}
	bool open(const std::string &filename)
	{
		return outbuf.open(filename);
	}
private:
	class gzip_streambuf : public std::stringbuf {
	public:
		gzip_streambuf() { };
		bool open(const std::string &filename)
		{
			gzf = gzopen(filename.c_str(), "wb");
			return gzf != nullptr;
		}
		virtual int sync() override
		{
			gzwrite(gzf, reinterpret_cast<const void *>(str().c_str()), unsigned(str().size()));
			str("");
			return 0;
		}
		virtual ~gzip_streambuf()
		{
			sync();
			gzclose(gzf);
		}
	private:
		gzFile gzf = nullptr;
	} outbuf;
};
PRIVATE_NAMESPACE_END

#endif

YOSYS_NAMESPACE_BEGIN

#define MAX_REG_COUNT 1000

bool echo_mode = false;
Pass *first_queued_pass;
Pass *current_pass;

std::map<std::string, Frontend*> frontend_register;
std::map<std::string, Pass*> pass_register;
std::map<std::string, Backend*> backend_register;

std::vector<std::string> Frontend::next_args;

Pass::Pass(std::string name, std::string short_help) : pass_name(name), short_help(short_help)
{
	next_queued_pass = first_queued_pass;
	first_queued_pass = this;
	call_counter = 0;
	runtime_ns = 0;
}

void Pass::run_register()
{
	log_assert(pass_register.count(pass_name) == 0);
	pass_register[pass_name] = this;
}

void Pass::init_register()
{
	vector<Pass*> added_passes;
	while (first_queued_pass) {
		added_passes.push_back(first_queued_pass);
		first_queued_pass->run_register();
		first_queued_pass = first_queued_pass->next_queued_pass;
	}
	for (auto added_pass : added_passes)
		added_pass->on_register();
}

void Pass::done_register()
{
	for (auto &it : pass_register)
		it.second->on_shutdown();

	frontend_register.clear();
	pass_register.clear();
	backend_register.clear();
	log_assert(first_queued_pass == NULL);
}

void Pass::on_register()
{
}

void Pass::on_shutdown()
{
}

Pass::~Pass()
{
}

Pass::pre_post_exec_state_t Pass::pre_execute()
{
	pre_post_exec_state_t state;
	call_counter++;
	state.begin_ns = PerformanceTimer::query();
	state.parent_pass = current_pass;
	current_pass = this;
	clear_flags();
	return state;
}

void Pass::post_execute(Pass::pre_post_exec_state_t state)
{
	IdString::checkpoint();
	log_suppressed();

	int64_t time_ns = PerformanceTimer::query() - state.begin_ns;
	runtime_ns += time_ns;
	current_pass = state.parent_pass;
	if (current_pass)
		current_pass->runtime_ns -= time_ns;
}

void Pass::help()
{
	log("\n");
	log("No help message for command `%s'.\n", pass_name.c_str());
	log("\n");
}

void Pass::clear_flags()
{
}

void Pass::cmd_log_args(const std::vector<std::string> &args)
{
	if (args.size() <= 1)
		return;
	log("Full command line:");
	for (size_t i = 0; i < args.size(); i++)
		log(" %s", args[i].c_str());
	log("\n");
}

void Pass::cmd_error(const std::vector<std::string> &args, size_t argidx, std::string msg)
{
	std::string command_text;
	int error_pos = 0;

	for (size_t i = 0; i < args.size(); i++) {
		if (i < argidx)
			error_pos += args[i].size() + 1;
		command_text = command_text + (command_text.empty() ? "" : " ") + args[i];
	}

	log("\nSyntax error in command `%s':\n", command_text.c_str());
	help();

	log_cmd_error("Command syntax error: %s\n> %s\n> %*s^\n",
			msg.c_str(), command_text.c_str(), error_pos, "");
}

void Pass::extra_args(std::vector<std::string> args, size_t argidx, RTLIL::Design *design, bool select)
{
	for (; argidx < args.size(); argidx++)
	{
		std::string arg = args[argidx];

		if (arg.compare(0, 1, "-") == 0)
			cmd_error(args, argidx, "Unknown option or option in arguments.");

		if (!select)
			cmd_error(args, argidx, "Extra argument.");

		handle_extra_select_args(this, args, argidx, args.size(), design);
		break;
	}
	// cmd_log_args(args);
}

void Pass::call(RTLIL::Design *design, std::string command)
{
	std::vector<std::string> args;

	std::string cmd_buf = command;
	std::string tok = next_token(cmd_buf, " \t\r\n", true);

	if (tok.empty())
		return;

	if (tok[0] == '!') {
		cmd_buf = command.substr(command.find('!') + 1);
		while (!cmd_buf.empty() && (cmd_buf.back() == ' ' || cmd_buf.back() == '\t' ||
				cmd_buf.back() == '\r' || cmd_buf.back() == '\n'))
			cmd_buf.resize(cmd_buf.size()-1);
		log_header(design, "Shell command: %s\n", cmd_buf.c_str());
		int retCode = run_command(cmd_buf);
		if (retCode != 0)
			log_cmd_error("Shell command returned error code %d.\n", retCode);
		return;
	}

	while (!tok.empty()) {
		if (tok[0] == '#') {
			int stop;
			for (stop = 0; stop < GetSize(cmd_buf); stop++)
				if (cmd_buf[stop] == '\r' || cmd_buf[stop] == '\n')
					break;
			cmd_buf = cmd_buf.substr(stop);
		} else
		if (tok.back() == ';') {
			int num_semikolon = 0;
			while (!tok.empty() && tok.back() == ';')
				tok.resize(tok.size()-1), num_semikolon++;
			if (!tok.empty())
				args.push_back(tok);
			call(design, args);
			args.clear();
			if (num_semikolon == 2)
				call(design, "clean");
			if (num_semikolon == 3)
				call(design, "clean -purge");
		} else
			args.push_back(tok);
		bool found_nl = false;
		for (auto c : cmd_buf) {
			if (c == ' ' || c == '\t')
				continue;
			if (c == '\r' || c == '\n')
				found_nl = true;
			break;
		}
		if (found_nl) {
			call(design, args);
			args.clear();
		}
		tok = next_token(cmd_buf, " \t\r\n", true);
	}

	call(design, args);
}

void Pass::call(RTLIL::Design *design, std::vector<std::string> args)
{
	if (args.size() == 0 || args[0][0] == '#' || args[0][0] == ':')
		return;

	if (echo_mode) {
		log("%s", create_prompt(design, 0));
		for (size_t i = 0; i < args.size(); i++)
			log("%s%s", i ? " " : "", args[i].c_str());
		log("\n");
	}

	if (pass_register.count(args[0]) == 0)
		log_cmd_error("No such command: %s (type 'help' for a command overview)\n", args[0].c_str());

	if (pass_register[args[0]]->experimental_flag)
		log_experimental("%s", args[0].c_str());

	size_t orig_sel_stack_pos = design->selection_stack.size();
	auto state = pass_register[args[0]]->pre_execute();
	pass_register[args[0]]->execute(args, design);
	pass_register[args[0]]->post_execute(state);
	while (design->selection_stack.size() > orig_sel_stack_pos)
		design->selection_stack.pop_back();
}

void Pass::call_on_selection(RTLIL::Design *design, const RTLIL::Selection &selection, std::string command)
{
	std::string backup_selected_active_module = design->selected_active_module;
	design->selected_active_module.clear();
	design->selection_stack.push_back(selection);

	Pass::call(design, command);

	design->selection_stack.pop_back();
	design->selected_active_module = backup_selected_active_module;
}

void Pass::call_on_selection(RTLIL::Design *design, const RTLIL::Selection &selection, std::vector<std::string> args)
{
	std::string backup_selected_active_module = design->selected_active_module;
	design->selected_active_module.clear();
	design->selection_stack.push_back(selection);

	Pass::call(design, args);

	design->selection_stack.pop_back();
	design->selected_active_module = backup_selected_active_module;
}

void Pass::call_on_module(RTLIL::Design *design, RTLIL::Module *module, std::string command)
{
	std::string backup_selected_active_module = design->selected_active_module;
	design->selected_active_module = module->name.str();
	design->selection_stack.push_back(RTLIL::Selection(false));
	design->selection_stack.back().select(module);

	Pass::call(design, command);

	design->selection_stack.pop_back();
	design->selected_active_module = backup_selected_active_module;
}

void Pass::call_on_module(RTLIL::Design *design, RTLIL::Module *module, std::vector<std::string> args)
{
	std::string backup_selected_active_module = design->selected_active_module;
	design->selected_active_module = module->name.str();
	design->selection_stack.push_back(RTLIL::Selection(false));
	design->selection_stack.back().select(module);

	Pass::call(design, args);

	design->selection_stack.pop_back();
	design->selected_active_module = backup_selected_active_module;
}

bool ScriptPass::check_label(std::string label, std::string info)
{
	if (active_design == nullptr) {
		log("\n");
		if (info.empty())
			log("    %s:\n", label.c_str());
		else
			log("    %s:    %s\n", label.c_str(), info.c_str());
		return true;
	} else {
		if (!active_run_from.empty() && active_run_from == active_run_to) {
			block_active = (label == active_run_from);
		} else {
			if (label == active_run_from)
				block_active = true;
			if (label == active_run_to)
				block_active = false;
		}
		return block_active;
	}
}

void ScriptPass::run(std::string command, std::string info)
{
	if (active_design == nullptr) {
		if (info.empty())
			log("        %s\n", command.c_str());
		else
			log("        %s    %s\n", command.c_str(), info.c_str());
	} else {
		Pass::call(active_design, command);
		active_design->check();
	}
}

void ScriptPass::run_script(RTLIL::Design *design, std::string run_from, std::string run_to)
{
	help_mode = false;
	active_design = design;
	block_active = run_from.empty();
	active_run_from = run_from;
	active_run_to = run_to;
	script();
}

void ScriptPass::help_script()
{
	clear_flags();
	help_mode = true;
	active_design = nullptr;
	block_active = true;
	active_run_from.clear();
	active_run_to.clear();
	script();
}

Frontend::Frontend(std::string name, std::string short_help) :
		Pass(name.rfind("=", 0) == 0 ? name.substr(1) : "read_" + name, short_help),
		frontend_name(name.rfind("=", 0) == 0 ? name.substr(1) : name)
{
}

void Frontend::run_register()
{
	log_assert(pass_register.count(pass_name) == 0);
	pass_register[pass_name] = this;

	log_assert(frontend_register.count(frontend_name) == 0);
	frontend_register[frontend_name] = this;
}

Frontend::~Frontend()
{
}

void Frontend::execute(std::vector<std::string> args, RTLIL::Design *design)
{
	log_assert(next_args.empty());
	do {
		std::istream *f = NULL;
		next_args.clear();
		auto state = pre_execute();
		execute(f, std::string(), args, design);
		post_execute(state);
		args = next_args;
		delete f;
	} while (!args.empty());
}

FILE *Frontend::current_script_file = NULL;
std::string Frontend::last_here_document;

void Frontend::extra_args(std::istream *&f, std::string &filename, std::vector<std::string> args, size_t argidx, bool bin_input)
{
	bool called_with_fp = f != NULL;

	next_args.clear();

	if (argidx < args.size())
	{
		std::string arg = args[argidx];

		if (arg.compare(0, 1, "-") == 0)
			cmd_error(args, argidx, "Unknown option or option in arguments.");
		if (f != NULL)
			cmd_error(args, argidx, "Extra filename argument in direct file mode.");

		filename = arg;
		if (filename == "<<" && argidx+1 < args.size())
			filename += args[++argidx];
		if (filename.compare(0, 2, "<<") == 0) {
			if (Frontend::current_script_file == NULL)
				log_error("Unexpected here document '%s' outside of script!\n", filename.c_str());
			if (filename.size() <= 2)
				log_error("Missing EOT marker in here document!\n");
			std::string eot_marker = filename.substr(2);
			last_here_document.clear();
			while (1) {
				std::string buffer;
				char block[4096];
				while (1) {
					if (fgets(block, 4096, Frontend::current_script_file) == NULL)
						log_error("Unexpected end of file in here document '%s'!\n", filename.c_str());
					buffer += block;
					if (buffer.size() > 0 && (buffer[buffer.size() - 1] == '\n' || buffer[buffer.size() - 1] == '\r'))
						break;
				}
				size_t indent = buffer.find_first_not_of(" \t\r\n");
				if (indent != std::string::npos && buffer.compare(indent, eot_marker.size(), eot_marker) == 0)
					break;
				last_here_document += buffer;
			}
			f = new std::istringstream(last_here_document);
		} else {
			rewrite_filename(filename);
			vector<string> filenames = glob_filename(filename);
			filename = filenames.front();
			if (GetSize(filenames) > 1) {
				next_args.insert(next_args.end(), args.begin(), args.begin()+argidx);
				next_args.insert(next_args.end(), filenames.begin()+1, filenames.end());
			}
			std::ifstream *ff = new std::ifstream;
			ff->open(filename.c_str(), bin_input ? std::ifstream::binary : std::ifstream::in);
			yosys_input_files.insert(filename);
			if (ff->fail())
				delete ff;
			else
				f = ff;
			if (f != NULL) {
				// Check for gzip magic
				unsigned char magic[3];
				int n = 0;
				while (n < 3)
				{
					int c = ff->get();
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
					delete ff;
					std::stringstream *df = new std::stringstream();
					decompress_gzip(filename, *df);
					f = df;
	#else
					log_cmd_error("File `%s' is a gzip file, but Yosys is compiled without zlib.\n", filename.c_str());
	#endif
				} else {
					ff->clear();
					ff->seekg(0, std::ios::beg);
				}
			}
		}
		if (f == NULL)
			log_cmd_error("Can't open input file `%s' for reading: %s\n", filename.c_str(), strerror(errno));

		for (size_t i = argidx+1; i < args.size(); i++)
			if (args[i].compare(0, 1, "-") == 0)
				cmd_error(args, i, "Found option, expected arguments.");

		if (argidx+1 < args.size()) {
			if (next_args.empty())
				next_args.insert(next_args.end(), args.begin(), args.begin()+argidx);
			next_args.insert(next_args.end(), args.begin()+argidx+1, args.end());
			args.erase(args.begin()+argidx+1, args.end());
		}
	}

	if (f == NULL)
		cmd_error(args, argidx, "No filename given.");

	if (called_with_fp)
		args.push_back(filename);
	args[0] = pass_name;
	// cmd_log_args(args);
}

void Frontend::frontend_call(RTLIL::Design *design, std::istream *f, std::string filename, std::string command)
{
	std::vector<std::string> args;
	char *s = strdup(command.c_str());
	for (char *p = strtok(s, " \t\r\n"); p; p = strtok(NULL, " \t\r\n"))
		args.push_back(p);
	free(s);
	frontend_call(design, f, filename, args);
}

void Frontend::frontend_call(RTLIL::Design *design, std::istream *f, std::string filename, std::vector<std::string> args)
{
	if (args.size() == 0)
		return;
	if (frontend_register.count(args[0]) == 0)
		log_cmd_error("No such frontend: %s\n", args[0].c_str());

	if (f != NULL) {
		auto state = frontend_register[args[0]]->pre_execute();
		frontend_register[args[0]]->execute(f, filename, args, design);
		frontend_register[args[0]]->post_execute(state);
	} else if (filename == "-") {
		std::istream *f_cin = &std::cin;
		auto state = frontend_register[args[0]]->pre_execute();
		frontend_register[args[0]]->execute(f_cin, "<stdin>", args, design);
		frontend_register[args[0]]->post_execute(state);
	} else {
		if (!filename.empty())
			args.push_back(filename);
		frontend_register[args[0]]->execute(args, design);
	}
}

Backend::Backend(std::string name, std::string short_help) :
		Pass(name.rfind("=", 0) == 0 ? name.substr(1) : "write_" + name, short_help),
		backend_name(name.rfind("=", 0) == 0 ? name.substr(1) : name)
{
}

void Backend::run_register()
{
	log_assert(pass_register.count(pass_name) == 0);
	pass_register[pass_name] = this;

	log_assert(backend_register.count(backend_name) == 0);
	backend_register[backend_name] = this;
}

Backend::~Backend()
{
}

void Backend::execute(std::vector<std::string> args, RTLIL::Design *design)
{
	std::ostream *f = NULL;
	auto state = pre_execute();
	execute(f, std::string(), args, design);
	post_execute(state);
	if (f != &std::cout)
		delete f;
}

void Backend::extra_args(std::ostream *&f, std::string &filename, std::vector<std::string> args, size_t argidx, bool bin_output)
{
	bool called_with_fp = f != NULL;

	for (; argidx < args.size(); argidx++)
	{
		std::string arg = args[argidx];

		if (arg.compare(0, 1, "-") == 0 && arg != "-")
			cmd_error(args, argidx, "Unknown option or option in arguments.");
		if (f != NULL)
			cmd_error(args, argidx, "Extra filename argument in direct file mode.");

		if (arg == "-") {
			filename = "<stdout>";
			f = &std::cout;
			continue;
		}

		filename = arg;
		rewrite_filename(filename);
		if (filename.size() > 3 && filename.compare(filename.size()-3, std::string::npos, ".gz") == 0) {
#ifdef YOSYS_ENABLE_ZLIB
			gzip_ostream *gf = new gzip_ostream;
			if (!gf->open(filename)) {
				delete gf;
				log_cmd_error("Can't open output file `%s' for writing: %s\n", filename.c_str(), strerror(errno));
			}
			yosys_output_files.insert(filename);
			f = gf;
#else
			log_cmd_error("Yosys is compiled without zlib support, unable to write gzip output.\n");
#endif
		} else {
			std::ofstream *ff = new std::ofstream;
			ff->open(filename.c_str(), bin_output ? (std::ofstream::trunc | std::ofstream::binary) : std::ofstream::trunc);
			yosys_output_files.insert(filename);
			if (ff->fail()) {
				delete ff;
				log_cmd_error("Can't open output file `%s' for writing: %s\n", filename.c_str(), strerror(errno));
			}
			f = ff;
		}
	}

	if (called_with_fp)
		args.push_back(filename);
	args[0] = pass_name;
	// cmd_log_args(args);

	if (f == NULL) {
		filename = "<stdout>";
		f = &std::cout;
	}
}

void Backend::backend_call(RTLIL::Design *design, std::ostream *f, std::string filename, std::string command)
{
	std::vector<std::string> args;
	char *s = strdup(command.c_str());
	for (char *p = strtok(s, " \t\r\n"); p; p = strtok(NULL, " \t\r\n"))
		args.push_back(p);
	free(s);
	backend_call(design, f, filename, args);
}

void Backend::backend_call(RTLIL::Design *design, std::ostream *f, std::string filename, std::vector<std::string> args)
{
	if (args.size() == 0)
		return;
	if (backend_register.count(args[0]) == 0)
		log_cmd_error("No such backend: %s\n", args[0].c_str());

	size_t orig_sel_stack_pos = design->selection_stack.size();

	if (f != NULL) {
		auto state = backend_register[args[0]]->pre_execute();
		backend_register[args[0]]->execute(f, filename, args, design);
		backend_register[args[0]]->post_execute(state);
	} else if (filename == "-") {
		std::ostream *f_cout = &std::cout;
		auto state = backend_register[args[0]]->pre_execute();
		backend_register[args[0]]->execute(f_cout, "<stdout>", args, design);
		backend_register[args[0]]->post_execute(state);
	} else {
		if (!filename.empty())
			args.push_back(filename);
		backend_register[args[0]]->execute(args, design);
	}

	while (design->selection_stack.size() > orig_sel_stack_pos)
		design->selection_stack.pop_back();
}

static struct CellHelpMessages {
	dict<string, string> cell_help, cell_code;
	CellHelpMessages() {
#include "techlibs/common/simlib_help.inc"
#include "techlibs/common/simcells_help.inc"
		cell_help.sort();
		cell_code.sort();
	}
} cell_help_messages;

struct HelpPass : public Pass {
	HelpPass() : Pass("help", "display help messages") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    help  ................  list all commands\n");
		log("    help <command>  ......  print help message for given command\n");
		log("    help -all  ...........  print complete command reference\n");
		log("\n");
		log("    help -cells ..........  list all cell types\n");
		log("    help <celltype>  .....  print help message for given cell type\n");
		log("    help <celltype>+  ....  print verilog code for given cell type\n");
		log("\n");
	}
	void escape_tex(std::string &tex)
	{
		for (size_t pos = 0; (pos = tex.find('_', pos)) != std::string::npos; pos += 2)
			tex.replace(pos, 1, "\\_");
		for (size_t pos = 0; (pos = tex.find('$', pos)) != std::string::npos; pos += 2)
			tex.replace(pos, 1, "\\$");
	}
	void write_tex(FILE *f, std::string cmd, std::string title, std::string text)
	{
		size_t begin = text.find_first_not_of("\n"), end = text.find_last_not_of("\n");
		if (begin != std::string::npos && end != std::string::npos && begin < end)
			text = text.substr(begin, end-begin+1);
		std::string cmd_unescaped = cmd;
		escape_tex(cmd);
		escape_tex(title);
		fprintf(f, "\\section{%s -- %s}\n", cmd.c_str(), title.c_str());
		fprintf(f, "\\label{cmd:%s}\n", cmd_unescaped.c_str());
		fprintf(f, "\\begin{lstlisting}[numbers=left,frame=single]\n");
		fprintf(f, "%s\n\\end{lstlisting}\n\n", text.c_str());
	}
	void escape_html(std::string &html)
	{
		size_t pos = 0;
		while ((pos = html.find_first_of("<>&", pos)) != std::string::npos)
			switch (html[pos]) {
			case '<':
				html.replace(pos, 1, "&lt;");
				pos += 4;
				break;
			case '>':
				html.replace(pos, 1, "&gt;");
				pos += 4;
				break;
			case '&':
				html.replace(pos, 1, "&amp;");
				pos += 5;
				break;
			}
	}
	void write_html(FILE *idxf, std::string cmd, std::string title, std::string text)
	{
		FILE *f = fopen(stringf("cmd_%s.in", cmd.c_str()).c_str(), "wt");
		fprintf(idxf, "<li><a href=\"cmd_%s.html\"> ", cmd.c_str());

		escape_html(cmd);
		escape_html(title);
		escape_html(text);

		fprintf(idxf, "%s</a> <span>%s</span></a>\n", cmd.c_str(), title.c_str());

		fprintf(f, "@cmd_header %s@\n", cmd.c_str());
		fprintf(f, "<h1>%s - %s</h1>\n", cmd.c_str(), title.c_str());
		fprintf(f, "<pre>%s</pre>\n", text.c_str());
		fprintf(f, "@footer@\n");

		fclose(f);
	}
	void execute(std::vector<std::string> args, RTLIL::Design*) YS_OVERRIDE
	{
		if (args.size() == 1) {
			log("\n");
			for (auto &it : pass_register)
				log("    %-20s %s\n", it.first.c_str(), it.second->short_help.c_str());
			log("\n");
			log("Type 'help <command>' for more information on a command.\n");
			log("Type 'help -cells' for a list of all cell types.\n");
			log("\n");
			return;
		}

		if (args.size() == 2) {
			if (args[1] == "-all") {
				for (auto &it : pass_register) {
					log("\n\n");
					log("%s  --  %s\n", it.first.c_str(), it.second->short_help.c_str());
					for (size_t i = 0; i < it.first.size() + it.second->short_help.size() + 6; i++)
						log("=");
					log("\n");
					it.second->help();
					if (it.second->experimental_flag) {
						log("\n");
						log("WARNING: THE '%s' COMMAND IS EXPERIMENTAL.\n", it.first.c_str());
						log("\n");
					}
				}
			}
			else if (args[1] == "-cells") {
				log("\n");
				for (auto &it : cell_help_messages.cell_help) {
					string line = split_tokens(it.second, "\n").at(0);
					string cell_name = next_token(line);
					log("    %-15s %s\n", cell_name.c_str(), line.c_str());
				}
				log("\n");
				log("Type 'help <cell_type>' for more information on a cell type.\n");
				log("\n");
				return;
			}
			// this option is undocumented as it is for internal use only
			else if (args[1] == "-write-tex-command-reference-manual") {
				FILE *f = fopen("command-reference-manual.tex", "wt");
				fprintf(f, "%% Generated using the yosys 'help -write-tex-command-reference-manual' command.\n\n");
				for (auto &it : pass_register) {
					std::ostringstream buf;
					log_streams.push_back(&buf);
					it.second->help();
					if (it.second->experimental_flag) {
						log("\n");
						log("WARNING: THE '%s' COMMAND IS EXPERIMENTAL.\n", it.first.c_str());
						log("\n");
					}
					log_streams.pop_back();
					write_tex(f, it.first, it.second->short_help, buf.str());
				}
				fclose(f);
			}
			// this option is undocumented as it is for internal use only
			else if (args[1] == "-write-web-command-reference-manual") {
				FILE *f = fopen("templates/cmd_index.in", "wt");
				for (auto &it : pass_register) {
					std::ostringstream buf;
					log_streams.push_back(&buf);
					it.second->help();
					if (it.second->experimental_flag) {
						log("\n");
						log("WARNING: THE '%s' COMMAND IS EXPERIMENTAL.\n", it.first.c_str());
						log("\n");
					}
					log_streams.pop_back();
					write_html(f, it.first, it.second->short_help, buf.str());
				}
				fclose(f);
			}
			else if (pass_register.count(args[1])) {
				pass_register.at(args[1])->help();
				if (pass_register.at(args[1])->experimental_flag) {
					log("\n");
					log("WARNING: THE '%s' COMMAND IS EXPERIMENTAL.\n", args[1].c_str());
					log("\n");
				}
			}
			else if (cell_help_messages.cell_help.count(args[1])) {
				log("%s", cell_help_messages.cell_help.at(args[1]).c_str());
				log("Run 'help %s+' to display the Verilog model for this cell type.\n", args[1].c_str());
				log("\n");
			}
			else if (cell_help_messages.cell_code.count(args[1])) {
				log("\n");
				log("%s", cell_help_messages.cell_code.at(args[1]).c_str());
			}
			else
				log("No such command or cell type: %s\n", args[1].c_str());
			return;
		}

		help();
	}
} HelpPass;

struct EchoPass : public Pass {
	EchoPass() : Pass("echo", "turning echoing back of commands on and off") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    echo on\n");
		log("\n");
		log("Print all commands to log before executing them.\n");
		log("\n");
		log("\n");
		log("    echo off\n");
		log("\n");
		log("Do not print all commands to log before executing them. (default)\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design*) YS_OVERRIDE
	{
		if (args.size() > 2)
			cmd_error(args, 2, "Unexpected argument.");

		if (args.size() == 2) {
			if (args[1] == "on")
				echo_mode = true;
			else if (args[1] == "off")
				echo_mode = false;
			else
				cmd_error(args, 1, "Unexpected argument.");
		}

		log("echo %s\n", echo_mode ? "on" : "off");
	}
} EchoPass;

SatSolver *yosys_satsolver_list;
SatSolver *yosys_satsolver;

struct MinisatSatSolver : public SatSolver {
	MinisatSatSolver() : SatSolver("minisat") {
		yosys_satsolver = this;
	}
	ezSAT *create() YS_OVERRIDE {
		return new ezMiniSAT();
	}
} MinisatSatSolver;

YOSYS_NAMESPACE_END
