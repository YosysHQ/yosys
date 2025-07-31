/* -*- c++ -*-
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
 */

#ifndef REGISTER_H
#define REGISTER_H

#include "kernel/yosys_common.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct Pass
{
	std::string pass_name, short_help;
	Pass(std::string name, std::string short_help = "** document me **");
	// Prefer overriding 'Pass::on_shutdown()' if possible
	virtual ~Pass();

	virtual void help();
	virtual void clear_flags();
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) = 0;

	int call_counter;
	int64_t runtime_ns;
	bool experimental_flag = false;

	void experimental() {
		experimental_flag = true;
	}

	struct pre_post_exec_state_t {
		Pass *parent_pass;
		int64_t begin_ns;
	};

	pre_post_exec_state_t pre_execute();
	void post_execute(pre_post_exec_state_t state);

	void cmd_log_args(const std::vector<std::string> &args);
	void cmd_error(const std::vector<std::string> &args, size_t argidx, std::string msg);
	void extra_args(std::vector<std::string> args, size_t argidx, RTLIL::Design *design, bool select = true);

	static void call(RTLIL::Design *design, std::string command);
	static void call(RTLIL::Design *design, std::vector<std::string> args);

	static void call_on_selection(RTLIL::Design *design, const RTLIL::Selection &selection, std::string command);
	static void call_on_selection(RTLIL::Design *design, const RTLIL::Selection &selection, std::vector<std::string> args);

	static void call_on_module(RTLIL::Design *design, RTLIL::Module *module, std::string command);
	static void call_on_module(RTLIL::Design *design, RTLIL::Module *module, std::vector<std::string> args);

	Pass *next_queued_pass;
	virtual void run_register();
	static void init_register();
	static void done_register();

	virtual void on_register();
	virtual void on_shutdown();
	virtual bool replace_existing_pass() const { return false; }
};

struct ScriptPass : Pass
{
	bool block_active, help_mode;
	RTLIL::Design *active_design;
	std::string active_run_from, active_run_to;

	ScriptPass(std::string name, std::string short_help = "** document me **") : Pass(name, short_help) { }

	virtual void script() = 0;

	bool check_label(std::string label, std::string info = std::string());
	void run(std::string command, std::string info = std::string());
	void run_nocheck(std::string command, std::string info = std::string());
	void run_script(RTLIL::Design *design, std::string run_from = std::string(), std::string run_to = std::string());
	void help_script();
};

struct Frontend : Pass
{
	// for reading of here documents
	static FILE *current_script_file;
	static std::string last_here_document;

	std::string frontend_name;
	Frontend(std::string name, std::string short_help = "** document me **");
	void run_register() override;
	~Frontend() override;
	void execute(std::vector<std::string> args, RTLIL::Design *design) override final;
	virtual void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) = 0;

	static std::vector<std::string> next_args;
	void extra_args(std::istream *&f, std::string &filename, std::vector<std::string> args, size_t argidx, bool bin_input = false);

	static void frontend_call(RTLIL::Design *design, std::istream *f, std::string filename, std::string command);
	static void frontend_call(RTLIL::Design *design, std::istream *f, std::string filename, std::vector<std::string> args);
};

struct Backend : Pass
{
	std::string backend_name;
	Backend(std::string name, std::string short_help = "** document me **");
	void run_register() override;
	~Backend() override;
	void execute(std::vector<std::string> args, RTLIL::Design *design) override final;
	virtual void execute(std::ostream *&f, std::string filename,  std::vector<std::string> args, RTLIL::Design *design) = 0;

	void extra_args(std::ostream *&f, std::string &filename, std::vector<std::string> args, size_t argidx, bool bin_output = false);

	static void backend_call(RTLIL::Design *design, std::ostream *f, std::string filename, std::string command);
	static void backend_call(RTLIL::Design *design, std::ostream *f, std::string filename, std::vector<std::string> args);
};

// implemented in passes/cmds/select.cc
extern void handle_extra_select_args(Pass *pass, const std::vector<std::string> &args, size_t argidx, size_t args_size, RTLIL::Design *design);
extern RTLIL::Selection eval_select_args(const vector<string> &args, RTLIL::Design *design);
extern void eval_select_op(vector<RTLIL::Selection> &work, const string &op, RTLIL::Design *design);

extern std::map<std::string, Pass*> pass_register;
extern std::map<std::string, Frontend*> frontend_register;
extern std::map<std::string, Backend*> backend_register;

YOSYS_NAMESPACE_END

#endif
