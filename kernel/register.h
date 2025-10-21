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

#ifdef YOSYS_ENABLE_HELP_SOURCE
	#include <version>
#	if __cpp_lib_source_location == 201907L
		#include <source_location>
		using std::source_location;
		#define HAS_SOURCE_LOCATION
#	elif defined(__has_include)
#		if __has_include(<experimental/source_location>)
			#include <experimental/source_location>
			using std::experimental::source_location;
			#define HAS_SOURCE_LOCATION
#		endif
#	endif
#endif

#ifndef HAS_SOURCE_LOCATION
struct source_location { // dummy placeholder
	int line() const { return 0; }
	int column() const { return 0; }
	const char* file_name() const { return "unknown"; }
	const char* function_name() const { return "unknown"; }
	static const source_location current(...) { return source_location(); }
};
#endif

YOSYS_NAMESPACE_BEGIN

// Track whether garbage collection is enabled. Garbage collection must be disabled
// while any RTLIL objects (e.g. non-owning non-immortal IdStrings) exist outside Designs.
// Garbage collection is disabled whenever any GarbageCollectionGuard(false) is on the
// stack. These objects must be stack-allocated on the main thread.
class GarbageCollectionGuard
{
	bool was_enabled;
	static bool is_enabled_;
public:
	GarbageCollectionGuard(bool allow) : was_enabled(is_enabled_) {
		is_enabled_ &= allow;
	}
	~GarbageCollectionGuard() {
		is_enabled_ = was_enabled;
	}
	static bool is_enabled() { return is_enabled_; }
};

// Call from anywhere to request GC at the next safe point.
void request_garbage_collection();

// GC if GarbageCollectionGuard::is_enabled() and GC was requested.
void try_collect_garbage();

struct Pass
{
	std::string pass_name, short_help;
	source_location location;
	Pass(std::string name, std::string short_help = "** document me **",
		source_location location = source_location::current());
	// Prefer overriding 'Pass::on_shutdown()' if possible
	virtual ~Pass();

	// Makes calls to log() to generate help message
	virtual void help();
	// Uses PrettyHelp::get_current() to produce a more portable formatted help message
	virtual bool formatted_help();
	virtual void clear_flags();
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) = 0;

	int call_counter;
	int64_t runtime_ns;
	bool experimental_flag = false;
	bool internal_flag = false;

	static void subtract_from_current_runtime_ns(int64_t time_ns);

	void experimental() {
		experimental_flag = true;
	}

	void internal() {
		internal_flag = true;
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

	// This should return false if the pass holds onto RTLIL objects outside a Design while it
	// calls nested passes. For safety, we default to assuming the worst.
	virtual bool allow_garbage_collection_during_pass() const { return false; }
};

struct ScriptPass : Pass
{
	bool block_active, help_mode;
	RTLIL::Design *active_design;
	std::string active_run_from, active_run_to;

	ScriptPass(std::string name, std::string short_help = "** document me **", source_location location = source_location::current()) :
		Pass(name, short_help, location) { }

	virtual void script() = 0;

	bool check_label(std::string label, std::string info = std::string());
	void run(std::string command, std::string info = std::string());
	void run_nocheck(std::string command, std::string info = std::string());
	void run_script(RTLIL::Design *design, std::string run_from = std::string(), std::string run_to = std::string());
	void help_script();

	bool allow_garbage_collection_during_pass() const override { return true; }
};

struct Frontend : Pass
{
	// for reading of here documents
	static FILE *current_script_file;
	static std::string last_here_document;

	std::string frontend_name;
	Frontend(std::string name, std::string short_help = "** document me **",
		source_location location = source_location::current());
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
	Backend(std::string name, std::string short_help = "** document me **",
		source_location location = source_location::current());
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
