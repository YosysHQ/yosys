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

#ifndef REGISTER_H
#define REGISTER_H

#include "kernel/rtlil.h"
#include <stdio.h>
#include <string>
#include <vector>
#include <map>

#ifdef YOSYS_ENABLE_TCL
#include <tcl.h>
extern Tcl_Interp *yosys_get_tcl_interp();
extern RTLIL::Design *yosys_get_tcl_design();
#endif

struct Pass
{
	std::string pass_name, short_help;
	Pass(std::string name, std::string short_help = "** document me **");
	virtual void run_register();
	virtual ~Pass();
	virtual void help();
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) = 0;

	void cmd_log_args(const std::vector<std::string> &args);
	void cmd_error(const std::vector<std::string> &args, size_t argidx, std::string msg);
	void extra_args(std::vector<std::string> args, size_t argidx, RTLIL::Design *design, bool select = true);

	static void call(RTLIL::Design *design, std::string command);
	static void call(RTLIL::Design *design, std::vector<std::string> args);

	static void init_register();
	static void done_register();
};

struct Frontend : Pass
{
	std::string frontend_name;
	Frontend(std::string name, std::string short_help = "** document me **");
	virtual void run_register();
	virtual ~Frontend();
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design);
	virtual void execute(FILE *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) = 0;

	static std::vector<std::string> next_args;
	void extra_args(FILE *&f, std::string &filename, std::vector<std::string> args, size_t argidx);

	static void frontend_call(RTLIL::Design *design, FILE *f, std::string filename, std::string command);
	static void frontend_call(RTLIL::Design *design, FILE *f, std::string filename, std::vector<std::string> args);
};

struct Backend : Pass
{
	std::string backend_name;
	Backend(std::string name, std::string short_help = "** document me **");
	virtual void run_register();
	virtual ~Backend();
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design);
	virtual void execute(FILE *&f, std::string filename,  std::vector<std::string> args, RTLIL::Design *design) = 0;

	void extra_args(FILE *&f, std::string &filename, std::vector<std::string> args, size_t argidx);

	static void backend_call(RTLIL::Design *design, FILE *f, std::string filename, std::string command);
	static void backend_call(RTLIL::Design *design, FILE *f, std::string filename, std::vector<std::string> args);
};

// implemented in kernel/select.cc
extern void handle_extra_select_args(Pass *pass, std::vector<std::string> args, size_t argidx, size_t args_size, RTLIL::Design *design);

namespace REGISTER_INTERN {
	extern int raw_register_count;
	extern bool raw_register_done;
	extern Pass *raw_register_array[];
	extern std::map<std::string, Pass*> pass_register;
	extern std::map<std::string, Frontend*> frontend_register;
	extern std::map<std::string, Backend*> backend_register;
}

#endif
