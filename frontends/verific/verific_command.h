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
 */

#ifndef VERIFIC_COMMAND_H
#define VERIFIC_COMMAND_H

#ifdef YOSYS_ENABLE_VERIFIC

#include "kernel/register.h"
#include "frontends/verific/verific.h"

YOSYS_NAMESPACE_BEGIN

struct VerificCommand {
	Pass &pass;
	std::vector<std::string> &args;
	RTLIL::Design *design;
	int argidx = 1;
	std::string mode = {};
	std::string work = "work";
	bool is_work_set = false;
	std::vector<std::string> search_libraries = {};
	std::vector<std::string> tmp_files = {};

	VerificCommand(Pass &pass, std::vector<std::string> &args, RTLIL::Design *design);
	~VerificCommand();
	void run();
	static void reset_settings();

private:
	struct VerilogStandard;
	struct VhdlStandard;
	static const VerilogStandard *find_verilog_standard(const std::string &flag);
	static const VhdlStandard *find_vhdl_standard(const std::string &flag);

	std::string frontend_rewrite();
	void append_remaining_args(std::vector<std::string> &list);
	void apply_library_options();
	bool change_setting();

	void set_msg_type();
	void define_macros();
	void undefine_macros();
	void read_target();
	void read_f_file();
	void read_verilog(const VerilogStandard &standard);
	void read_vhdl(const VhdlStandard &standard);
	void read_edif();
	void read_liberty();
	void pretty_print();
	void import_design();
	void configure();
	void run_extension();
};

YOSYS_NAMESPACE_END

#endif
#endif
