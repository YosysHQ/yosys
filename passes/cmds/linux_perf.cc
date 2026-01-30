/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2014  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2014  Johann Glaser <Johann.Glaser@gmx.at>
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
#include "kernel/log_help.h"

#include <fcntl.h>
#include <stdlib.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#ifdef __linux__
#include <unistd.h>
struct LinuxPerf : public Pass {
	LinuxPerf() : Pass("linux_perf", "turn linux perf recording off or on") {
		internal();
	}
	bool formatted_help() override
	{
		auto *help = PrettyHelp::get_current();
		
		auto content_root = help->get_root();

		content_root->usage("linux_perf [on|off]");

		content_root->paragraph(
			"This pass turns Linux 'perf' profiling on or off, when it has been configured to use control FIFOs."
			"YOSYS_PERF_CTL and YOSYS_PERF_ACK must point to Linux perf control FIFOs."
		);
		content_root->paragraph("Example shell command line:");
		content_root->codeblock(
			"mkfifo /tmp/perf.fifo /tmp/perf-ack.fifo\n"
			"YOSYS_PERF_CTL=/tmp/perf.fifo YOSYS_PERF_ACK=/tmp/perf-ack.fifo \\\n"
			"  perf record --latency --delay=-1 \\\n"
			"  --control=fifo:/tmp/perf.fifo,/tmp/perf-ack.fifo --call-graph=dwarf ./yosys \\\n"
			"  -dt -p \"read_rtlil design.rtlil; linux_perf on; opt_clean; linux_perf off\"\n"
		);

		return true;
	}
	void execute(std::vector<std::string> args, RTLIL::Design *) override
	{
		if (args.size() > 2)
			cmd_error(args, 2, "Unexpected argument.");

		std::string_view ctl_msg;
		if (args.size() == 2) {
			if (args[1] == "on")
				ctl_msg = "enable\n";
			else if (args[1] == "off")
				ctl_msg = "disable\n";
			else
				cmd_error(args, 1, "Unexpected argument.");
		}

		const char *ctl_fifo = std::getenv("YOSYS_PERF_CTL");
		if (!ctl_fifo)
			log_error("YOSYS_PERF_CTL environment variable not set.");
		const char *ack_fifo = std::getenv("YOSYS_PERF_ACK");
		if (!ack_fifo)
			log_error("YOSYS_PERF_ACK environment variable not set.");

		int ctl_fd = open(ctl_fifo, O_WRONLY);
		if (ctl_fd < 0)
			log_error("Failed to open YOSYS_PERF_CTL.");
		int ack_fd = open(ack_fifo, O_RDONLY);
		if (ack_fd < 0)
			log_error("Failed to open YOSYS_PERF_ACK.");
		int result = write(ctl_fd, ctl_msg.data(), ctl_msg.size());
		if (result != static_cast<int>(ctl_msg.size()))
			log_error("Failed to write to YOSYS_PERF_CTL.");
		char buffer[64];
		result = read(ack_fd, buffer, sizeof(buffer));
		close(ctl_fd);
		close(ack_fd);
		if (result <= 0)
			log_error("Failed to read from YOSYS_PERF_ACK.");
		if (strcmp(buffer, "ack\n") != 0)
			log_error("YOSYS_PERF_ACK did not return 'ack'.");
	}
} LinuxPerf;
#endif

PRIVATE_NAMESPACE_END
