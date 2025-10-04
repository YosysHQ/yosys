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
 */

#ifdef YOSYS_ENABLE_PYTHON

// <!-- generated includes -->
#include <pybind11/pybind11.h>
#include <pybind11/native_enum.h>
#include "pyosys/hashlib.h"

namespace py = pybind11;

USING_YOSYS_NAMESPACE

using std::set;
using std::regex;
using std::ostream;
using namespace RTLIL;

#include "wrappers.inc.cc"

namespace pyosys {
	struct Globals {};

	// Trampolines for Classes with Python-Overridable Virtual Methods
	// https://pybind11.readthedocs.io/en/stable/advanced/classes.html#overriding-virtual-functions-in-python
	class PassTrampoline : public Pass {
	public:
		using Pass::Pass;

		void help() override {
			PYBIND11_OVERRIDE(void, Pass, help);
		}

		bool formatted_help() override {
			PYBIND11_OVERRIDE(bool, Pass, formatted_help);
		}

		void clear_flags() override {
			PYBIND11_OVERRIDE(void, Pass, clear_flags);
		}

		void execute(std::vector<std::string> args, RTLIL::Design *design) override {
			PYBIND11_OVERRIDE_PURE(
				void,
				Pass,
				execute,
				args,
				design
			);
		}

		void on_register() override {
			PYBIND11_OVERRIDE(void, Pass, on_register);
		}

		void on_shutdown() override {
			PYBIND11_OVERRIDE(void, Pass, on_shutdown);
		}

		bool replace_existing_pass() const override {
			PYBIND11_OVERRIDE(
				bool,
				Pass,
				replace_existing_pass
			);
		}
	};

	class MonitorTrampoline : public RTLIL::Monitor {
	public:
		using RTLIL::Monitor::Monitor;

		void notify_module_add(RTLIL::Module *module) override {
			PYBIND11_OVERRIDE(
				void,
				RTLIL::Monitor,
				notify_module_add,
				module
			);
		}

		void notify_module_del(RTLIL::Module *module) override {
			PYBIND11_OVERRIDE(
				void,
				RTLIL::Monitor,
				notify_module_del,
				module
			);
		}

		void notify_connect(
			RTLIL::Cell *cell,
			const RTLIL::IdString &port,
			const RTLIL::SigSpec &old_sig,
			const RTLIL::SigSpec &sig
		) override {
			PYBIND11_OVERRIDE(
				void,
				RTLIL::Monitor,
				notify_connect,
				cell,
				port,
				old_sig,
				sig
			);
		}

		void notify_connect(
			RTLIL::Module *module,
			const RTLIL::SigSig &sigsig
		) override {
			PYBIND11_OVERRIDE(
				void,
				RTLIL::Monitor,
				notify_connect,
				module,
				sigsig
			);
		}

		void notify_connect(
			RTLIL::Module *module,
			const std::vector<RTLIL::SigSig> &sigsig_vec
		) override {
			PYBIND11_OVERRIDE(
				void,
				RTLIL::Monitor,
				notify_connect,
				module,
				sigsig_vec
			);
		}

		void notify_blackout(
			RTLIL::Module *module
		) override {
			PYBIND11_OVERRIDE(
				void,
				RTLIL::Monitor,
				notify_blackout,
				module
			);
		}
	};

	PYBIND11_MODULE(libyosys, m) {
		// this code is run on import
		m.doc() = "python access to libyosys";

		if (!yosys_already_setup()) {
			log_streams.push_back(&std::cout);
			log_error_stderr = true;
			yosys_setup();

			// Cleanup
			m.add_object("_cleanup_handle", py::capsule([](){
				yosys_shutdown();
			}));
		}

		// Logging Methods
		m.def("log_header", [](Design *d, std::string s) { log_formatted_header(d, "%s", s); });
		m.def("log", [](std::string s) { log_formatted_string("%s", s); });
		m.def("log_file_info", [](std::string_view file, int line, std::string s) { log_formatted_file_info(file, line, s); });
		m.def("log_warning", [](std::string s) { log_formatted_warning("Warning: ", s); });
		m.def("log_warning_noprefix", [](std::string s) { log_formatted_warning("", s); });
		m.def("log_file_warning", [](std::string_view file, int line, std::string s) { log_formatted_file_warning(file, line, s); });
		m.def("log_error", [](std::string s) { log_formatted_error(s); });
		m.def("log_file_error", [](std::string_view file, int line, std::string s) { log_formatted_file_error(file, line, s); });

		// Namespace to host global objects
		auto global_variables = py::class_<Globals>(m, "Globals");

		// Trampoline Classes
		py::class_<Pass, pyosys::PassTrampoline, std::unique_ptr<Pass, py::nodelete>>(m, "Pass")
			.def(py::init([](std::string name, std::string short_help) {
				auto created = new pyosys::PassTrampoline(name, short_help);
				Pass::init_register();
				return created;
			}), py::arg("name"), py::arg("short_help"))
			.def("help", &Pass::help)
			.def("formatted_help", &Pass::formatted_help)
			.def("execute", &Pass::execute)
			.def("clear_flags", &Pass::clear_flags)
			.def("on_register", &Pass::on_register)
			.def("on_shutdown", &Pass::on_shutdown)
			.def("replace_existing_pass", &Pass::replace_existing_pass)
			.def("experimental", &Pass::experimental)
			.def("internal", &Pass::internal)
			.def("pre_execute", &Pass::pre_execute)
			.def("post_execute", &Pass::post_execute)
			.def("cmd_log_args", &Pass::cmd_log_args)
			.def("cmd_error", &Pass::cmd_error)
			.def("extra_args", &Pass::extra_args)
			.def("call", py::overload_cast<RTLIL::Design *,std::string>(&Pass::call))
			.def("call", py::overload_cast<RTLIL::Design *,std::vector<std::string>>(&Pass::call))
		;

		py::class_<RTLIL::Monitor, pyosys::MonitorTrampoline>(m, "Monitor")
			.def(py::init([]() {
				return new pyosys::MonitorTrampoline();
			}))
			.def("notify_module_add", &RTLIL::Monitor::notify_module_add)
			.def("notify_module_del", &RTLIL::Monitor::notify_module_del)
			.def(
				"notify_connect",
				py::overload_cast<
					RTLIL::Cell *,
					const RTLIL::IdString &,
					const RTLIL::SigSpec &,
					const RTLIL::SigSpec &
				>(&RTLIL::Monitor::notify_connect)
			)
			.def(
				"notify_connect",
				py::overload_cast<
					RTLIL::Module *,
					const RTLIL::SigSig &
				>(&RTLIL::Monitor::notify_connect)
			)
			.def(
				"notify_connect",
				py::overload_cast<
					RTLIL::Module *,
					const std::vector<RTLIL::SigSig> &
				>(&RTLIL::Monitor::notify_connect)
			)
			.def("notify_blackout", &RTLIL::Monitor::notify_blackout)
		;

		// Bind Opaque Containers
		bind_autogenerated_opaque_containers(m);

		// <!-- generated pymod-level code -->

		py::implicitly_convertible<std::string, RTLIL::IdString>();
		py::implicitly_convertible<const char *, RTLIL::IdString>();
	};
};

#endif // YOSYS_ENABLE_PYTHON
