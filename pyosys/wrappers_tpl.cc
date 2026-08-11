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

// <!-- generated includes -->
#include <pybind11/pybind11.h>
#include <pybind11/native_enum.h>
#include <pybind11/functional.h>

// duplicates for LSPs
#include "kernel/register.h"
#include "kernel/yosys_common.h"

#include "pyosys/hashlib.h"

namespace py = pybind11;

USING_YOSYS_NAMESPACE

using std::set;
using std::function;
using std::ostream;
using namespace RTLIL;

#include "wrappers.inc.cc"

namespace pyosys {
	struct Globals {};

	static bool name_renderable(const RTLIL::PooledName &n)
	{
		return n.pool() != nullptr || n.ref().empty() || ID::is_static(n.ref());
	}

	static std::string name_str(const RTLIL::PooledName &n)
	{
		if (!name_renderable(n))
			throw std::runtime_error(
				"this name has no twine pool to resolve against; render it with Design.str(name)");
		return n.str();
	}

	static std::string name_repr(const RTLIL::PooledName &n)
	{
		if (n.ref().empty())
			return "<IdString Null>";
		if (!name_renderable(n))
			return stringf("<IdString #%zu%s>", n.ref().untag().raw(), n.ref().isPublic() ? " public" : "");
		return stringf("<IdString %s>", n.str().c_str());
	}

	static size_t name_hash(const RTLIL::PooledName &n) { return run_hash(name_str(n)); }

	static bool name_eq(const RTLIL::PooledName &lhs, const RTLIL::PooledName &rhs)
	{
		return name_str(lhs) == name_str(rhs);
	}

	static bool name_eq_str(const RTLIL::PooledName &lhs, const std::string &rhs)
	{
		return name_str(lhs) == rhs;
	}

	static bool name_ne(const RTLIL::PooledName &lhs, const RTLIL::PooledName &rhs) { return !name_eq(lhs, rhs); }
	static bool name_ne_str(const RTLIL::PooledName &lhs, const std::string &rhs) { return !name_eq_str(lhs, rhs); }
	static bool name_lt(const RTLIL::PooledName &lhs, const RTLIL::PooledName &rhs)
	{
		return name_str(lhs) < name_str(rhs);
	}
	static const TwinePool *pool_of(const RTLIL::Design &design) { return &design.twines; }
	static const TwinePool *pool_of(const RTLIL::Module &module)
	{
		return module.design ? &module.design->twines : nullptr;
	}

	template<typename Owner, typename Map>
	static py::dict name_keyed_snapshot(Owner &self, const Map &map)
	{
		const TwinePool *pool = pool_of(self);
		py::dict out;
		for (const auto &entry : map)
			out[py::cast(RTLIL::PooledName(pool, entry.first))] =
				py::cast(entry.second, py::return_value_policy::reference);
		return out;
	}

	static py::dict design_modules(RTLIL::Design &self) { return name_keyed_snapshot(self, self.modules_); }
	static py::dict module_wires(RTLIL::Module &self) { return name_keyed_snapshot(self, self.wires_); }
	static py::dict module_cells(RTLIL::Module &self) { return name_keyed_snapshot(self, self.cells_); }

	static RTLIL::PooledName design_id_add(RTLIL::Design &self, const std::string &name)
	{
		return RTLIL::PooledName(&self.twines, self.twines.add(name));
	}

	static py::object design_id_find(RTLIL::Design &self, const std::string &name)
	{
		RTLIL::IdString ref = self.twines.find(name);
		if (ref.empty())
			return py::none();
		return py::cast(RTLIL::PooledName(&self.twines, ref));
	}

	static std::string design_str(RTLIL::Design &self, const RTLIL::PooledName &name)
	{
		if (name_renderable(name))
			return name.str();
		return self.twines.str(name.ref());
	}

	static py::list module_ports(RTLIL::Module &self)
	{
		const TwinePool *pool = pool_of(self);
		py::list out;
		for (RTLIL::IdString port : self.ports)
			out.append(py::cast(RTLIL::PooledName(pool, port)));
		return out;
	}

	static bool lookup_constid(const std::string &text, RTLIL::IdString &out)
	{
		try {
			out = ID::lookup(text);
			return true;
		} catch (...) {
			return false;
		}
	}
}

namespace pybind11 {
namespace detail {

template <> struct type_caster<Yosys::RTLIL::IdString> {
public:
	PYBIND11_TYPE_CASTER(Yosys::RTLIL::IdString, const_name("IdString"));

	bool load(handle src, bool)
	{
		if (!src)
			return false;
		if (isinstance<Yosys::RTLIL::PooledName>(src)) {
			value = src.cast<const Yosys::RTLIL::PooledName &>().ref();
			return true;
		}
		if (PyUnicode_Check(src.ptr()))
			return pyosys::lookup_constid(src.cast<std::string>(), value);
		return false;
	}

	static handle cast(Yosys::RTLIL::IdString src, return_value_policy, handle)
	{
		return pybind11::cast(Yosys::RTLIL::PooledName(src)).release();
	}
};

template <typename Masq> struct masq_caster {
	static constexpr auto name = const_name("IdString");

	static handle cast(const Masq &src, return_value_policy, handle)
	{
		return pybind11::cast(Yosys::RTLIL::PooledName(src)).release();
	}
};

template <typename Owner>
struct type_caster<Yosys::RTLIL::ObjNameMasq<Owner>> : masq_caster<Yosys::RTLIL::ObjNameMasq<Owner>> {};
template <> struct type_caster<Yosys::RTLIL::ModuleNameMasq> : masq_caster<Yosys::RTLIL::ModuleNameMasq> {};
template <> struct type_caster<Yosys::RTLIL::CellTypeMasq> : masq_caster<Yosys::RTLIL::CellTypeMasq> {};

}
}

namespace pyosys {

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
			RTLIL::IdString port,
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
					RTLIL::IdString,
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

		py::class_<RTLIL::PooledName>(m, "IdString")
			.def("str", &name_str)
			.def("empty", &RTLIL::PooledName::empty)
			.def("isPublic", &RTLIL::PooledName::isPublic)
			.def("__str__", &name_str)
			.def("__repr__", &name_repr)
			.def("__hash__", &name_hash)
			.def("__eq__", &name_eq)
			.def("__eq__", &name_eq_str)
			.def("__ne__", &name_ne)
			.def("__ne__", &name_ne_str)
			.def("__lt__", &name_lt)
		;

		// Bind Opaque Containers
		bind_autogenerated_opaque_containers(m);

		// <!-- generated pymod-level code -->

		py::reinterpret_borrow<py::class_<RTLIL::Design>>(m.attr("Design"))
			.def_property_readonly("modules_", &design_modules)
			.def("id_add", &design_id_add, py::arg("name"))
			.def("id_find", &design_id_find, py::arg("name"))
			.def("str", &design_str, py::arg("name"));
		py::reinterpret_borrow<py::class_<RTLIL::Module>>(m.attr("Module"))
			.def_property_readonly("wires_", &module_wires)
			.def_property_readonly("cells_", &module_cells)
			.def_property_readonly("ports", &module_ports);

	};
};
