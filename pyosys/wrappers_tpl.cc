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

	static py::ssize_t name_hash(const RTLIL::PooledName &n)
	{
		if (!name_renderable(n))
			return py::hash(py::int_(n.ref().raw()));
		return py::hash(py::str(n.str()));
	}

	static bool name_lt(const RTLIL::PooledName &lhs, const RTLIL::PooledName &rhs)
	{
		return name_str(lhs) < name_str(rhs);
	}
	static TwinePool *twine_pool(RTLIL::Design &design) { return &design.twines(); }
	static TwinePool *twine_pool(RTLIL::Module &module) { return module.design ? &module.design->twines() : nullptr; }
	template<typename T>
	static TwinePool *twine_pool(T &obj) { return obj.module ? twine_pool(*obj.module) : nullptr; }

	static RTLIL::PooledName design_id_add(RTLIL::Design &self, const std::string &name)
	{
		return RTLIL::PooledName(&self.twines(), self.twines().add(name));
	}

	static py::object design_id_find(RTLIL::Design &self, const std::string &name)
	{
		RTLIL::IdString ref = self.twines().find(name);
		if (ref.empty())
			return py::none();
		return py::cast(RTLIL::PooledName(&self.twines(), ref));
	}

	static std::string design_str(RTLIL::Design &self, const RTLIL::PooledName &name)
	{
		if (name_renderable(name))
			return name.str();
		return self.twines().str(name.ref());
	}

	static py::list module_ports(RTLIL::Module &self)
	{
		TwinePool *pool = twine_pool(self);
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

	struct NameArg {
		RTLIL::PooledName name;
		std::string text;
		bool is_text = false;
	};

	static bool name_eq(const RTLIL::PooledName &lhs, const NameArg &rhs)
	{
		return name_str(lhs) == (rhs.is_text ? rhs.text : name_str(rhs.name));
	}

	static RTLIL::IdString resolve_name(TwinePool *pool, const NameArg &arg, bool create)
	{
		if (!arg.is_text) {
			RTLIL::IdString ref = arg.name.ref();
			const TwinePool *src = arg.name.pool();
			if (ref.empty() || ID::is_static(ref) || src == nullptr || pool == nullptr || src == pool)
				return ref;
			return create ? pool->copy_from(*src, ref) : pool->find_from(*src, ref);
		}
		const std::string &text = arg.text;
		if (text.empty() || (text[0] != '\\' && text[0] != '$'))
			throw py::value_error("RTLIL names must start with '\\' or '$', got '" + text + "'");
		RTLIL::IdString id;
		if (lookup_constid(text, id))
			return id;
		if (pool == nullptr)
			throw py::value_error("cannot resolve name '" + text + "': the object is not part of a design");
		return create ? pool->add(text) : pool->find(text);
	}

	template<typename Owner>
	static RTLIL::IdString resolve_name(Owner &self, const NameArg &arg, bool create)
	{
		return resolve_name(twine_pool(self), arg, create);
	}

	template<typename Owner>
	static RTLIL::PooledName pooled_name(Owner &self, RTLIL::IdString id)
	{
		return RTLIL::PooledName(twine_pool(self), id);
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

template <> struct type_caster<pyosys::NameArg> {
public:
	PYBIND11_TYPE_CASTER(pyosys::NameArg, const_name("IdString | str"));

	bool load(handle src, bool)
	{
		if (!src)
			return false;
		if (isinstance<Yosys::RTLIL::PooledName>(src)) {
			value.name = src.cast<const Yosys::RTLIL::PooledName &>();
			value.is_text = false;
			return true;
		}
		if (PyUnicode_Check(src.ptr())) {
			value.text = src.cast<std::string>();
			value.is_text = true;
			return true;
		}
		return false;
	}
};

template <typename Owner, typename Slot> struct type_caster<Yosys::RTLIL::OwnedId<Owner, Slot>> {
	static constexpr auto name = const_name("IdString");

	static handle cast(const Yosys::RTLIL::OwnedId<Owner, Slot> &src, return_value_policy, handle)
	{
		return pybind11::cast(Yosys::RTLIL::PooledName(src)).release();
	}
};

}
}

namespace pyosys {

	template<typename Value>
	struct NameMapView {
		using Map = dict<RTLIL::IdString, Value>;
		TwinePool *pool;
		Map *map;

		static constexpr py::return_value_policy policy =
			std::is_pointer_v<Value> ? py::return_value_policy::reference : py::return_value_policy::copy;

		typename Map::iterator find(const NameArg &name) const { return map->find(resolve_name(pool, name, false)); }

		typename Map::iterator at(const NameArg &name) const
		{
			auto it = find(name);
			if (it == map->end())
				throw py::key_error(name.is_text ? name.text : name_repr(name.name));
			return it;
		}

		py::list keys() const
		{
			py::list out;
			for (auto &entry : *map)
				out.append(RTLIL::PooledName(pool, entry.first));
			return out;
		}

		py::list values() const
		{
			py::list out;
			for (auto &entry : *map)
				out.append(py::cast(entry.second, policy));
			return out;
		}

		py::list items() const
		{
			py::list out;
			for (auto &entry : *map)
				out.append(py::make_tuple(RTLIL::PooledName(pool, entry.first), py::cast(entry.second, policy)));
			return out;
		}

		void assign(py::handle source)
		{
			Map fresh;
			py::object pairs = py::hasattr(source, "items") ? source.attr("items")() : py::reinterpret_borrow<py::object>(source);
			for (py::handle pair : pairs) {
				py::tuple kv = py::reinterpret_borrow<py::tuple>(pair);
				fresh[resolve_name(pool, kv[0].cast<NameArg>(), true)] = kv[1].cast<Value>();
			}
			*map = std::move(fresh);
		}
	};

	template<typename Value>
	static void bind_name_map_view(py::module &m, const char *name, bool writable)
	{
		using View = NameMapView<Value>;
		auto cls = py::class_<View>(m, name)
			.def("__getitem__", [](const View &v, const NameArg &key) { return py::cast(v.at(key)->second, View::policy); })
			.def("get", [](const View &v, const NameArg &key, py::object fallback) {
				auto it = v.find(key);
				return it == v.map->end() ? fallback : py::cast(it->second, View::policy);
			}, py::arg("name"), py::arg("default") = py::none())
			.def("__contains__", [](const View &v, const NameArg &key) { return v.find(key) != v.map->end(); })
			.def("__contains__", [](const View &, py::object) { return false; })
			.def("__len__", [](const View &v) { return v.map->size(); })
			.def("__iter__", [](const View &v) { return py::iter(v.keys()); })
			.def("keys", &View::keys)
			.def("values", &View::values)
			.def("items", &View::items)
			.def("__repr__", [](const View &v) { return "<" + std::string(py::str(py::dict(v.items()))) + ">"; });
		if (writable)
			cls.def("__setitem__", [](View &v, const NameArg &key, const Value &value) { (*v.map)[resolve_name(v.pool, key, true)] = value; })
				.def("__delitem__", [](View &v, const NameArg &key) { v.map->erase(v.at(key)); });
	}

	template<typename Owner, typename Value>
	static NameMapView<Value> name_view(Owner &owner, dict<RTLIL::IdString, Value> &map)
	{
		return {twine_pool(owner), &map};
	}

	template<typename Owner, typename PyClass, typename Member>
	static void def_name_dict(PyClass &&cls, const char *name, Member member, bool writable)
	{
		auto getter = [member](Owner &self) { return name_view(self, self.*member); };
		if (writable)
			cls.def_property(name, getter, [member](Owner &self, py::object source) { name_view(self, self.*member).assign(source); });
		else
			cls.def_property_readonly(name, getter);
	}

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
			logger().add_sink<ConsoleLogSink>();
			yosys_setup();

			// Cleanup
			m.add_object("_cleanup_handle", py::capsule([](){
				yosys_shutdown();
			}));
		}

		// Logging Methods
		m.def("log_header", [](Design *d, std::string s) { logger().formatted_header(d, "%s", s); });
		m.def("log", [](std::string s) { logger().formatted_string(LogSeverity::Info, LogSourceLocation{}, {}, "%s", s); });
		m.def("log_file_info", [](std::string file, int line, std::string s) { logger().formatted_string(LogSeverity::Info, LogSourceLocation(file,line), "Info: ", "%s", s); });
		m.def("log_warning", [](std::string s) { logger().formatted_warning(LogSourceLocation{}, "Warning: ", "%s", s); });
		m.def("log_warning_noprefix", [](std::string s) { logger().formatted_warning(LogSourceLocation{}, "", "%s", s); });
		m.def("log_file_warning", [](std::string file, int line, std::string s) { logger().formatted_warning(LogSourceLocation(file,line), "Warning: ", "%s", s); });
		m.def("log_error", [](std::string s) { logger().formatted_error(LogSourceLocation{}, "ERROR: ", "%s", s); });
		m.def("log_file_error", [](std::string file, int line, std::string s) { logger().formatted_error(LogSourceLocation(file,line), "ERROR: ", "%s", s); });

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
			.def("__lt__", &name_lt)
		;

		// Bind Opaque Containers
		bind_autogenerated_opaque_containers(m);

		// <!-- generated pymod-level code -->

		bind_name_map_view<RTLIL::Const>(m, "NameConstView", true);
		bind_name_map_view<RTLIL::SigSpec>(m, "NameSigSpecView", false);
		bind_name_map_view<RTLIL::Module *>(m, "NameModuleView", false);
		bind_name_map_view<RTLIL::Wire *>(m, "NameWireView", false);
		bind_name_map_view<RTLIL::Cell *>(m, "NameCellView", false);
		bind_name_map_view<RTLIL::Memory *>(m, "NameMemoryView", false);
		bind_name_map_view<RTLIL::Process *>(m, "NameProcessView", false);

		auto design_cls = py::reinterpret_borrow<py::class_<RTLIL::Design>>(m.attr("Design"));
		def_name_dict<RTLIL::Design>(design_cls, "modules_", &RTLIL::Design::modules_, false);
		design_cls
			.def("id_add", &design_id_add, py::arg("name"))
			.def("id_find", &design_id_find, py::arg("name"))
			.def("str", &design_str, py::arg("name"));

		auto module_cls = py::reinterpret_borrow<py::class_<RTLIL::Module>>(m.attr("Module"));
		def_name_dict<RTLIL::Module>(module_cls, "attributes", &RTLIL::Module::attributes, true);
		def_name_dict<RTLIL::Module>(module_cls, "wires_", &RTLIL::Module::wires_, false);
		def_name_dict<RTLIL::Module>(module_cls, "cells_", &RTLIL::Module::cells_, false);
		def_name_dict<RTLIL::Module>(module_cls, "memories", &RTLIL::Module::memories, false);
		def_name_dict<RTLIL::Module>(module_cls, "processes", &RTLIL::Module::processes, false);
		def_name_dict<RTLIL::Module>(module_cls, "parameter_default_values", &RTLIL::Module::parameter_default_values, true);
		module_cls.def_property_readonly("ports", &module_ports);

		auto cell_cls = py::reinterpret_borrow<py::class_<RTLIL::Cell>>(m.attr("Cell"));
		def_name_dict<RTLIL::Cell>(cell_cls, "attributes", &RTLIL::Cell::attributes, true);
		def_name_dict<RTLIL::Cell>(cell_cls, "parameters", &RTLIL::Cell::parameters, true);
		def_name_dict<RTLIL::Cell>(cell_cls, "connections_", &RTLIL::Cell::connections_, false);
		cell_cls.def_property("type",
			[](RTLIL::Cell &self) { return pooled_name(self, self.type.ref()); },
			[](RTLIL::Cell &self, const NameArg &type) { self.type = resolve_name(self, type, true); });

		def_name_dict<RTLIL::Wire>(py::reinterpret_borrow<py::class_<RTLIL::Wire>>(m.attr("Wire")), "attributes", &RTLIL::Wire::attributes, true);
		def_name_dict<RTLIL::Memory>(py::reinterpret_borrow<py::class_<RTLIL::Memory>>(m.attr("Memory")), "attributes", &RTLIL::Memory::attributes, true);
		def_name_dict<RTLIL::Process>(py::reinterpret_borrow<py::class_<RTLIL::Process>>(m.attr("Process")), "attributes", &RTLIL::Process::attributes, true);
	};
};
