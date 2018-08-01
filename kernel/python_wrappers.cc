#ifdef WITH_PYTHON

#include "yosys.h"
#include <boost/python/module.hpp>
#include <boost/python/class.hpp>
#include <boost/python/wrapper.hpp>
#include <boost/python/call.hpp>
#include <boost/python.hpp>

namespace YOSYS_PYTHON {

	struct Design;
	struct Module;
	struct Cell;
	struct Wire;
	struct Monitor;

	void run(std::string command)
	{
		Yosys::run_pass(command);
	}

	struct Cell
	{
		unsigned int id;

		Cell(Yosys::RTLIL::Cell* ref)
		{
			this->id = ref->hashidx_;
		}
	
		Yosys::RTLIL::Cell* get_cpp_obj() const
		{
			return Yosys::RTLIL::Cell::get_all_cells()->at(this->id);
		}
	};

	std::ostream &operator<<(std::ostream &ostr, const Cell &cell)
	{
		if(cell.get_cpp_obj() != NULL)
			ostr << "Cell with name " << cell.get_cpp_obj()->name.c_str();
		else
			ostr << "deleted cell";
		return ostr;
	}

	struct Wire
	{
		unsigned int id;

		Wire(Yosys::RTLIL::Wire* ref)
		{
			this->id = ref->hashidx_;
		}
	
		Yosys::RTLIL::Wire* get_cpp_obj() const
		{
			return Yosys::RTLIL::Wire::get_all_wires()->at(this->id);
		}
	};

	std::ostream &operator<<(std::ostream &ostr, const Wire &wire)
	{
		if(wire.get_cpp_obj() != NULL)
			ostr << "Wire with name " << wire.get_cpp_obj()->name.c_str();
		else
			ostr << "deleted wire";
		return ostr;
	}

	struct Module
	{
		unsigned int id;

		Module(Yosys::RTLIL::Module* ref)
		{
			this->id = ref->hashidx_;
		}

		Yosys::RTLIL::Module* get_cpp_obj() const
		{
			return Yosys::RTLIL::Module::get_all_modules()->at(this->id);
		}

		boost::python::list get_cells()
		{
			Yosys::RTLIL::Module* cpp_mod = this->get_cpp_obj();
			boost::python::list result;
			if(cpp_mod == NULL)
				return result;
			for(auto &cell_it : cpp_mod->cells_)
			{
				result.append(new Cell(cell_it.second));
			}
			return result;
		}

		boost::python::list get_wires()
		{
			Yosys::RTLIL::Module* cpp_mod = this->get_cpp_obj();
			boost::python::list result;
			if(cpp_mod == NULL)
				return result;
			for(auto &wire_it : cpp_mod->wires_)
			{
				result.append(new Wire(wire_it.second));
			}
			return result;
		}

		void register_monitor(Monitor* const m);
	};

	std::ostream &operator<<(std::ostream &ostr, const Module &module)
	{
		if(module.get_cpp_obj() != NULL)
			ostr << "Module with name " << module.get_cpp_obj()->name.c_str();
		else
			ostr << "deleted module";
		return ostr;
	}

	struct Design
	{
		unsigned int hashid;

		Design(unsigned int hashid)
		{
			this->hashid = hashid;
		}

		Design()
		{
			Yosys::RTLIL::Design* new_design = new Yosys::RTLIL::Design();
			this->hashid = new_design->hashidx_;
		}

		Yosys::RTLIL::Design* get_cpp_obj()
		{
			return Yosys::RTLIL::Design::get_all_designs()->at(hashid);
		}

		boost::python::list get_modules()
		{
			Yosys::RTLIL::Design* cpp_design = get_cpp_obj();
			boost::python::list result;
			if(cpp_design == NULL)
			{
				return result;
			}
			for(auto &mod_it : cpp_design->modules_)
			{
				result.append(new Module(mod_it.second));
			}
			return result;
		}

		void run(std::string command)
		{
			Yosys::RTLIL::Design* cpp_design = get_cpp_obj();
			if(cpp_design != NULL)
				Yosys::run_pass(command, cpp_design);
		}

		void register_monitor(Monitor* const m);
	};

	struct Monitor : public Yosys::RTLIL::Monitor
	{

		virtual void notify_module_add(Yosys::RTLIL::Module *module) YS_OVERRIDE
		{
			py_notify_module_add(new Module(module));
		}

		virtual void notify_module_del(Yosys::RTLIL::Module *module) YS_OVERRIDE
		{
			py_notify_module_del(new Module(module));
		}

		virtual void notify_connect(Yosys::RTLIL::Cell *cell, const Yosys::RTLIL::IdString &port, const Yosys::RTLIL::SigSpec &old_sig, Yosys::RTLIL::SigSpec &sig) YS_OVERRIDE
		{
			//@TODO: Implement once necessary classes are wrapped
		}

		virtual void notify_connect(Yosys::RTLIL::Module *module, const Yosys::RTLIL::SigSig &sigsig) YS_OVERRIDE
		{
			//@TODO: Implement once necessary classes are wrapped
		}

		virtual void notify_connect(Yosys::RTLIL::Module *module, const std::vector<Yosys::RTLIL::SigSig> &sigsig_vec) YS_OVERRIDE
		{
			//@TODO: Implement once necessary classes are wrapped
		}

		virtual void notify_blackout(Yosys::RTLIL::Module *module) YS_OVERRIDE
		{
			py_notify_blackout(new Module(module));
		}

		virtual void py_notify_module_add(Module*){};
		virtual void py_notify_module_del(Module*){};
		virtual void py_notify_blackout(Module*){};

	};

	struct MonitorWrap : Monitor, boost::python::wrapper<Monitor>
	{
		void py_notify_module_add(Module* m)
		{
			if(boost::python::override py_notify_module_add = this->get_override("py_notify_module_add"))
				py_notify_module_add(m);
			else
				Monitor::py_notify_module_add(m);
		}

		void default_py_notify_module_add(Module* m)
		{
			this->Monitor::py_notify_module_add(m);
		}

		void py_notify_module_del(Module* m)
		{
			if(boost::python::override py_notify_module_del = this->get_override("py_notify_module_del"))
				py_notify_module_del(m);
			else
				Monitor::py_notify_module_del(m);
		}

		void default_py_notify_module_del(Module* m)
		{
			this->Monitor::py_notify_module_del(m);
		}

		void py_notify_blackout(Module* m)
		{
			if(boost::python::override py_notify_blackout = this->get_override("py_notify_blackout"))
				py_notify_blackout(m);
			else
				Monitor::py_notify_blackout(m);
		}

		void default_py_notify_blackout(Module* m)
		{
			this->Monitor::py_notify_blackout(m);
		}
	};

	void Design::register_monitor(Monitor* const m)
	{
		Yosys::RTLIL::Design* cpp_design = this->get_cpp_obj();
		if(cpp_design == NULL)
			return;
		cpp_design->monitors.insert(m);
	}

	void Module::register_monitor(Monitor* const m)
	{
		Yosys::RTLIL::Module* cpp_design = this->get_cpp_obj();
		if(cpp_design == NULL)
			return;
		cpp_design->monitors.insert(m);
	}

	std::ostream &operator<<(std::ostream &ostr, const Design &design)
	{
		ostr << "Design with id " << design.hashid;
		return ostr;
	}

	unsigned int get_active_design_id()
	{
		Yosys::RTLIL::Design* active_design = Yosys::yosys_get_design();
		if(active_design != NULL)
		{
			return active_design->hashidx_;
		}
		return 0;
	}

	struct Initializer
	{
		Initializer() {
			Yosys::log_streams.push_back(&std::cout);
			Yosys::log_error_stderr = true;
			Yosys::yosys_setup();
			Yosys::yosys_banner();
		}

		Initializer(Initializer const &) {}

		~Initializer() {
			Yosys::yosys_shutdown();
		}
	};

	BOOST_PYTHON_MODULE(libyosys)
	{
		using namespace boost::python;

		class_<Initializer>("Initializer");
		scope().attr("_hidden") = new Initializer();

		class_<Design>("Design", init<unsigned int>())
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def(init<>())
			.def("get_modules", &Design::get_modules)
			.def("run",&Design::run)
			.def("register_monitor", &Design::register_monitor)
			;

		class_<Module>("Module", no_init)
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("get_cells", &Module::get_cells)
			.def("get_wires", &Module::get_wires)
			.def("register_monitor", &Module::register_monitor)
			;

		class_<Cell>("Cell", no_init)
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			;

		class_<Wire>("Wire", no_init)
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			;

		class_<MonitorWrap, boost::noncopyable>("Monitor")
			.def("py_notify_module_add", &Monitor::py_notify_module_add, &MonitorWrap::default_py_notify_module_add)
			.def("py_notify_module_del", &Monitor::py_notify_module_del, &MonitorWrap::default_py_notify_module_del)
			.def("py_notify_blackout", &Monitor::py_notify_blackout, &MonitorWrap::default_py_notify_blackout)
			;

		def("run",run);
		def("get_active_design_id",get_active_design_id);
	}

}
#endif
