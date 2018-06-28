#ifdef WITH_PYTHON

#include "yosys.h"
#include <boost/python.hpp>

namespace YOSYS_PYTHON {

	struct Design;
	struct Module;
	struct Cell;
	struct Wire;

	void yosys_setup()
	{
		Yosys::log_streams.push_back(&std::cout);
		Yosys::log_error_stderr = true;

		Yosys::yosys_setup();
		Yosys::yosys_banner();
	}

	void run(std::string command)
	{
		Yosys::run_pass(command);
	}

	void yosys_shutdown()
	{
		Yosys::yosys_shutdown();
	}

	struct Cell
	{
		Yosys::RTLIL::IdString name;
		Yosys::RTLIL::IdString parent_name;

		Cell(Yosys::RTLIL::Cell* ref)
		{
			this->name = ref->name;
			this->parent_name = ref->module->name;
		}
	
		Yosys::RTLIL::Cell* get_cpp_obj()
		{
			Yosys::RTLIL::Design* active_design = Yosys::yosys_get_design();
			if(active_design == NULL)
				return NULL;
			if(active_design->modules_[this->parent_name] == NULL)
				return NULL;
			return active_design->modules_[this->parent_name]->cells_[this->name];
		}
	};

	std::ostream &operator<<(std::ostream &ostr, const Cell &cell)
	{
		ostr << "Cell with name " << cell.name.c_str();
		return ostr;
	}

	struct Wire
	{
		Yosys::RTLIL::IdString name;
		Yosys::RTLIL::IdString parent_name;

		Wire(Yosys::RTLIL::Wire* ref)
		{
			this->name = ref->name;
			this->parent_name = ref->module->name;
		}
	
		Yosys::RTLIL::Wire* get_cpp_obj()
		{
			Yosys::RTLIL::Design* active_design = Yosys::yosys_get_design();
			if(active_design == NULL)
				return NULL;
			if(active_design->modules_[this->parent_name] == NULL)
				return NULL;
			return active_design->modules_[this->parent_name]->wires_[this->name];
		}
	};

	std::ostream &operator<<(std::ostream &ostr, const Wire &wire)
	{
		ostr << "Wire with name " << wire.name.c_str();
		return ostr;
	}

	struct Module
	{
		Yosys::RTLIL::IdString name;
		unsigned int parent_hashid;

		Module(Yosys::RTLIL::Module* ref)
		{
			this->name = ref->name;
			this->parent_hashid = ref->design->hashidx_;
		}

		Yosys::RTLIL::Module* get_cpp_obj()
		{
			Yosys::RTLIL::Design* active_design = Yosys::yosys_get_design();
			if(active_design == NULL)
				return NULL;
			if(active_design->hashidx_ != this->parent_hashid)
				printf("Somehow the active design changed!\n");
			return active_design->modules_[this->name];
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
	};

	std::ostream &operator<<(std::ostream &ostr, const Module &module)
	{
		ostr << "Module with name " << module.name.c_str();
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
			Yosys::RTLIL::Design* active_design = Yosys::yosys_get_design();
			if(active_design != NULL)
			{
				printf("design is not null and has id %u\n", active_design->hashidx_);
				this->hashid = active_design->hashidx_;
			}
		}

		boost::python::list get_modules()
		{
			Yosys::RTLIL::Design* active_design = Yosys::yosys_get_design();
			boost::python::list result;
			if(active_design == NULL)
				return result;
			for(auto &mod_it : active_design->modules_)
			{
				result.append(new Module(mod_it.second));
			}
			return result;
		}
	};

	std::ostream &operator<<(std::ostream &ostr, const Design &design)
	{
		ostr << "Design with id " << design.hashid;
		return ostr;
	}

	BOOST_PYTHON_MODULE(libyosys)
	{
		using namespace boost::python;

		class_<Design>("Design", init<unsigned int>())
			.def(init<>())
			.def("get_modules", &Design::get_modules)
			;

		class_<Module>("Module", no_init)
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			.def("get_cells", &Module::get_cells)
			.def("get_wires", &Module::get_wires)
			;

		class_<Cell>("Cell", no_init)
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			;

		class_<Wire>("Wire", no_init)
			.def(boost::python::self_ns::str(boost::python::self_ns::self))
			.def(boost::python::self_ns::repr(boost::python::self_ns::self))
			;


		def("yosys_setup",yosys_setup);
		def("run",run);
		def("yosys_shutdown",yosys_shutdown);
	}

}
#endif
