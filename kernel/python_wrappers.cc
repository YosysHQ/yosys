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
	};

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
		def("get_active_design_id",get_active_design_id);
		def("yosys_shutdown",yosys_shutdown);
	}

}
#endif
