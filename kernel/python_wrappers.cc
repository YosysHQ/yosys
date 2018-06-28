#ifdef WITH_PYTHON

#include "yosys.h"
#include <boost/python.hpp>

struct YosysDesign;
struct YosysModule;
struct YosysCell;
struct YosysWire;

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

struct YosysCell
{
	Yosys::RTLIL::IdString name;
	Yosys::RTLIL::IdString parent_name;

	YosysCell(Yosys::RTLIL::Cell* ref)
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

std::ostream &operator<<(std::ostream &ostr, const YosysCell &cell)
{
	ostr << "Cell with name " << cell.name.c_str();
	return ostr;
}

struct YosysWire
{
	Yosys::RTLIL::IdString name;
	Yosys::RTLIL::IdString parent_name;

	YosysWire(Yosys::RTLIL::Wire* ref)
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

std::ostream &operator<<(std::ostream &ostr, const YosysWire &wire)
{
	ostr << "Wire with name " << wire.name.c_str();
	return ostr;
}

struct YosysModule
{
	Yosys::RTLIL::IdString name;
	unsigned int parent_hashid;

	YosysModule(Yosys::RTLIL::Module* ref)
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
			result.append(new YosysCell(cell_it.second));
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
			result.append(new YosysWire(wire_it.second));
		}
		return result;
	}
};

std::ostream &operator<<(std::ostream &ostr, const YosysModule &module)
{
	ostr << "Module with name " << module.name.c_str();
	return ostr;
}

struct YosysDesign
{
	unsigned int hashid;

	YosysDesign(unsigned int hashid)
	{
		this->hashid = hashid;
	}

	YosysDesign()
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
			result.append(new YosysModule(mod_it.second));
		}
		return result;
	}
};

std::ostream &operator<<(std::ostream &ostr, const YosysDesign &design)
{
	ostr << "Design with id " << design.hashid;
	return ostr;
}

BOOST_PYTHON_MODULE(libyosys)
{
	using namespace boost::python;

	class_<YosysDesign>("YosysDesign", init<unsigned int>())
		.def(init<>())
		.def("get_modules", &YosysDesign::get_modules)
		;

	class_<YosysModule>("YosysModule", no_init)
		.def(boost::python::self_ns::str(boost::python::self_ns::self))
		.def(boost::python::self_ns::repr(boost::python::self_ns::self))
		.def("get_cells", &YosysModule::get_cells)
		.def("get_wires", &YosysModule::get_wires)
		;

	class_<YosysCell>("YosysCell", no_init)
		.def(boost::python::self_ns::str(boost::python::self_ns::self))
		.def(boost::python::self_ns::repr(boost::python::self_ns::self))
		;

	class_<YosysWire>("YosysWire", no_init)
		.def(boost::python::self_ns::str(boost::python::self_ns::self))
		.def(boost::python::self_ns::repr(boost::python::self_ns::self))
		;


	def("yosys_setup",yosys_setup);
	def("run",run);
	def("yosys_shutdown",yosys_shutdown);
}

#endif

