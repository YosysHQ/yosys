#ifdef WITH_PYTHON

#include "yosys.h"
#include <boost/python.hpp>

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
	unsigned int hashid;

	YosysCell(unsigned int hashid)
	{
		this->hashid = hashid;
	}

	YosysCell(Yosys::RTLIL::Cell* ref)
	{
		this->hashid = ref->hashidx_;
	}
	
	Yosys::RTLIL::Cell* get_cpp_obj()
	{
		Yosys::RTLIL::Design* active_design = Yosys::yosys_get_design();
		if(active_design == NULL)
			return NULL;
		for(auto &mod_it : active_design->modules_)
		{
			for(auto &cell_it : mod_it.second->cells_)
				if(cell_it.second->hashidx_ == this->hashid)
					return cell_it.second;
		}
		return NULL;
	}
};

std::ostream &operator<<(std::ostream &ostr, const YosysCell &cell)
{
	ostr << "Cell with id " << cell.hashid;
	return ostr;
}

struct YosysWire
{
	unsigned int hashid;

	YosysWire(unsigned int hashid)
	{
		this->hashid = hashid;
	}

	YosysWire(Yosys::RTLIL::Wire* ref)
	{
		this->hashid = ref->hashidx_;
	}
	
	Yosys::RTLIL::Wire* get_cpp_obj()
	{
		Yosys::RTLIL::Design* active_design = Yosys::yosys_get_design();
		if(active_design == NULL)
			return NULL;
		for(auto &mod_it : active_design->modules_)
		{
			for(auto &wire_it : mod_it.second->wires_)
				if(wire_it.second->hashidx_ == this->hashid)
					return wire_it.second;
		}
		return NULL;
	}
};

std::ostream &operator<<(std::ostream &ostr, const YosysWire &wire)
{
	ostr << "Wire with id " << wire.hashid;
	return ostr;
}


struct YosysModule
{
	unsigned int hashid;

	YosysModule(unsigned int hashid)
	{
		this->hashid = hashid;
	}

	YosysModule(Yosys::RTLIL::Module* ref)
	{
		this->hashid = ref->hashidx_;
	}

	Yosys::RTLIL::Module* get_cpp_obj()
	{
		Yosys::RTLIL::Design* active_design = Yosys::yosys_get_design();
		if(active_design == NULL)
			return NULL;
		for(auto &mod_it : active_design->modules_)
		{
			if(mod_it.second->hashidx_ == this->hashid)
				return mod_it.second;
		}
		return NULL;
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
	ostr << "Module with id " << module.hashid;
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
			/*
			for (auto &mod_it : active_design->modules_)
			{
				printf("found module in design!!!\n");
				//design->add(it.second->clone());
				
				for (auto &wire_it : mod_it.second->wires_)
				{
					printf("found wire in module!!!\n");
				}

				for (auto &cell_it : mod_it.second->cells_)
				{
					printf("found cell in module!!!\n");
				}
			}*/
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

	class_<YosysModule>("YosysModule", init<unsigned int>())
		.def(boost::python::self_ns::str(boost::python::self_ns::self))
		.def(boost::python::self_ns::repr(boost::python::self_ns::self))
		.def("get_cells", &YosysModule::get_cells)
		.def("get_wires", &YosysModule::get_wires)
		;

	class_<YosysCell>("YosysCell", init<unsigned int>())
		.def(boost::python::self_ns::str(boost::python::self_ns::self))
		.def(boost::python::self_ns::repr(boost::python::self_ns::self))
		;

	class_<YosysWire>("YosysWire", init<unsigned int>())
		.def(boost::python::self_ns::str(boost::python::self_ns::self))
		.def(boost::python::self_ns::repr(boost::python::self_ns::self))
		;


	def("yosys_setup",yosys_setup);
	def("run",run);
	def("yosys_shutdown",yosys_shutdown);
}

#endif

