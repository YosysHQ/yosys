#include "kernel/cost.h"

USING_YOSYS_NAMESPACE

unsigned int CellCosts::get(RTLIL::Module *mod)
{
	if (mod_cost_cache_.count(mod->name))
		return mod_cost_cache_.at(mod->name);

	unsigned int module_cost = 1;
	for (auto c : mod->cells()) {
		unsigned int new_cost = module_cost + get(c);
		module_cost = new_cost >= module_cost ? new_cost : INT_MAX;
	}

	mod_cost_cache_[mod->name] = module_cost;
	return module_cost;
}

static unsigned int y_coef(RTLIL::IdString type)
{
	if (
	  // equality
	  type.in(ID($bweqx), ID($nex), ID($eqx)) ||
	  // basic logic
	  type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($not)) ||
	  // mux
	  type.in(ID($bwmux), ID($mux)) ||
	  // others
	  type == ID($tribuf)) {
		return 1;
	} else if (type == ID($neg)) {
		return 4;
	} else if (type == ID($demux)) {
		return 2;
	} else if (type == ID($fa)) {
		return 5;
	} else if (type.in(ID($add), ID($sub), ID($alu))) {
		// multi-bit adders
		return 8;
	} else if (type.in(ID($shl), ID($sshl))) {
		// left shift
		return 10;
	}
	return 0;
}

static unsigned int max_inp_coef(RTLIL::IdString type)
{
	if (
	  // binop reduce
	  type.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool)) ||
	  // others
	  type.in(ID($logic_not), ID($pmux), ID($bmux))) {
		return 1;
	} else if (
	  // equality
	  type.in(ID($eq), ID($ne)) ||
	  // logic
	  type.in(ID($logic_and), ID($logic_or))) {
		return 2;
	} else if (type == ID($lcu)) {
		return 5;
	} else if (type.in(ID($lt), ID($le), ID($ge), ID($gt))) {
		// comparison
		return 7;
	}
	return 0;
}

static unsigned int sum_coef(RTLIL::IdString type)
{
	if (type.in(ID($shr), ID($sshr))) {
		// right shift
		return 4;
	} else if (type.in(ID($shift), ID($shiftx))) {
		// shift
		return 8;
	}
	return 0;
}

static unsigned int is_div_mod(RTLIL::IdString type)
{
	return (type == ID($div) || type == ID($divfloor) || type == ID($mod) || type == ID($modfloor));
}

static bool is_free(RTLIL::IdString type)
{
	return (
	  // tags
	  type.in(ID($overwrite_tag), ID($set_tag), ID($original_tag), ID($get_tag)) ||
	  // formal
	  type.in(ID($check), ID($equiv), ID($initstate), ID($assert), ID($assume), ID($live), ID($cover), ID($fair)) ||
	  type.in(ID($allseq), ID($allconst), ID($anyseq), ID($anyconst), ID($anyinit)) ||
	  // utilities
	  type.in(ID($scopeinfo), ID($print)) ||
	  // real but free
	  type.in(ID($concat), ID($slice), ID($pos)) ||
	  // specify
	  type.in(ID($specrule), ID($specify2), ID($specify3)));
}

unsigned int max_inp_width(RTLIL::Cell *cell)
{
	unsigned int max = 0;
	RTLIL::IdString input_width_params[] = {
	  ID::WIDTH,
	  ID::A_WIDTH,
	  ID::B_WIDTH,
	  ID::S_WIDTH,
	};

	if (cell->type == ID($bmux))
		return cell->getParam(ID::WIDTH).as_int() << cell->getParam(ID::S_WIDTH).as_int();

	for (RTLIL::IdString param : input_width_params)
		if (cell->hasParam(param))
			max = std::max(max, (unsigned int)cell->getParam(param).as_int());
	return max;
}

unsigned int port_width_sum(RTLIL::Cell *cell)
{
	unsigned int sum = 0;
	RTLIL::IdString port_width_params[] = {
	  ID::WIDTH, ID::A_WIDTH, ID::B_WIDTH, ID::S_WIDTH, ID::Y_WIDTH,
	};

	for (auto param : port_width_params)
		if (cell->hasParam(param))
			sum += cell->getParam(param).as_int();

	return sum;
}

unsigned int CellCosts::get(RTLIL::Cell *cell)
{

	// simple 1-bit cells
	if (cmos_gate_cost().count(cell->type))
		return 1;

	if (design_ && design_->module(cell->type) && cell->parameters.empty()) {
		log_debug("%s is a module, recurse\n", cell->name.c_str());
		return get(design_->module(cell->type));
	} else if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
		log_assert(cell->hasPort(ID::Q) && "Weird flip flop");
		log_debug("%s is ff\n", cell->name.c_str());
		return cell->getParam(ID::WIDTH).as_int();
	} else if (y_coef(cell->type)) {
		// linear with Y_WIDTH or WIDTH
		log_assert((cell->hasParam(ID::Y_WIDTH) || cell->hasParam(ID::WIDTH)) && "Unknown width");
		auto param = cell->hasParam(ID::Y_WIDTH) ? ID::Y_WIDTH : ID::WIDTH;
		int width = cell->getParam(param).as_int();
		if (cell->type == ID($demux))
			width <<= cell->getParam(ID::S_WIDTH).as_int();
		log_debug("%s Y*coef %d * %d\n", cell->name.c_str(), width, y_coef(cell->type));
		return width * y_coef(cell->type);
	} else if (sum_coef(cell->type)) {
		// linear with sum of port widths
		unsigned int sum = port_width_sum(cell);
		log_debug("%s sum*coef %d * %d\n", cell->name.c_str(), sum, sum_coef(cell->type));
		return sum * sum_coef(cell->type);
	} else if (max_inp_coef(cell->type)) {
		// linear with largest input width
		unsigned int max = max_inp_width(cell);
		log_debug("%s max*coef %d * %d\n", cell->name.c_str(), max, max_inp_coef(cell->type));
		return max * max_inp_coef(cell->type);
	} else if (is_div_mod(cell->type) || cell->type == ID($mul)) {
		// quadratic with sum of port widths
		unsigned int sum = port_width_sum(cell);
		unsigned int coef = cell->type == ID($mul) ? 3 : 5;
		log_debug("%s coef*(sum**2) %d * %d\n", cell->name.c_str(), coef, sum * sum);
		return coef * sum * sum;
	} else if (cell->type == ID($lut)) {
		int width = cell->getParam(ID::WIDTH).as_int();
		unsigned int cost = 1U << (unsigned int)width;
		log_debug("%s is 2**%d\n", cell->name.c_str(), width);
		return cost;
	} else if (cell->type == ID($sop)) {
		int width = cell->getParam(ID::WIDTH).as_int();
		int depth = cell->getParam(ID::DEPTH).as_int();
		log_debug("%s is (2*%d + 1)*%d\n", cell->name.c_str(), width, depth);
		return (2 * width + 1) * depth;
	} else if (is_free(cell->type)) {
		log_debug("%s is free\n", cell->name.c_str());
		return 0;
	}
	// TODO: $fsm $mem.* $macc
	// ignored: $pow

	log_warning("Can't determine cost of %s cell (%d parameters).\n", log_id(cell->type), GetSize(cell->parameters));
	return 1;
}
