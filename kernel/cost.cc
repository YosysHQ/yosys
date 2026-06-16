#include "kernel/cost.h"
#include "kernel/macc.h"

USING_YOSYS_NAMESPACE

unsigned int CellCosts::get(RTLIL::Module *mod)
{
	if (mod_cost_cache_.count(mod->meta_->name))
		return mod_cost_cache_.at(mod->meta_->name);

	unsigned int module_cost = 1;
	for (auto c : mod->cells()) {
		unsigned int new_cost = module_cost + get(c);
		module_cost = new_cost >= module_cost ? new_cost : INT_MAX;
	}

	mod_cost_cache_[mod->meta_->name] = module_cost;
	return module_cost;
}

static unsigned int y_coef(TwineRef type)
{
	if (
	  // equality
	  type.in(TW($bweqx), TW($nex), TW($eqx)) ||
	  // basic logic
	  type.in(TW($and), TW($or), TW($xor), TW($xnor), TW($not)) ||
	  // mux
	  type.in(TW($bwmux), TW($mux)) ||
	  // others
	  type == TW($tribuf)) {
		return 1;
	} else if (type == TW($neg)) {
		return 4;
	} else if (type == TW($demux)) {
		return 2;
	} else if (type == TW($fa)) {
		return 5;
	} else if (type.in(TW($add), TW($sub), TW($alu))) {
		// multi-bit adders
		return 8;
	} else if (type.in(TW($shl), TW($sshl))) {
		// left shift
		return 10;
	}
	return 0;
}

static unsigned int max_inp_coef(TwineRef type)
{
	if (
	  // binop reduce
	  type.in(TW($reduce_and), TW($reduce_or), TW($reduce_xor), TW($reduce_xnor), TW($reduce_bool)) ||
	  // others
	  type.in(TW($logic_not), TW($pmux), TW($bmux))) {
		return 1;
	} else if (
	  // equality
	  type.in(TW($eq), TW($ne)) ||
	  // logic
	  type.in(TW($logic_and), TW($logic_or))) {
		return 2;
	} else if (type == TW($lcu)) {
		return 5;
	} else if (type.in(TW($lt), TW($le), TW($ge), TW($gt))) {
		// comparison
		return 7;
	}
	return 0;
}

static unsigned int sum_coef(TwineRef type)
{
	if (type.in(TW($shr), TW($sshr))) {
		// right shift
		return 4;
	} else if (type.in(TW($shift), TW($shiftx))) {
		// shift
		return 8;
	}
	return 0;
}

static unsigned int is_div_mod(TwineRef type)
{
	return (type == TW($div) || type == TW($divfloor) || type == TW($mod) || type == TW($modfloor));
}

static bool is_free(TwineRef type)
{
	return (
	  // tags
	  type.in(TW($overwrite_tag), TW($set_tag), TW($original_tag), TW($get_tag)) ||
	  // formal
	  type.in(TW($check), TW($equiv), TW($initstate), TW($assert), TW($assume), TW($live), TW($cover), TW($fair)) ||
	  type.in(TW($allseq), TW($allconst), TW($anyseq), TW($anyconst), TW($anyinit)) ||
	  // utilities
	  type.in(TW($scopeinfo), TW($print)) ||
	  // real but free
	  type.in(TW($concat), TW($slice), TW($pos)) ||
	  // specify
	  type.in(TW($specrule), TW($specify2), TW($specify3)));
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

	if (cell->type == TW($bmux))
		return cell->getParam(ID::WIDTH).as_int() << cell->getParam(ID::S_WIDTH).as_int();

	for (RTLIL::IdString param : input_width_params)
		if (cell->hasParam(param))
			max = std::max(max, (unsigned int)cell->getParam(param).as_int());
	return max;
}

unsigned int port_width_sum(RTLIL::Cell *cell)
{
	unsigned int sum = 0;
	IdString port_width_params[] = {
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
	if (cmos_gate_cost().count(cell->type_impl))
		return 1;

	if (design_ && design_->module(cell->type_impl) && cell->parameters.empty()) {
		log_debug("%s is a module, recurse\n", cell->name);
		return get(design_->module(cell->type_impl));
	} else if (cell->is_builtin_ff()) {
		log_assert(cell->hasPort(TW::Q) && "Weird flip flop");
		log_debug("%s is ff\n", cell->name);
		return cell->getParam(ID::WIDTH).as_int();
	} else if (cell->type.in(TW($mem), TW($mem_v2))) {
		log_debug("%s is mem\n", cell->name);
		return cell->getParam(ID::WIDTH).as_int() * cell->getParam(ID::SIZE).as_int();
	} else if (y_coef(cell->type.ref())) {
		// linear with Y_WIDTH or WIDTH
		log_assert((cell->hasParam(ID::Y_WIDTH) || cell->hasParam(ID::WIDTH)) && "Unknown width");
		auto param = cell->hasParam(ID::Y_WIDTH) ? ID::Y_WIDTH : ID::WIDTH;
		int width = cell->getParam(param).as_int();
		if (cell->type == TW($demux))
			width <<= cell->getParam(ID::S_WIDTH).as_int();
		log_debug("%s Y*coef %d * %d\n", cell->name, width, y_coef(cell->type.ref()));
		return width * y_coef(cell->type.ref());
	} else if (sum_coef(cell->type.ref())) {
		// linear with sum of port widths
		unsigned int sum = port_width_sum(cell);
		log_debug("%s sum*coef %d * %d\n", cell->name, sum, sum_coef(cell->type.ref()));
		return sum * sum_coef(cell->type.ref());
	} else if (max_inp_coef(cell->type.ref())) {
		// linear with largest input width
		unsigned int max = max_inp_width(cell);
		log_debug("%s max*coef %d * %d\n", cell->name, max, max_inp_coef(cell->type.ref()));
		return max * max_inp_coef(cell->type.ref());
	} else if (is_div_mod(cell->type.ref()) || cell->type == TW($mul)) {
		// quadratic with sum of port widths
		unsigned int sum = port_width_sum(cell);
		unsigned int coef = cell->type == TW($mul) ? 3 : 5;
		log_debug("%s coef*(sum**2) %d * %d\n", cell->name, coef, sum * sum);
		return coef * sum * sum;
	} else if (cell->type.in(TW($macc), TW($macc_v2))) {
		// quadratic per term
		unsigned int cost_sum = 0;
		Macc macc;
		macc.from_cell(cell);
		unsigned int y_width = cell->getParam(ID::Y_WIDTH).as_int();
		for (auto &term: macc.terms) {
			if (term.in_b.empty()) {
				// neglect addends
				continue;
			}
			unsigned a_width = term.in_a.size(), b_width = term.in_b.size();
			unsigned int sum = a_width + b_width + std::min(y_width, a_width + b_width);
			cost_sum += 3 * sum * sum;
		}
		return cost_sum;
	} else if (cell->type == TW($lut)) {
		int width = cell->getParam(ID::WIDTH).as_int();
		unsigned int cost = 1U << (unsigned int)width;
		log_debug("%s is 2**%d\n", cell->name, width);
		return cost;
	} else if (cell->type == TW($sop)) {
		int width = cell->getParam(ID::WIDTH).as_int();
		int depth = cell->getParam(ID::DEPTH).as_int();
		log_debug("%s is (2*%d + 1)*%d\n", cell->name, width, depth);
		return (2 * width + 1) * depth;
	} else if (is_free(cell->type.ref())) {
		log_debug("%s is free\n", cell->name);
		return 0;
	}
	// TODO: $fsm
	// ignored: $pow $memrd $memwr $meminit (and v2 counterparts)

	log_warning("Can't determine cost of %s cell (%d parameters).\n", cell->type.unescape(), GetSize(cell->parameters));
	return 1;
}
