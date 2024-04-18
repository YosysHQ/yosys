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
	// clang-format off
    if (// equality
        type == ID($bweqx) ||
        type == ID($nex) ||
        type == ID($eqx) ||
        // basic logic
        type == ID($and) ||
        type == ID($or) ||
        type == ID($xor) ||
        type == ID($xnor) ||
        type == ID($not) ||
        // mux
        type == ID($bwmux) ||
        type == ID($mux) ||
        type == ID($demux) ||
        // others
        type == ID($tribuf)) {
        return 1;
    } else if (type == ID($neg)) {
        return 4;
    } else if (type == ID($fa)) {
        return 5;
    } else if (// multi-bit adders
        type == ID($add) ||
        type == ID($sub) ||
        type == ID($alu)) {
        return 8;
    } else if (// left shift
        type == ID($shl) ||
        type == ID($sshl)) {
        return 10;
    }
	// clang-format on
	return 0;
}

static unsigned int max_inp_coef(RTLIL::IdString type)
{
	// clang-format off
    if (// binop reduce
        type == ID($reduce_and) ||
        type == ID($reduce_or) ||
        type == ID($reduce_xor) ||
        type == ID($reduce_xnor) ||
        type == ID($reduce_bool) ||
        // others
        type == ID($logic_not) ||
        type == ID($pmux) ||
        type == ID($bmux)) {
        return 1;
    } else if (// equality
        type == ID($eq) ||
        type == ID($ne) ||
        // logic
        type == ID($logic_and) ||
        type == ID($logic_or)) {
        return 2;
    } else if (type == ID($lcu)) {
        return 5;
    } else if (// comparison
        type == ID($lt) ||
        type == ID($le) ||
        type == ID($ge) ||
        type == ID($gt) ||
        // others
        type == ID($sop)) {
        return 6;
	}
	// clang-format on
	return 0;
}

static unsigned int sum_coef(RTLIL::IdString type)
{
	// clang-format off
    if (// right shift
        type == ID($shr) ||
        type == ID($sshr)) {
        return 4;
    } else if (// shift
        type == ID($shift) ||
        type == ID($shiftx)) {
        return 8;
	}
	// clang-format on
	return 0;
}

static unsigned int is_div_mod(RTLIL::IdString type)
{
	return (type == ID($div) || type == ID($divfloor) || type == ID($mod) || type == ID($modfloor));
}

static bool is_free(RTLIL::IdString type)
{
	// clang-format off
    return (// tags
        type == ID($overwrite_tag) ||
        type == ID($set_tag) ||
        type == ID($original_tag) ||
        type == ID($get_tag) ||
        // formal
        type == ID($check) ||
        type == ID($equiv) ||
        type == ID($initstate) ||
        type == ID($assert) ||
        type == ID($assume) ||
        type == ID($live) ||
        type == ID($cover) ||
        type == ID($allseq) ||
        type == ID($allconst) ||
        type == ID($anyseq) ||
        type == ID($anyinit) ||
        type == ID($anyconst) ||
        type == ID($fair) ||
        // utilities
        type == ID($scopeinfo) ||
        type == ID($print) ||
        // real but free
        type == ID($concat) ||
        type == ID($slice) ||
        type == ID($pos) ||
        // specify
        type == ID($specrule) ||
        type == ID($specify2) ||
        type == ID($specify3));
	// clang-format on
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

	if (gate_type_cost().count(cell->type))
		return gate_type_cost().at(cell->type);

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
	} else if (is_div_mod(cell->type)) {
		// quadratic with sum of port widths
		int sum = port_width_sum(cell);
        log_debug("%s coef*(sum**2) 5 * %d\n", cell->name.c_str(), sum * sum);
		return 5 * sum * sum;
	} else if (is_free(cell->type)) {
		log_debug("%s is free\n", cell->name.c_str());
		return 0;
	}
	// TODO: $fsm $mem.*
	// ignored: $pow

	log_warning("Can't determine cost of %s cell (%d parameters).\n", log_id(cell->type), GetSize(cell->parameters));
	return 1;
}
