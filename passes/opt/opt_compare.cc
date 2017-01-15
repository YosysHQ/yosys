#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"
USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN
void replace_le_cell(Cell* cell, Module* module){
	RTLIL::SigSpec a = cell->getPort("\\A");
	RTLIL::SigSpec b = cell->getPort("\\B");
	RTLIL::SigSpec y(RTLIL::State::S0, cell->parameters["\\Y_WIDTH"].as_int());
	if(b.is_fully_const() && b.is_fully_zero() ){ 
		if(cell->parameters["\\A_SIGNED"].as_bool()){
			// a < 0, can be replaced with a[MAX_BIT]
			log("Found x < 0 (signed), replacing with the last bit\n");
			int a_width = cell->parameters["\\A_WIDTH"].as_int();
			if(a_width > 0){
				y[0] = a[a_width-1];
				module->connect(cell->getPort("\\Y"), y);
				module->remove(cell);
			}
		}
	} 
}
void replace_ge_cell(Cell* cell, Module* module){
	RTLIL::SigSpec a = cell->getPort("\\A");
	RTLIL::SigSpec b = cell->getPort("\\B");
	RTLIL::SigSpec y = cell->getPort("\\Y");
	if(b.is_fully_const() && b.is_fully_zero()){
		if(cell->parameters["\\A_SIGNED"].as_bool()){
			log("Found x >= 0 (signed), optimizing\n");
			RTLIL::SigSpec a_prime(RTLIL::State::S0, cell->parameters["\\Y_WIDTH"].as_int());
			int a_width = cell->parameters["\\A_WIDTH"].as_int();
			if(a_width > 0){
				a_prime[0] = a[a_width-1];
				module->remove(cell);
				module->addNot("$not", a_prime, y,false);
			}
		}
	}
}
void optimize_compares(Design* design, Module* module){
	log_header(design, "Executing OPT_COMPARE pass.\n");
	log_push();
	TopoSort<RTLIL::Cell*, RTLIL::IdString::compare_ptr_by_name<RTLIL::Cell>> cells;
	for(auto cell: module->cells())
		if(design->selected(module,cell) && cell->type[0] == '$'){
			cells.node(cell);
		}
	cells.sort();
	for (auto cell: cells.sorted){
		if (cell->type == "$lt"){
			replace_le_cell(cell,module);
		}
		else if(cell->type == "$ge"){
			replace_ge_cell(cell,module);
		}
	}

}
struct OptCompare : public Pass {
	OptCompare() : Pass("opt_compare") {}
	virtual void execute(vector<string>, Design* design){
		for(auto module: design->selected_modules())
			optimize_compares(design,module);
	}
	virtual void help() {
		log("\n");
		log("opt_compare\n");
		log("\n");
		log("This pass optimizes some signed compares with 0.\n");
		log("In particular, it replaces a < 0 with the msb of a,\n");
		log("and a >= 0 with the inverted msb of a.\n");
		log("\n");

	}
} OptCompare;


PRIVATE_NAMESPACE_END
