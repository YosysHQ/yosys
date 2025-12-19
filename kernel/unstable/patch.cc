#include "kernel/unstable/patch.h"

YOSYS_NAMESPACE_BEGIN

using namespace RTLIL;
Cell* Patch::addCell(IdString name, IdString type) {
    auto& cell = cells_.emplace_back();
	cell.name = std::move(name);
	cell.type = type;
    return &cell;
}
// RTLIL::Cell *RTLIL::Module::addCell(RTLIL::IdString name, RTLIL::IdString type)
// {
// 	RTLIL::Cell *cell = new RTLIL::Cell;
// 	cell->name = std::move(name);
// 	cell->type = type;
// 	add(cell);
// 	return cell;
// }

YOSYS_NAMESPACE_END