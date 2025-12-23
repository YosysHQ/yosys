#include "kernel/unstable/patch.h"

YOSYS_NAMESPACE_BEGIN

using namespace RTLIL;
Cell* Patch::addCell(IdString name, IdString type) {
    auto& cell = cells_.emplace_back(Cell::ConstructToken{});
	cell.name = std::move(name);
	cell.type = type;
    return &cell;
}



YOSYS_NAMESPACE_END