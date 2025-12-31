#include "kernel/unstable/patch.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

using namespace RTLIL;
Cell* Patch::addCell(IdString name, IdString type) {
    auto& cell = cells_.emplace_back(Cell::ConstructToken{});
	cell.name = std::move(name);
	cell.type = type;
    return &cell;
}

void Patch::patch() {
    for (auto& cell: cells_) {
        Cell* new_cell = mod->addCell(cell.name, &cell);
        for (auto [port_name, sig] : new_cell->connections()) {
            log_assert(yosys_celltypes.cell_known(cell.type));
            auto dir = cell.port_dir(port_name);
            if (dir == PD_OUTPUT || dir == PD_INOUT) {
                for (auto chunk : sig.chunks()) {
                    log_assert(chunk.is_wire());
                    auto* wire = chunk.wire;
                    wire->driverCell_->setPort(wire->driverPort_, SigSpec());
                    wire->driverCell_ = new_cell;
                    wire->driverPort_ = port_name;
                }
            }
        }
    }
}


YOSYS_NAMESPACE_END