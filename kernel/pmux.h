#ifndef PMUX_H
#define PMUX_H

#include "kernel/yosys_common.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

struct PmuxBPortIterator {
    Cell* cell;
    std::vector<SigBit> b;
    int port_idx;
    int port_count;
    PmuxBPortIterator(Cell* mux) : cell(mux) {
        log_assert(mux->type == ID($mux) || mux->type == ID($pmux));
        port_idx = 0;
        b = mux->getPort(ID::B).to_sigbit_vector();
        
        port_count = GetSize(sig_b) / s_width;
    }
};

YOSYS_NAMESPACE_END

#endif
