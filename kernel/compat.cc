#include "hashlib.h"
#include "rtlil.h"

YOSYS_NAMESPACE_BEGIN

/**
 * not sure if I need this file but this couldn't go in either
 * hashlib or rtlil without adding an include to the other header
 */

dict<RTLIL::IdString, RTLIL::Const> cell_to_mod_params (const RTLIL::Cell::FakeParams& cell_params) {
    dict<RTLIL::IdString, RTLIL::Const> ret;
    for (auto i : cell_params){
        ret[i.first] = i.second;
    }
    return ret;

}

YOSYS_NAMESPACE_END
