#ifndef FRONTENDS_COMMON_ATTRIBUTES_H
#define FRONTENDS_COMMON_ATTRIBUTES_H

#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

void import_attribute(RTLIL::Design *design, RTLIL::AttrObject *obj, RTLIL::IdString id, const RTLIL::Const &value);
void import_attributes(RTLIL::Design *design, RTLIL::AttrObject *obj, dict<RTLIL::IdString, RTLIL::Const> attributes);

YOSYS_NAMESPACE_END

#endif
