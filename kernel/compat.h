// TODO header whatever

#ifndef COMPAT_H
#define COMPAT_H

YOSYS_NAMESPACE_BEGIN

dict<RTLIL::IdString, RTLIL::Const> cell_to_mod_params (const RTLIL::Cell::FakeParams& cell_params);

YOSYS_NAMESPACE_END

#endif
