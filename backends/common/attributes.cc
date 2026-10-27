#include "backends/common/attributes.h"

YOSYS_NAMESPACE_BEGIN

ExportedAttributes::ExportedAttributes(const RTLIL::Design *design, const RTLIL::AttrObject *obj)
{
	interned.reserve(std::size(RTLIL::interned_attributes));
	entries.reserve(std::size(RTLIL::interned_attributes) + obj->attributes.size());
	for (IdString id : RTLIL::interned_attributes)
		if (obj->has_attribute(id)) {
			interned.emplace_back(design->get_interned_attribute(obj, id));
			entries.push_back({id, interned.back()});
		}
	for (auto &[id, value] : obj->attributes)
		entries.push_back({id, value});
}

YOSYS_NAMESPACE_END
