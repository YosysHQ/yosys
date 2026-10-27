#include "frontends/common/attributes.h"

YOSYS_NAMESPACE_BEGIN

void import_attribute(RTLIL::Design *design, RTLIL::AttrObject *obj, RTLIL::IdString id, const RTLIL::Const &value)
{
	if (RTLIL::is_interned_attribute(id))
		design->set_interned_attribute(obj, id, value.decode_string());
	else
		obj->attributes[id] = value;
}

void import_attributes(RTLIL::Design *design, RTLIL::AttrObject *obj, dict<RTLIL::IdString, RTLIL::Const> attributes)
{
	for (IdString id : RTLIL::interned_attributes) {
		auto it = attributes.find(id);
		if (it == attributes.end())
			continue;
		design->set_interned_attribute(obj, id, it->second.decode_string());
		attributes.erase(it);
	}
	obj->attributes = std::move(attributes);
}

YOSYS_NAMESPACE_END
