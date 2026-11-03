#include "kernel/metadata/attributes.h"

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

ExportedAttributes::ExportedAttributes(const RTLIL::Design *design, const RTLIL::AttrObject *obj)
{
	interned_values.reserve(std::size(RTLIL::interned_attributes));
	entries.reserve(std::size(RTLIL::interned_attributes) + obj->attributes.size());
	for (IdString id : RTLIL::interned_attributes)
		if (obj->has_attribute(id)) {
			interned_values.emplace_back(design->get_interned_attribute(obj, id));
			entries.push_back({id, interned_values.back()});
		}
	for (auto &[id, value] : obj->attributes)
		entries.push_back({id, value});
}

YOSYS_NAMESPACE_END
