#include "kernel/metadata/attributes.h"

YOSYS_NAMESPACE_BEGIN

void import_attribute(RTLIL::Design *design, RTLIL::AttrObject *obj, RTLIL::IdString id, const RTLIL::Const &value)
{
	if (RTLIL::is_specialized_attribute(id))
		design->set_specialized_attribute(obj, id, value.decode_string());
	else
		obj->attributes[id] = value;
}

void import_attributes(RTLIL::Design *design, RTLIL::AttrObject *obj, dict<RTLIL::IdString, RTLIL::Const> attributes)
{
	for (IdString id : RTLIL::specialized_attributes) {
		auto it = attributes.find(id);
		if (it == attributes.end())
			continue;
		design->set_specialized_attribute(obj, id, it->second.decode_string());
		attributes.erase(it);
	}
	obj->attributes = std::move(attributes);
}

ExportedAttributes::ExportedAttributes(const RTLIL::Design *design, const RTLIL::AttrObject *obj)
{
	specialized_values.reserve(std::size(RTLIL::specialized_attributes));
	entries.reserve(std::size(RTLIL::specialized_attributes) + obj->attributes.size());
	for (IdString id : RTLIL::specialized_attributes)
		if (obj->has_attribute(id)) {
			specialized_values.emplace_back(design->get_specialized_attribute(obj, id));
			entries.push_back({id, specialized_values.back()});
		}
	for (auto &[id, value] : obj->attributes)
		entries.push_back({id, value});
}

YOSYS_NAMESPACE_END
