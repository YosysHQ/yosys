#ifndef YOSYS_METADATA_ATTRIBUTES_H
#define YOSYS_METADATA_ATTRIBUTES_H

#include "kernel/rtlil.h"

#include <span>

YOSYS_NAMESPACE_BEGIN

void import_attribute(RTLIL::Design *design, RTLIL::AttrObject *obj, RTLIL::IdString id, const RTLIL::Const &value);
void import_attributes(RTLIL::Design *design, RTLIL::AttrObject *obj, dict<RTLIL::IdString, RTLIL::Const> attributes);

class ExportedAttributes
{
public:
	struct Entry {
		RTLIL::IdString name;
		const RTLIL::Const &value;
	};

	ExportedAttributes(const RTLIL::Design *design, const RTLIL::AttrObject *obj);
	ExportedAttributes(const ExportedAttributes &) = delete;
	ExportedAttributes &operator=(const ExportedAttributes &) = delete;

	std::vector<Entry>::const_iterator begin() const { return entries.begin(); }
	std::vector<Entry>::const_iterator end() const { return entries.end(); }
	int size() const { return GetSize(entries); }
	std::span<const Entry> interned() const { return std::span(entries).first(interned_values.size()); }

private:
	std::vector<RTLIL::Const> interned_values;
	std::vector<Entry> entries;
};

YOSYS_NAMESPACE_END

#endif
