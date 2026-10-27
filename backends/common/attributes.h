#ifndef BACKENDS_COMMON_ATTRIBUTES_H
#define BACKENDS_COMMON_ATTRIBUTES_H

#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

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

private:
	std::vector<RTLIL::Const> interned;
	std::vector<Entry> entries;
};

YOSYS_NAMESPACE_END

#endif
