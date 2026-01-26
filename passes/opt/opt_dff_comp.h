#ifndef OPT_DFF_COMP_H
#define OPT_DFF_COMP_H

#include "kernel/rtlil.h"
#include <map>
#include <optional>

YOSYS_NAMESPACE_BEGIN

typedef std::map<RTLIL::SigBit, bool> pattern_t;

inline std::optional<RTLIL::SigBit> find_complementary_pattern_var(
	const pattern_t& left,
	const pattern_t& right
) {
	std::optional<RTLIL::SigBit> ret;
	for (const auto &pt : left) {
		if (right.count(pt.first) == 0)
			return std::nullopt;
		if (right.at(pt.first) == pt.second)
			continue;
		if (ret)
			return std::nullopt;
		ret = pt.first;
	}
	return ret;
}

YOSYS_NAMESPACE_END

#endif
