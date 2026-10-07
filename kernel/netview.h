// NetView: a Netlist built from an RTLIL design

#ifndef NETVIEW_H
#define NETVIEW_H

#include "kernel/netlist.h"
#include "kernel/rtlil.h"

#include <deque>

YOSYS_NAMESPACE_BEGIN

struct NetView final : public Netlist
{
	NetView() = default;
	NetView(const NetView &) = delete;
	NetView &operator=(const NetView &) = delete;

	void build(RTLIL::Design *design);
	void reset();
	bool built() const;
	static RTLIL::Module *topModule(RTLIL::Design *design);

	bool valid() const override;

	Instance *top() const override;
private:
	void buildTop(RTLIL::Module *top);
private:
	Instance *top_ = nullptr;

	// Records
	std::deque<Instance> instances_;
};

YOSYS_NAMESPACE_END

#endif
