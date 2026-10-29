// NetView: the Netlist of an RTLIL design
// - Instances  one per cell occurrence, depth first in statement order
// - Nets       one per SigMap bit, a $barrier joins its A and Y unless either is constant
// - Names      port, then 'keep', then public wire. 'hdlname' gives hdlpath

#ifndef NETVIEW_H
#define NETVIEW_H

#include "kernel/netlist.h"
#include "kernel/rtlil.h"

#include <memory>

YOSYS_NAMESPACE_BEGIN

namespace Netlist
{

struct CellLibrary {
	virtual ~CellLibrary();
	virtual bool ports(const Instance &inst, std::vector<Port> &out) = 0;
};

} // namespace Netlist

namespace detail
{
struct ViewData;
}

struct NetView final {
	struct BuildOptions {
		Netlist::CellLibrary *library = nullptr;
	};

	struct Counts {
		size_t instances = 0;
		size_t nets = 0;
		size_t pins = 0;
		bool operator==(const Counts &) const = default;
	};

	struct ScopeNames {
		std::vector<Netlist::OwnedName> names; // by path, then bit
		size_t shared = 0;		       // nets that share their canonical name with an earlier net
	};

	NetView();
	~NetView();
	NetView(const NetView &) = delete;
	NetView &operator=(const NetView &) = delete;

	void build(RTLIL::Design *design);
	void build(RTLIL::Design *design, const BuildOptions &options);
	static bool buildable(RTLIL::Design *design, std::string &reason);
	void clear();
	bool built() const;
	RTLIL::Design *design() const;
	Netlist::Instance *top() const;

	bool upToDate() const;
	void recheck();

	Counts counts() const;

	const std::vector<Netlist::Net *> &nets(const Netlist::Instance *scope) const;
	std::vector<Netlist::Net *> constNets(Netlist::Net::Const value) const;
	Netlist::NetName name(const Netlist::Net *net) const;
	const std::vector<Netlist::NetAlias> &aliases(const Netlist::Instance *scope) const;
	std::vector<Netlist::Pin *> leafPins(const Netlist::Net *net, Netlist::WalkTarget target) const;
	std::vector<std::string> childNames(const Netlist::Instance *scope) const;
	ScopeNames netNames(const Netlist::Instance *scope) const;
	std::string bodyKey(const Netlist::Instance *scope) const;

	RTLIL::Cell *cell(const Netlist::Instance *inst) const;
	RTLIL::Module *module(const Netlist::Instance *scope) const;
	Netlist::Instance *instance(const RTLIL::Cell *cell, const Netlist::Instance *scope) const;
	const std::vector<Netlist::Instance *> &scopes(const RTLIL::Module *module) const;
	const std::vector<RTLIL::SigBit> &wireBits(const Netlist::Net *net) const;

      private:
	std::unique_ptr<detail::ViewData> data_;
};

YOSYS_NAMESPACE_END

#endif
