// NetView: the Netlist of an RTLIL design
// - Instances  one per cell occurrence, depth first in statement order
// - Nets       one per SigMap bit, a $barrier joins its A and Y, a constant only from A
// - Names      port, then 'keep', then public wire. 'hdlname' gives hdlpath
// - Barriers   a $barrier of BuildOptions::barrier_instances is a Barrier instance
// - Lifetime   records live until clear(), build after clear() restarts the ids

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
	virtual bool isRegister(const Instance &inst);
	virtual bool isClockPin(const Pin &pin);
	virtual bool isBuffer(const Instance &inst);
};

} // namespace Netlist

namespace detail
{
struct ViewData;
}

struct NetView final {
	struct BuildOptions {
		Netlist::CellLibrary *library = nullptr;
		const pool<const RTLIL::Cell *> *barrier_instances = nullptr;
	};

	struct Counts {
		size_t instances = 0;
		size_t nets = 0;
		size_t pins = 0;
		bool operator==(const Counts &) const = default;
		void add(const Counts &other); // saturates at UINT32_MAX
		bool fitIds() const;
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
	void recheck() const;
	void markUpToDate();

	Counts counts() const;

	const std::vector<Netlist::Net *> &nets(const Netlist::Instance *scope) const;
	std::vector<Netlist::Net *> constNets(Netlist::Net::Const value) const;
	Netlist::NetName name(const Netlist::Net *net) const;
	const std::vector<Netlist::NetName> &aliases(const Netlist::Net *net) const; // of the public wire bits on the net
	std::vector<Netlist::Pin *> leafPins(const Netlist::Net *net, Netlist::WalkTarget target) const;
	uint64_t bodyKey(const Netlist::Instance *scope) const; // equal for equal bodies, a 64-bit hash

	RTLIL::Cell *cell(const Netlist::Instance *inst) const;
	RTLIL::Module *module(const Netlist::Instance *scope) const;
	Netlist::Instance *instance(const RTLIL::Cell *cell, const Netlist::Instance *scope) const;
	const std::vector<Netlist::Instance *> &scopes(const RTLIL::Module *module) const;
	const std::vector<RTLIL::SigBit> &wireBits(const Netlist::Net *net) const;
	// nullptr if no record has the id
	Netlist::Instance *instanceById(uint32_t id) const;
	Netlist::Pin *pinById(uint32_t id) const;
	Netlist::Net *netById(uint32_t id) const;

	bool isRegister(const Netlist::Instance *inst) const;
	bool isClockPin(const Netlist::Pin *pin) const;
	bool isBuffer(const Netlist::Instance *inst) const;

private:
	std::unique_ptr<detail::ViewData> data_;
};

YOSYS_NAMESPACE_END

#endif
