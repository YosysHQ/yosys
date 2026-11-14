// NetView is a read-only, bit-level, unfolded netlist of an RTLIL design

#ifndef NETVIEW_H
#define NETVIEW_H

#include "kernel/rtlil.h"

#include <deque>
#include <memory>

YOSYS_NAMESPACE_BEGIN

namespace Netlist
{

struct Pin;
struct Net;

struct Port {
	std::string name; // unescaped
	int width = 0;
	int from = 0;     // left index of the declared range, to is the right one
	int to = 0;
	RTLIL::PortDir dir = RTLIL::PD_UNKNOWN;
	bool vector = false;         // declared with a range
	uint32_t first_pin = 0;      // of bit 0 in Instance::pins
	int hdlIndex(int bit) const; // the declared index of a bit
};

// one record per module or type of a library or blackbox, each other cell has its own with its connections as ports
struct CellType {
	enum class Kind : uint8_t { Module, LibraryCell, InternalCell };

	std::string name;      // cell type or module name, unescaped
	std::string hdl_name;  // the source module name before uniquify, else name
	uint64_t body_key = 0; // of a scope, equal for one source name and equal bodies
	Kind kind = Kind::Module;
	bool is_buffer = false; // the library or the yosys cell type gives it
	std::vector<Port> ports;
};

// a scope (top or submodule) has inner nets, a leaf (cell or blackbox) has none
// the RTLIL pointers of a record are valid while the view is upToDate()
struct Instance {
	std::string name;                 // local name, unescaped
	const CellType *type = nullptr;
	uint32_t id = 0;                  // 0 is the top
	Instance *parent = nullptr;
	RTLIL::Cell *cell = nullptr;      // none for the top
	RTLIL::Module *module = nullptr;  // none for leaves
	std::vector<Pin *> pins;          // one per port bit, in port then bit order
	std::vector<Instance *> children;
	// one net per SigMap bit that a pin touches, a tie net per constant 0 and 1
	// a $barrier joins its A and Y, a constant only from A
	std::vector<Net *> nets;
	bool isTop() const { return parent == nullptr; }
	bool isLeaf() const { return type->kind != CellType::Kind::Module; }
	Pin *findPin(const std::string &port, int bit) const;
};

// a top pin has only an inner net, top has no cell
struct Pin {
	Instance *inst = nullptr;
	Net *net = nullptr;      // outside, parent scope, from the cell connection
	Net *inner = nullptr;    // inside, instance scope, from the port wire
	uint32_t id = 0;         // from 1
	uint32_t port_index = 0; // in inst->type->ports
	int bit = 0;
	const Port &port() const;
	RTLIL::PortDir dir() const;
	int hdlIndex() const;
	bool isDriver() const;
};

struct NetName {
	std::string wire;
	int index = 0;
	bool scalar = false;
	auto operator<=>(const NetName &) const = default;
};

struct Net {
	enum class Const : uint8_t { None, Zero, One };

	Instance *scope = nullptr;
	uint32_t id = 0; // from 1
	Const constant = Const::None;
	std::vector<Pin *> pins;     // the pins in the scope on this net
	std::vector<Pin *> boundary; // the pins of the scope whose inner net this is
	NetName name;                // ranks port, then public wire, a constant has none
	RTLIL::SigBit name_bit;      // the wire bit that gives the name
};

// what a cell library knows of the leaf cell types
struct CellLibrary {
	virtual ~CellLibrary() = default;
	// type has its name and kind, fills its ports and facts, false if it does not know the type
	virtual bool describe(CellType &type) = 0;
};

} // namespace Netlist

namespace detail
{
struct ViewBuilder;
}

// the records are read only and live with the view
// a record id is its position, instances from 0 (top), pins and nets from 1
struct NetView final {
	// one instance per cell occurrence, depth first in statement order
	// log_cmd_error if not buildable() or a leaf type has no port model
	// with a library only a connected cell needs one
	explicit NetView(RTLIL::Design *design, Netlist::CellLibrary *library = nullptr);
	NetView(const NetView &) = delete;
	NetView &operator=(const NetView &) = delete;

	static bool buildable(RTLIL::Design *design, std::string &reason);
	RTLIL::Design *design() const { return design_; }
	Netlist::Instance *top() const { return top_; }

	// false when the name pool or fingerprint changed since build, or the design a shared_ptr held at build is gone
	// fingerprint has module names, blackbox ports, top, wires, cells, connections of view modules
	bool upToDate() const;

	Netlist::Instance *instance(const RTLIL::Cell *cell, const Netlist::Instance *scope) const;

	const std::deque<Netlist::Instance> &instances() const { return instances_; }
	const std::deque<Netlist::Pin> &pins() const { return pins_; }
	const std::deque<Netlist::Net> &nets() const { return nets_; }
private:
	friend struct NetTracker;
	friend struct detail::ViewBuilder;
	void markUpToDate(); // a checkpoint calls it, a barrier and an owned keep do not change the view
	RTLIL::Design *design_;
	Netlist::Instance *top_ = nullptr;
	std::deque<Netlist::Instance> instances_;
	std::deque<Netlist::Pin> pins_;
	std::deque<Netlist::Net> nets_;
	std::deque<Netlist::CellType> types_;
	dict<std::pair<uint32_t, uint32_t>, Netlist::Instance *> instance_by_cell_scope_; // by cell hashidx_ and parent id

	// the design at the build
	std::weak_ptr<const RTLIL::Design> design_owner_;
	bool design_shared_ = false;
	uint64_t fingerprint_ = 0;
	size_t twines_serial_ = 0;
	std::vector<std::string> watched_module_names_;
};

YOSYS_NAMESPACE_END

#endif
