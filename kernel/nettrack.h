// NetTracker lets refs find objects again after passes change the design

#ifndef NETTRACK_H
#define NETTRACK_H

#include "kernel/netview.h"

YOSYS_NAMESPACE_BEGIN

namespace detail
{
struct TrackData;
}

// identity is the id of the cell, wire or barrier plus its scope at the checkpoint
struct TrackedRef {
	enum class Kind : uint8_t { Pin, Instance, Net };

	// caller fills kind and the vector of the kind, resolve refills the vector and makes a Net that is gone a Pin
	Kind kind;
	std::vector<const Netlist::Pin *> pins = {}; // of a Pin, a resolved leaf pin is on its cut side
	std::vector<const Netlist::Instance *> instances = {}; // of an Instance, when gone the cells between its barriers
	// resolve did not find the object, a Net that is not found becomes a Pin of the leaf pins that were on it
	bool gone = false;
	// the loads behind a leaf Pin or an Instance that is a wire or a constant now, a checkpoint anchors them as pins
	std::vector<const Netlist::Pin *> loads = {};
	// of an Instance, each old port with the pins now at its cut side
	// the cut side of an output with no new driver has the loads behind it
	struct PortCut {
		std::string port;
		bool is_output;
		std::vector<const Netlist::Pin *> pins;
	};
	std::vector<PortCut> port_cuts = {};
	std::vector<const Netlist::Net *> nets = {};
};

// the caller keeps to one tracker per design and one thread, not checked
// an anchor marks where an object was, by the netview_ref id of a cell, wire or barrier
// a checkpoint with protect puts keep_hierarchy on each scope with a private name above a ref object
// each checkpoint puts an id and an hdlname with its name on each scope cell, each cell and barrier of a ref
// the hdlname stays in the design, one with scope names in front stays as it is, see makeScopeNamesUnique
struct NetTracker final {
	NetTracker();
	~NetTracker();

	// drop old anchors, protect and anchor the objects of each ref, the view must be up to date
	// checkpoint -> passes -> new view -> resolve
	// without protect an object has only its id, a pass can remove it
	void checkpoint(NetView &view, const std::vector<TrackedRef *> &refs, bool protect = true);
	// point each checkpoint ref at what its anchors find, can rerun, see Resolver
	// only moved cells are twins, two that fit lose the ref, a copy can get the ref of a deleted cell
	// a hierarchical pin or net that flatten dissolved becomes the leaf pins that were on it, a Net is then a Pin
	void resolve(const NetView &view, const std::vector<TrackedRef *> &refs);
	// drop the ids and notes of the last checkpoint, barriers stay until unprotect
	void clear(RTLIL::Design *design);
	// remove barriers and marks, keep anchors, the caller gives protect = false to a later checkpoint
	// runs optbarriers -remove as a pass, so the pass hooks of the consumer see it
	void unprotect(RTLIL::Design *design);
private:
	std::unique_ptr<detail::TrackData> data_;
};

YOSYS_NAMESPACE_END

#endif
