// NetTracker lets refs find objects again after passes change the design

#ifndef NETTRACK_H
#define NETTRACK_H

#include "kernel/netview.h"

YOSYS_NAMESPACE_BEGIN

namespace detail
{
struct TrackData;
}

struct PortRename {
	std::string old_port;
	const Netlist::Pin *pin;
};

// identity is the signal plus the name at the checkpoint
// field comments start with the kinds that use them
struct TrackedRef {
	enum class Kind : uint8_t {
		Pin,
		Instance,
		Net,
		TopPort
	};

	struct Hints {
		bool keep_cell = false;        // Pin, keep a multi-output leaf cell, cut all its pins
		bool keep_as_instance = false; // hierarchical Pin, its barrier becomes a Barrier instance
	};

	struct Origin {
		// Pin, Input or Output of a hierarchical pin, Inout is Input
		Netlist::PortDir hier_pin_dir = Netlist::PortDir::Unknown;
		bool on_barrier_instance = false;                          // Pin, was on a Barrier instance
		// Pin, a checkpoint without barriers moved a Barrier instance A pin to its drivers
		bool anchored_on_drivers = false;
	};

	struct Result {
		std::vector<const Netlist::Pin *> own_pins = {};       // Pin, pins of the anchored objects
		// hierarchical Pin, Instance (output barriers), Y side loads
		std::vector<const Netlist::Pin *> loads_beyond = {};
		// hierarchical Pin, A pins of its Barrier instance barriers
		std::vector<const Netlist::Pin *> barrier_a_pins = {};
		std::vector<const Netlist::Pin *> barrier_y_pins = {}; // hierarchical Pin, their Y pins
		// Net, leaf pins in the old scope of a net flatten merged
		std::vector<const Netlist::Pin *> old_scope_pins = {};
		// Instance, pins whose port name or bit changed since checkpoint
		std::vector<PortRename> port_renames = {};
		// hierarchical Pin, flatten removed it, pins are input loads or output drivers
		bool flattened_hier_pin = false;
	};

	Kind kind;                                   // caller fills kind, hints and the vector of the kind
	Hints hints = {};
	// checkpoint sets it without clearing, a ref given again keeps unset fields
	Origin origin = {};
	std::vector<const Netlist::Pin *> pins = {}; // Pin and TopPort, a resolved Pin has its cut sides or own_pins
	std::vector<const Netlist::Instance *> instances = {};
	std::vector<const Netlist::Net *> nets = {};
	Result result = {};                          // filled by resolve
public:
	bool isBehindNewLogic() const;    // Pin, new logic between own_pins and the cut sides in pins
	bool removedButLoadsKept() const; // Instance, cell gone, its barriers' Y side loads kept
};

// one live tracker per design, all in one thread
// an anchor marks where an object was, by netview_ref or barrier id
struct NetTracker final {
	NetTracker();
	~NetTracker();
	NetTracker(const NetTracker &) = delete;
	NetTracker &operator=(const NetTracker &) = delete;

	// drop old anchors, anchor the objects of each ref
	// checkpoint -> passes -> new view -> resolve
	void checkpoint(NetView &view, const std::vector<TrackedRef *> &refs, bool with_barriers);
	// point each checkpoint ref at what its anchors find, can rerun
	// hits match by old instance path, else all unless in a shared module
	void resolve(const NetView &view, const std::vector<TrackedRef *> &refs);
	// drop anchors, barriers stay until unprotect
	void clear(RTLIL::Design *design);
	// remove barriers and marks, keep anchors
	// runs optbarriers -remove as a pass
	void unprotect(RTLIL::Design *design);
	// BuildOptions::barrier_instances of the new view
	pool<const RTLIL::Cell *> barrierInstances(RTLIL::Design *design) const;
private:
	std::unique_ptr<detail::TrackData> data_;
};

YOSYS_NAMESPACE_END

#endif
