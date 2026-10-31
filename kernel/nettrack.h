// NetTracker: refs find their objects again after passes change the design
// - checkpoint  before passes: takes the names, writes anchors on the cells and wires of the objects, and barriers in TrackMode::Barriers
// - passes      carry the anchors (attributes) and keep the barriers and the logic between them
// - resolve     in a view built after the passes with barrierInstances() as BuildOptions::barrier_instances:
//               finds the anchors and turns them into objects
// Rules:
// - identity is the signal plus the name at the checkpoint
// - a ref takes the pins on the cut side of its barriers
// - a hierarchical pin that flatten removed resolves to its leaf pins inside: the loads of an input, the drivers of an output

#ifndef NETTRACK_H
#define NETTRACK_H

#include "kernel/netview.h"

YOSYS_NAMESPACE_BEGIN

namespace detail
{
struct TrackData;
}

enum class TrackMode : uint8_t { AnchorsOnly, Barriers };

struct PortRename {
	std::string old_port;
	std::string new_port;
	const Netlist::Instance *inst;
};

struct TrackedRef {
	enum class Kind : uint8_t {
		Pin,
		Instance,
		Net,
		TopPort
	};

	struct Hints {
		bool keep_cell = false;
		bool keep_as_instance = false;
	};

	struct Origin {
		Netlist::PortDir hier_pin_dir = Netlist::PortDir::Unknown;
		bool on_barrier_instance = false;
		bool anchored_on_drivers = false;
	public:
		bool isHierarchicalPin() const;
	};

	struct Result {
		std::vector<const Netlist::Pin *> own_pins = {};
		std::vector<const Netlist::Pin *> loads_beyond = {};
		std::vector<const Netlist::Pin *> barrier_a_pins = {};
		std::vector<const Netlist::Pin *> barrier_y_pins = {};
		std::vector<const Netlist::Pin *> old_scope_pins = {};
		std::vector<PortRename> port_renames = {};
		bool flattened_hier_pin = false;
	};

	Kind kind;
	Hints hints = {};
	Origin origin = {};
	std::vector<const Netlist::Pin *> pins = {}; // of Pin and TopPort
	std::vector<const Netlist::Instance *> instances = {};
	std::vector<const Netlist::Net *> nets = {};
	Result result = {};
public:
	bool isBehindNewLogic() const;
	bool removedButLoadsKept() const;
};

struct NetTracker final {
	NetTracker();
	~NetTracker();
	NetTracker(const NetTracker &) = delete;
	NetTracker &operator=(const NetTracker &) = delete;

	void checkpoint(NetView &view, const std::vector<TrackedRef *> &refs, TrackMode mode);
	void resolve(const NetView &view, const std::vector<TrackedRef *> &refs);
	void clear(RTLIL::Design *design);

	void unprotect(RTLIL::Design *design);
	pool<const RTLIL::Cell *> barrierInstances(RTLIL::Design *design) const;

	bool isNewBuffer(const NetView &view, const Netlist::Instance *inst) const;
private:
	std::unique_ptr<detail::TrackData> data_;
};

YOSYS_NAMESPACE_END

#endif
