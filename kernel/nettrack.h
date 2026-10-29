// NetTracker: refs find their objects again after passes change the design
// - checkpoint  before passes: takes the names, writes anchors on the cells and wires of the objects, and barriers in TrackMode::Barriers
// - passes      carry the anchors (attributes) and keep the barriers and the logic between them
// - resolve     in a view built after the passes with barrierInstances() as BuildOptions::barrier_instances:
//               finds the anchors and turns them into objects
// Rules:
// - identity is the signal plus the name at the checkpoint

#ifndef NETTRACK_H
#define NETTRACK_H

#include "kernel/netview.h"

YOSYS_NAMESPACE_BEGIN

namespace detail
{
struct TrackData;
}

enum class TrackMode : uint8_t { AnchorsOnly, Barriers };

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

	struct Result {
		std::vector<const Netlist::Pin *> old_scope_pins = {};
	};

	Kind kind;
	Hints hints = {};
	std::vector<const Netlist::Pin *> pins = {}; // of Pin and TopPort
	std::vector<const Netlist::Instance *> instances = {};
	std::vector<const Netlist::Net *> nets = {};
	Result result = {};
};

struct NetTracker final {
	NetTracker();
	~NetTracker();
	NetTracker(const NetTracker &) = delete;
	NetTracker &operator=(const NetTracker &) = delete;

	void checkpoint(NetView &view, const std::vector<TrackedRef *> &refs, TrackMode mode);
	void resolve(const NetView &view, const std::vector<TrackedRef *> &refs);
	void clear(RTLIL::Design *design);

	pool<const RTLIL::Cell *> barrierInstances(RTLIL::Design *design) const;
private:
	std::unique_ptr<detail::TrackData> data_;
};

YOSYS_NAMESPACE_END

#endif
