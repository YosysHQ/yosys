// Netlist: a read-only, bit-level, unfolded netlist interface for external consumers
// Objects:
// - Instance  one occurrence of a cell or module, the top is an instance
//             with no parent, hierarchical instances own a scope of nets
// - Pin       one bit of one port of one instance
// - Net       one electrical node in one scope
// - Term      where a net meets its scope's boundary

#ifndef NETLIST_H
#define NETLIST_H

#include "kernel/yosys_common.h"

#include <cstdint>
#include <string>
#include <vector>

YOSYS_NAMESPACE_BEGIN

template <typename T> struct IdMap {
	T &operator[](uint32_t id)
	{
		if (data.size() <= id)
			data.resize(id + 1, T());
		return data[id];
	}
	const T &get(uint32_t id) const
	{
		if (id < data.size())
			return data[id];
		return fallback;
	}
	void clear() { data.clear(); }
	std::vector<T> data;
	T fallback = T();
};

struct Netlist
{
	struct Instance;
	struct Pin;
	struct Net;
	struct Term;

	enum class Dir : uint8_t {
		Unknown,
		Input,
		Output,
		Inout
	};

	struct PortShape {
		std::string name; // unescaped
		int width;
		int from;
		int to;
		Dir dir;
	};

	struct Instance {
		std::string name; // local name, unescaped
		std::string type; // cell type or module name, unescaped
		Instance *parent;
		uint32_t id;
		bool leaf;
		bool internal;
		const std::vector<PortShape> *ports;
		std::vector<Pin *> pins;
		std::vector<Instance *> children;
	};

	struct Pin {
		Instance *inst;
		Net *net;   // net on the instance's outer side
		Term *term; // boundary into the instance's scope
		uint32_t id;
		uint32_t port;
		int bit;
	};

	struct Net {
		enum class Const : uint8_t {
			None,
			Zero,
			One
		};

		Instance *scope;
		uint32_t id;
		Const constant;
		std::vector<Pin *> pins;   // pins inside the scope on this net
		std::vector<Term *> terms; // boundary terms whose inner net is this
	};

	struct Term {
		Pin *pin;
		Net *net;
		uint32_t id;
	};

	struct NetName {
		std::string wire;
		int index;
		bool scalar;
		bool operator==(const NetName &) const = default;
	};

	struct Alias {
		NetName name;
		Net *net;
	};

	// Leaf port shapes from a consumer with a richer library (liberty)
	struct PortModel {
		virtual ~PortModel();
		virtual bool ports(const Instance &inst, std::vector<PortShape> &out) = 0;
	};

	virtual ~Netlist();

	virtual bool valid() const = 0;

	virtual Instance *top() const = 0;
	bool isTop(const Instance *inst) const;
	// Ports of an instance's master as the host knows them, ignoring PortModel
	virtual bool hostPorts(const Instance *inst, std::vector<PortShape> &out) const = 0;

	virtual const std::vector<Net *> &nets(const Instance *scope) const = 0;
	virtual Net *constNet(const Instance *scope, bool one) const = 0;

	const PortShape &shape(const Pin *pin) const;
	Dir dir(const Pin *pin) const;
	bool scalar(const Pin *pin) const;
	int hdlIndex(const Pin *pin) const;
	bool isDriver(const Pin *pin) const;
};

YOSYS_NAMESPACE_END

#endif
