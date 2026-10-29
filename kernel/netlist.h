// Netlist: the records of a read-only, bit-level, unfolded netlist

#ifndef NETLIST_H
#define NETLIST_H

#include "kernel/yosys_common.h"

#include <cstdint>
#include <string>
#include <vector>

YOSYS_NAMESPACE_BEGIN

struct NetView;

namespace Netlist
{

struct Instance;
struct Pin;
struct Net;
struct Term;

enum class PortDir : uint8_t { Unknown, Input, Output, Inout };

enum class WalkTarget : uint8_t { Drivers, Loads };

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

struct Port {
	std::string name; // unescaped
	int width = 0;
	int from = 0; // [from:to] as declared
	int to = 0;
	PortDir dir = PortDir::Unknown;
	bool vector = false;	     // declared with a range
	bool scalar() const;	     // one bit, declared without a range
	int hdlIndex(int bit) const; // the declared index of a bit
};

struct Instance {
	enum class Kind : uint8_t { Module, LibraryCell, InternalCell };

	std::string name;		  // local name, unescaped
	std::string type;		  // cell type or module name, unescaped
	std::string hdl_type;		  // the source module name before uniquify, else type
	std::vector<std::string> hdlpath; // source path of a flattened cell
	Kind kind;
	uint32_t id;
	Instance *parent;
	const NetView *view; // the owner
	const std::vector<Port> *ports;
	std::vector<Pin *> pins;
	std::vector<Instance *> children;
public:
	bool isTop() const;
	bool isLeaf() const;
	Pin *findPin(const std::string &port, int bit) const;
	std::string localName() const;
};

struct Pin {
	Instance *inst;
	Net *net;   // the net outside, in the scope of the parent
	Term *term; // boundary into the instance's scope
	uint32_t id;
	uint32_t port_index; // in inst->ports
	int bit;
	mutable uint32_t user = 0; // the consumer's value, 0 after each build
public:
	const Port &port() const;
	PortDir dir() const;
	int hdlIndex() const;
	bool isDriver() const;
};

struct Net {
	enum class Const : uint8_t { None, Zero, One };

	Instance *scope;
	uint32_t id;
	Const constant;
	std::vector<Pin *> pins;   // the pins in the scope on this net
	std::vector<Term *> terms; // the inside ends on this net
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
	std::vector<std::string> hdlpath = {}; // source path of a flattened wire
public:
	std::string path() const;
	bool operator==(const NetName &) const = default;
};

struct NetAlias {
	NetName name;
	Net *net;
};

struct OwnedName {
	NetName name;
	Net *net;
	bool canonical;
};

PortDir portDir(bool input, bool output);
std::string joinPath(const std::vector<std::string> &parts);

} // namespace Netlist

YOSYS_NAMESPACE_END

#endif
