from libyosys import *
from scipy.sparse import coo_matrix
from numpy import savetxt

from enum import Enum
class NodeType(Enum):
	GRAPH_CELL = 0
	GRAPH_PI = 1
	GRAPH_PO = 2
	GRAPH_CONST = 3
	GRAPH_WIRE = 4

class NetlistElement:

	def __init__(self, design, module, name):
		self.design = design
		self.module = module
		self.name = name

class Bit(NetlistElement):

	def __init__(self, bit, design, module, node, port, pos):
		super().__init__(design, module, IdString("\\__BIT__"))
		self.bit = bit
		self.node = node
		self.port = port
		self.pos = pos

class Port(NetlistElement):

	def __init__(self, name):
		super().__init__(None, None, name)
		self.input = False
		self.output = False
		self.bits = []

class Node(NetlistElement):

	def __init__(self, design, module, name, nodeType):
		super().__init__(design, module, name)
		self.nodeType = nodeType
		self.ports = []

	def __lt__(self, other):
		if isinstance(other, self.__class):
			if self.type == other.type:
				return self.name.str() < other.name.str()
			return self.type < other.type
		return False

class PyCell(Node):

	def __init__(self, design, module, name, cell):
		super().__init__(design, module, name, NodeType.GRAPH_CELL)
		self.cell = cell

class PyWire(Node):

	def __init__(self, design, module, name):
		super().__init__(design, module, name, NodeType.GRAPH_WIRE)

class NetlistGraph:

	def __init__(self, design, module = None):
		self.design = design
		if module != None:
			self.module = module
		else:
			self.module = list(design.modules_.values())[0]
		self.cells = []
		self.wires = []
		self.nodes = []
		self.node_bits = []
		self.wire_bits = []
		self.node_index = {}
		self.node_bit_index = {}
		self.wire_bit_index = {}

		self.incoming = None
		self.outgoing = None
		self.create()

	def create(self):

		log_header(self.design, "Creating abstract graph representation of "
				+ "module " + self.module.name.str() + "\n")
		log_push()

		sigmap = SigMap(self.module)
		
		log("  Creating const node\n")
		const_node = Node(self.design, self.module, IdString("\\__CONST__"), NodeType.GRAPH_CONST)
		const_port = Port(IdString("\\__CONST__"))
		const_port.input = False
		const_port.output = True
		cb = SigBit(State.Sx)
		const_bit = Bit(cb, self.design, self.module, const_node, const_port, 0)
		const_node.ports.append(const_port)
		const_port.bits.append(const_bit)

		self.nodes.append(const_node)
		self.wires.append(const_node)
		log("  Creating cell nodes\n")

		for cell in self.module.selected_cells():
			c = PyCell(self.design, self.module, cell.name, cell)
			for first, second in cell.connections_.items():
				p = Port(first)
				p.input = cell.input(p.name)
				p.output = cell.output(p.name)
				for bit in sigmap(second).to_sigbit_vector():
					b = Bit(bit, self.design, self.module, c, p, len(p.bits))
					p.bits.append(b)
				c.ports.append(p)

			self.cells.append(c)

		log("  Creating wire nodes\n")

		for wire in self.module.selected_wires():
			node = PyWire(self.design, self.module, wire.name)
			p = Port(IdString(""))
			if wire.port_input:
				node.nodeType = NodeType.GRAPH_PI
				p.name = IdString("\\PI")
				p.input = False
				p.output = True
			elif wire.port_output:
				node.nodeType = NodeType.GRAPH_PO
				p.name = IdString("\\PO")
				p.input = True
				p.output = False
			for bit in sigmap(wire).to_sigbit_set():
				b = Bit(bit, self.design, self.module, node, p, len(p.bits))
				p.bits.append(b)
			node.ports.append(p)
			self.wires.append(node)

		self.nodes.extend(self.cells)
		self.nodes.extend(wire for wire in self.wires if wire.nodeType in [NodeType.GRAPH_PI, NodeType.GRAPH_PO])

		log("  Creating node index for fast lookup\n")

		idx = 0

		for node in self.nodes:
			self.node_index[node.name] = idx
			idx += 1

		log("  Creating node bits (= const + cell + PI + PO)\n")

		for node in self.nodes:
			for port in node.ports:
				for bit in port.bits:
					self.node_bits.append(bit)

		log("  Creating wire bits\n")

		for wire in self.wires:
			for port in wire.ports:
				for bit in port.bits:
					self.wire_bits.append(bit)

		log("  Creating node bit index for fast lookup\n")

		idx = 0

		for bit in self.node_bits:
			self.node_bit_index[bit] = idx
			idx += 1

		log("  Creating wire bit index for fast lookup\n")

		idx = 0

		for bit in self.wire_bits:
			self.wire_bit_index[bit] = idx
			idx += 1

		log("  Mapping port.wire connections to wire bit index\n")

		idx = 0

		wbitmap = {}
		for wbit in self.wire_bits:
			wbitmap[wbit.bit] = idx
			idx += 1

		inputTriplets = []
		outputTriplets = [(0,0,1)]

		log("  Mapping node bits to wire bits\n")

		idx = 0

		for nbit in self.node_bits:
			row = idx
			idx += 1
			col = 0
			val = 1

			def check_wire():
				nonlocal nbit
				try:
					wire = nbit.bit.wire
					return True
				except:
					return False

			if check_wire() and not self.design.selected_member(self.module.name, self.module.wire(nbit.bit.wire.name).name):
				continue

			if check_wire():
				col = wbitmap[nbit.bit]

			triplet = (row, col, val)

			if col == 0 and row != 0:
				inputTriplets.append(triplet)
				continue

			if nbit.node.nodeType == NodeType.GRAPH_CELL:
				cell = nbit.node
				if check_wire() and self.design.selected_member(self.module.name, self.module.wire(nbit.bit.wire.name).name):
					if cell.cell.input(nbit.port.name):
						inputTriplets.append(triplet)
					if cell.cell.output(nbit.port.name):
						outputTriplets.append(triplet)
				continue

			if nbit.node.nodeType == NodeType.GRAPH_PI and self.design.selected_member(self.module.name, self.module.wire(nbit.bit.wire.name).name):
				outputTriplets.append(triplet)
				continue

			if nbit.node.nodeType == NodeType.GRAPH_PO and self.design.selected_member(self.module.name, self.module.wire(nbit.bit.wire.name).name):
				inputTriplets.append(triplet)
				continue

		log("  Creating port-to-wire incidence matrices\n")

		sizeX = len(self.node_bits)
		sizeY= len(self.wire_bits)

		inputRows = [i[0] for i in inputTriplets]
		inputCols = [i[1] for i in inputTriplets]
		inputVals = [i[2] for i in inputTriplets]
		self.incoming = coo_matrix((inputVals, (inputRows, inputCols)), shape=(sizeX, sizeY), dtype='int32')

		outputRows = [i[0] for i in outputTriplets]
		outputCols = [i[1] for i in outputTriplets]
		outputVals = [i[2] for i in outputTriplets]
		self.outgoing = coo_matrix((outputVals, (outputRows, outputCols)), shape=(sizeX, sizeY), dtype='int32')

	def dot(self):
		log_header(self.design, "Creating 'dot' bipartite module graph representation of module " + self.module.name.str() + "\n")
		log_push()
		bitmap = {}

		ss  = "digraph g{\n"
		ss += "  rankdir = LR\n"
		nidx = 0
		pidx = 0
		bidx = 0
		cells_wires = []
		cells_wires.extend(self.cells)
		cells_wires.extend(self.wires)

		idx = 0

		for node in cells_wires:
			for port in node.ports:
				for bit in port.bits:
					bitmap[bit] = idx
					idx += 1
		
		for node in cells_wires:
			ss += "  subgraph cluster" + str(nidx) + " {\n"
			ss += "    style = \"setlinewidth(2)\";\n"
			ss += "    margin = .2;\n"
			ss += "    n" + str(node.name.index_)

			def s_cell():
				nonlocal ss
				ss += "[shape=ellipse,label=\"" + str(nidx) + ":"
				ss += unescape_id(node.cell.type) + "\""
			def s_pi():
				nonlocal ss
				ss += "[shape = box, label=\"" + str(nidx) + ":"
				ss += unescape_id(node.name.str()) + "\""
			def s_po():
				nonlocal ss
				ss += "[shape = diamond, label=\"" + str(nidx) + ":"
				ss += unescape_id(node.name.str()) + "\""
			def s_const():
				nonlocal ss
				ss += "[shape = octagon, label=\"" + str(nidx) + ":CO\""
			def s_wire():
				nonlocal ss
				ss += "[shape = plaintext, label=\"" + str(nidx - len(self.cells)) + ":"
				ss += unescape_id(node.name.str()) + "\""
			switch = {
					NodeType.GRAPH_CELL : s_cell,
					NodeType.GRAPH_PI : s_pi,
					NodeType.GRAPH_PO : s_po,
					NodeType.GRAPH_CONST : s_const,
					NodeType.GRAPH_WIRE : s_wire
					}
			switch[node.nodeType]()

			ss += "];\n"

			pidx = 0
			for port in node.ports:
				ss += "    port_" + str(node.name.index_) + "_" + str(port.name.index_)
				ss += "[shape=none,label=<\n"
				ss += "      <table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\" >\n"
				ss += "        <tr><td bgcolor=\"lightgray\" port=\"p" + str(node.name.index_) + "_"
				ss += str(port.name.index_) + "\"> "
				ss += unescape_id(port.name.str())
				ss += "</td></tr>\n"
	
				bidx = 0;
				for bit in port.bits:

					ss += "          <tr><td bgcolor=\"white\" port=\"b" + str(node.name.index_) + "_" + str(port.name.index_) + "_" + str(bit.pos) + "\"> " + str(bitmap[bit]) + ":"  + str(bidx) + "</td></tr>\n"

					bidx += 1

				ss += "      </table>\n    >];\n"

				if node.nodeType == NodeType.GRAPH_CELL:
					if node.cell.output(port.name):
						ss += "    n" + str(node.name.index_) + " -> " + "port_" + str(node.name.index_) + "_" + str(port.name.index_) + ":p" + str(node.name.index_) + "_" + str(port.name.index_) + ";\n"
					else:
						ss += "    port_" + str(node.name.index_) + "_" + str(port.name.index_) + ":p" + str(node.name.index_) + "_" + str(port.name.index_) + " -> " + "n" + str(node.name.index_) +  ";\n"
				if node.nodeType == NodeType.GRAPH_PI or node.nodeType == NodeType.GRAPH_CONST:
					ss += "    n" + str(node.name.index_) + " -> " + "port_" + str(node.name.index_) + "_" + str(port.name.index_) + ":p" + str(node.name.index_) + "_" + str(port.name.index_) + ";\n"
				if node.nodeType == NodeType.GRAPH_PO:
					ss += "    port_" + str(node.name.index_) + "_" + str(port.name.index_) + ":p" + str(node.name.index_) + "_" + str(port.name.index_) + " -> " + "n" + str(node.name.index_) +  ";\n"

				pidx += 1
			ss += "  }\n"
			nidx += 1

		for i in range(len(self.incoming.nonzero()[0])):
			b1 = self.node_bits[self.incoming.nonzero()[0][i]]
			b2 = self.wire_bits[self.incoming.nonzero()[1][i]]

			if b1.node.nodeType == NodeType.GRAPH_PO or b1.node.nodeType == NodeType.GRAPH_CONST:
				continue

			ss += "  "
			ss += "port_" + str(b2.node.name.index_) + "_" + str(b2.port.name.index_) + ":"
			ss += "b" + str(b2.node.name.index_) + "_" + str(b2.port.name.index_) + "_" + str(b2.pos)
			ss += " -> "
			ss += "port_" + str(b1.node.name.index_) + "_" + str(b1.port.name.index_) + ":"
			ss += "b" + str(b1.node.name.index_) + "_" + str(b1.port.name.index_) + "_" + str(b1.pos)
			ss += ";\n"

		for i in range(len(self.outgoing.nonzero()[0])):
			b1 = self.node_bits[self.outgoing.nonzero()[0][i]]
			b2 = self.wire_bits[self.outgoing.nonzero()[1][i]]

			if b1.node.nodeType == NodeType.GRAPH_PI:
				continue

			ss += "  "
			ss += "port_" + str(b1.node.name.index_) + "_" + str(b1.port.name.index_) + ":"
			ss += "b" + str(b1.node.name.index_) + "_" + str(b1.port.name.index_) + "_" + str(b1.pos)
			ss += " -> "
			ss += "port_" + str(b2.node.name.index_) + "_" + str(b2.port.name.index_) + ":"
			ss += "b" + str(b2.node.name.index_) + "_" + str(b2.port.name.index_) + "_" + str(b2.pos)
			ss += ";\n"

		ss += "}\n"

		log_pop()

		return ss

	def save_dot(self, filename):
		savetxt(filename, [self.dot()], fmt="%s")

	def save_incoming(self, filename, delimiter = ","):
		savetxt(filename, self.incoming.todense(), "%d", delimiter=delimiter)

	def save_outgoing(self, filename, delimiter = ","):
		savetxt(filename, self.outgoing.todense(), "%d", delimiter=delimiter)

	def save_adjacency(self, filename, delimiter = ","):
		savetxt(filename, (self.outgoing*self.incoming.transpose()).todense(), "%d", delimiter=delimiter)

p = None

class NetlistGraphPass(Pass):

	def __init__(self):
		super().__init__("netlist_graph", "Generates the Netlist-Graph of a module")

		import argparse
		self.parser = argparse.ArgumentParser()

		self.parser.add_argument("-mod", nargs=1, metavar="MOD", help="The Netlist-Graph of the module with the id-string <module> will be generated. If this argument is not given, the first module will be used")
		self.parser.add_argument("-dot", nargs=1, metavar="FILE", help="Write the Netlist-Graph to FILE in dot format")
		self.parser.add_argument("-i","-incoming", nargs=1, metavar="FILE", help="Write the incoming incidence matrix to FILE in csv format")
		self.parser.add_argument("-o","-outgoing", nargs=1, metavar="FILE", help="Write the outgoing incidence matrix to FILE in csv format")
		self.parser.add_argument("-a","-adjacency", nargs=1, metavar="FILE", help="Write the adjacency matrix to FILE in csv format")

	def py_help(self):

		log("This pass generates the Netlist-Graph of a module\n")
		log(self.parser.format_help())

	def py_execute(self, args, des):

		args = self.parser.parse_args(args[1:])

		graph = None
		if args.mod:
			try:
				graph = NetlistGraph(des, des.modules_[IdString(args.mod[0])])
			except KeyError:
				log("Module \"" + args.mod[0] + "\" not found!\n")
				exit()
		else:
			graph = NetlistGraph(des, list(des.modules_.values())[0])

		if args.dot:
			graph.save_dot(args.dot[0])

		if args.i:
			graph.save_incoming(args.i[0])

		if args.o:
			graph.save_outgoing(args.o[0])

		if args.a:
			graph.save_adjacency(args.a[0])
	
	def py_clear_flags(self):
		log("Clear\n")

if __name__ == "__main__":

	designs = {}
	graphs = {}

	testdir = "../../tests/simple/"

	import os
	for testcase in os.listdir(testdir):
		if not testcase.endswith(".v"):
			continue
		designs[testcase] = Design()
		run_pass("read_verilog " + testdir + testcase, designs[testcase])
		run_pass("hierarchy -check -auto-top", designs[testcase])
		run_pass("proc", designs[testcase])
		run_pass("clean", designs[testcase])
		run_pass("memory", designs[testcase])
		run_pass("clean", designs[testcase])
		run_pass("opt -full", designs[testcase])
		run_pass("clean", designs[testcase])
		graphs[testcase] = NetlistGraph(designs[testcase])

		file_prefix = "out/" + testcase
		graphs[testcase].save_dot(file_prefix + ".dot")
		graphs[testcase].save_incoming(file_prefix + "_in.csv")
		graphs[testcase].save_outgoing(file_prefix + "_out.csv")
		graphs[testcase].save_adjacency(file_prefix + "_adjacency.csv")

else:
	p = NetlistGraphPass()
