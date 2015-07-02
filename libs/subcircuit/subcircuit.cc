/*
 *  SubCircuit -- An implementation of the Ullmann Subgraph Isomorphism
 *                algorithm for coarse grain logic networks
 *
 *  Copyright (C) 2013  Clifford Wolf <clifford@clifford.at>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "subcircuit.h"

#include <algorithm>
#include <assert.h>
#include <stdarg.h>
#include <stdio.h>

#ifdef _YOSYS_
#  include "kernel/yosys.h"
#  define my_printf YOSYS_NAMESPACE_PREFIX log
#else
#  define my_printf printf
#endif

using namespace SubCircuit;

#ifndef _YOSYS_
static std::string my_stringf(const char *fmt, ...)
{
	std::string string;
	char *str = NULL;
	va_list ap;

	va_start(ap, fmt);
	if (vasprintf(&str, fmt, ap) < 0)
		str = NULL;
	va_end(ap);

	if (str != NULL) {
		string = str;
		free(str);
	}

	return string;
}
#else
#  define my_stringf YOSYS_NAMESPACE_PREFIX stringf
#endif

SubCircuit::Graph::Graph(const Graph &other, const std::vector<std::string> &otherNodes)
{
	allExtern = other.allExtern;

	std::map<int, int> other2this;
	for (int i = 0; i < int(otherNodes.size()); i++) {
		assert(other.nodeMap.count(otherNodes[i]) > 0);
		other2this[other.nodeMap.at(otherNodes[i])] = i;
		nodeMap[otherNodes[i]] = i;
	}

	std::map<int, int> edges2this;
	for (auto &i1 : other2this)
	for (auto &i2 : other.nodes[i1.first].ports)
	for (auto &i3 : i2.bits)
		if (edges2this.count(i3.edgeIdx) == 0) {
			int next_idx = edges2this.size();
			edges2this[i3.edgeIdx] = next_idx;
		}

	edges.resize(edges2this.size());
	for (auto &it : edges2this) {
		for (auto &bit : other.edges[it.first].portBits)
			if (other2this.count(bit.nodeIdx) > 0)
				edges[it.second].portBits.insert(BitRef(other2this[bit.nodeIdx], bit.portIdx, bit.bitIdx));
		edges[it.second].constValue = other.edges[it.first].constValue;
		edges[it.second].isExtern = other.edges[it.first].isExtern;
	}

	nodes.resize(other2this.size());
	for (auto &it : other2this) {
		nodes[it.second] = other.nodes[it.first];
		for (auto &i2 : nodes[it.second].ports)
		for (auto &i3 : i2.bits)
			i3.edgeIdx = edges2this.at(i3.edgeIdx);
	}
}

bool SubCircuit::Graph::BitRef::operator < (const BitRef &other) const
{
	if (nodeIdx != other.nodeIdx)
		return nodeIdx < other.nodeIdx;
	if (portIdx != other.portIdx)
		return portIdx < other.portIdx;
	return bitIdx < other.bitIdx;
}

void  SubCircuit::Graph::createNode(std::string nodeId, std::string typeId, void *userData, bool shared)
{
	assert(nodeMap.count(nodeId) == 0);
	nodeMap[nodeId] = nodes.size();
	nodes.push_back(Node());

	Node &newNode = nodes.back();
	newNode.nodeId = nodeId;
	newNode.typeId = typeId;
	newNode.userData = userData;
	newNode.shared = shared;
}

void SubCircuit::Graph::createPort(std::string nodeId, std::string portId, int width, int minWidth)
{
	assert(nodeMap.count(nodeId) != 0);
	int nodeIdx = nodeMap[nodeId];
	Node &node = nodes[nodeIdx];

	assert(node.portMap.count(portId) == 0);

	int portIdx = node.ports.size();
	node.portMap[portId] = portIdx;
	node.ports.push_back(Port());
	Port &port = node.ports.back();

	port.portId = portId;
	port.minWidth = minWidth < 0 ? width : minWidth;
	port.bits.insert(port.bits.end(), width, PortBit());

	for (int i = 0; i < width; i++) {
		port.bits[i].edgeIdx = edges.size();
		edges.push_back(Edge());
		edges.back().portBits.insert(BitRef(nodeIdx, portIdx, i));
	}
}

void SubCircuit::Graph::createConnection(std::string fromNodeId, std::string fromPortId, int fromBit, std::string toNodeId, std::string toPortId, int toBit, int width)
{
	assert(nodeMap.count(fromNodeId) != 0);
	assert(nodeMap.count(toNodeId) != 0);

	int fromNodeIdx = nodeMap[fromNodeId];
	Node &fromNode = nodes[fromNodeIdx];

	int toNodeIdx = nodeMap[toNodeId];
	Node &toNode = nodes[toNodeIdx];

	assert(fromNode.portMap.count(fromPortId) != 0);
	assert(toNode.portMap.count(toPortId) != 0);

	int fromPortIdx = fromNode.portMap[fromPortId];
	Port &fromPort = fromNode.ports[fromPortIdx];

	int toPortIdx = toNode.portMap[toPortId];
	Port &toPort = toNode.ports[toPortIdx];

	if (width < 0) {
		assert(fromBit == 0 && toBit == 0);
		assert(fromPort.bits.size() == toPort.bits.size());
		width = fromPort.bits.size();
	}

	assert(fromBit >= 0 && toBit >= 0);
	for (int i = 0; i < width; i++)
	{
		assert(fromBit + i < int(fromPort.bits.size()));
		assert(toBit + i < int(toPort.bits.size()));

		int fromEdgeIdx = fromPort.bits[fromBit + i].edgeIdx;
		int toEdgeIdx = toPort.bits[toBit + i].edgeIdx;

		if (fromEdgeIdx == toEdgeIdx)
			continue;

		// merge toEdge into fromEdge
		if (edges[toEdgeIdx].isExtern)
			edges[fromEdgeIdx].isExtern = true;
		if (edges[toEdgeIdx].constValue) {
			assert(edges[fromEdgeIdx].constValue == 0);
			edges[fromEdgeIdx].constValue = edges[toEdgeIdx].constValue;
		}
		for (const auto &ref : edges[toEdgeIdx].portBits) {
			edges[fromEdgeIdx].portBits.insert(ref);
			nodes[ref.nodeIdx].ports[ref.portIdx].bits[ref.bitIdx].edgeIdx = fromEdgeIdx;
		}

		// remove toEdge (move last edge over toEdge if needed)
		if (toEdgeIdx+1 != int(edges.size())) {
			edges[toEdgeIdx] = edges.back();
			for (const auto &ref : edges[toEdgeIdx].portBits)
				nodes[ref.nodeIdx].ports[ref.portIdx].bits[ref.bitIdx].edgeIdx = toEdgeIdx;
		}
		edges.pop_back();
	}
}

void SubCircuit::Graph::createConnection(std::string fromNodeId, std::string fromPortId, std::string toNodeId, std::string toPortId)
{
	createConnection(fromNodeId, fromPortId, 0, toNodeId, toPortId, 0, -1);
}

void SubCircuit::Graph::createConstant(std::string toNodeId, std::string toPortId, int toBit, int constValue)
{
	assert(nodeMap.count(toNodeId) != 0);
	int toNodeIdx = nodeMap[toNodeId];
	Node &toNode = nodes[toNodeIdx];

	assert(toNode.portMap.count(toPortId) != 0);
	int toPortIdx = toNode.portMap[toPortId];
	Port &toPort = toNode.ports[toPortIdx];

	assert(toBit >= 0 && toBit < int(toPort.bits.size()));
	int toEdgeIdx = toPort.bits[toBit].edgeIdx;

	assert(edges[toEdgeIdx].constValue == 0);
	edges[toEdgeIdx].constValue = constValue;
}

void SubCircuit::Graph::createConstant(std::string toNodeId, std::string toPortId, int constValue)
{
	assert(nodeMap.count(toNodeId) != 0);
	int toNodeIdx = nodeMap[toNodeId];
	Node &toNode = nodes[toNodeIdx];

	assert(toNode.portMap.count(toPortId) != 0);
	int toPortIdx = toNode.portMap[toPortId];
	Port &toPort = toNode.ports[toPortIdx];

	for (int i = 0; i < int(toPort.bits.size()); i++) {
		int toEdgeIdx = toPort.bits[i].edgeIdx;
		assert(edges[toEdgeIdx].constValue == 0);
		edges[toEdgeIdx].constValue = constValue % 2 ? '1' : '0';
		constValue = constValue >> 1;
	}
}

void SubCircuit::Graph::markExtern(std::string nodeId, std::string portId, int bit)
{
	assert(nodeMap.count(nodeId) != 0);
	Node &node = nodes[nodeMap[nodeId]];

	assert(node.portMap.count(portId) != 0);
	Port &port = node.ports[node.portMap[portId]];

	if (bit < 0) {
		for (const auto portBit : port.bits)
			edges[portBit.edgeIdx].isExtern = true;
	} else {
		assert(bit < int(port.bits.size()));
		edges[port.bits[bit].edgeIdx].isExtern = true;
	}
}

void SubCircuit::Graph::markAllExtern()
{
	allExtern = true;
}

void SubCircuit::Graph::print()
{
	for (int i = 0; i < int(nodes.size()); i++) {
		const Node &node = nodes[i];
		my_printf("NODE %d: %s (%s)\n", i, node.nodeId.c_str(), node.typeId.c_str());
		for (int j = 0; j < int(node.ports.size()); j++) {
			const Port &port = node.ports[j];
			my_printf("  PORT %d: %s (%d/%d)\n", j, port.portId.c_str(), port.minWidth, int(port.bits.size()));
			for (int k = 0; k < int(port.bits.size()); k++) {
				int edgeIdx = port.bits[k].edgeIdx;
				my_printf("    BIT %d (%d):", k, edgeIdx);
				for (const auto &ref : edges[edgeIdx].portBits)
					my_printf(" %d.%d.%d", ref.nodeIdx, ref.portIdx, ref.bitIdx);
				if (edges[edgeIdx].isExtern)
					my_printf(" [extern]");
				my_printf("\n");
			}
		}
	}
}

class SubCircuit::SolverWorker
{
	// basic internal data structures

	typedef std::vector<std::map<int, int>> adjMatrix_t;

	struct GraphData {
		std::string graphId;
		Graph graph;
		adjMatrix_t adjMatrix;
		std::vector<bool> usedNodes;
	};

	static void printAdjMatrix(const adjMatrix_t &matrix)
	{
		my_printf("%7s", "");
		for (int i = 0; i < int(matrix.size()); i++)
			my_printf("%4d:", i);
		my_printf("\n");
		for (int i = 0; i < int(matrix.size()); i++) {
			my_printf("%5d:", i);
			for (int j = 0; j < int(matrix.size()); j++)
				if (matrix.at(i).count(j) == 0)
					my_printf("%5s", "-");
				else
					my_printf("%5d", matrix.at(i).at(j));
			my_printf("\n");
		}
	}

	// helper functions for handling permutations

	static const int maxPermutationsLimit = 1000000;

	static int numberOfPermutations(const std::vector<std::string> &list)
	{
		int numPermutations = 1;
		for (int i = 0; i < int(list.size()); i++) {
			assert(numPermutations < maxPermutationsLimit);
			numPermutations *= i+1;
		}
		return numPermutations;
	}

	static void permutateVectorToMap(std::map<std::string, std::string> &map, const std::vector<std::string> &list, int idx)
	{
		// convert idx to a list.size() digits factoradic number

		std::vector<int> factoradicDigits;
		for (int i = 0; i < int(list.size()); i++) {
			factoradicDigits.push_back(idx % (i+1));
			idx = idx / (i+1);
		}

		// construct permutation

		std::vector<std::string> pool = list;
		std::vector<std::string> permutation;

		while (!factoradicDigits.empty()) {
			int i = factoradicDigits.back();
			factoradicDigits.pop_back();
			permutation.push_back(pool[i]);
			pool.erase(pool.begin() + i);
		}

		// update map

		for (int i = 0; i < int(list.size()); i++)
			map[list[i]] = permutation[i];
	}

	static int numberOfPermutationsArray(const std::vector<std::vector<std::string>> &list)
	{
		int numPermutations = 1;
		for (const auto &it : list) {
			int thisPermutations = numberOfPermutations(it);
			assert(float(numPermutations) * float(thisPermutations) < maxPermutationsLimit);
			numPermutations *= thisPermutations;
		}
		return numPermutations;
	}

	static void permutateVectorToMapArray(std::map<std::string, std::string> &map, const std::vector<std::vector<std::string>> &list, int idx)
	{
		for (const auto &it : list) {
			int thisPermutations = numberOfPermutations(it);
			int thisIdx = idx % thisPermutations;
			permutateVectorToMap(map, it, thisIdx);
			idx /= thisPermutations;
		}
	}

	static void applyPermutation(std::map<std::string, std::string> &map, const std::map<std::string, std::string> &permutation)
	{
		std::vector<std::pair<std::string, std::string>> changeLog;
		for (const auto &it : permutation)
			if (map.count(it.second))
				changeLog.push_back(std::pair<std::string, std::string>(it.first, map.at(it.second)));
			else
				changeLog.push_back(std::pair<std::string, std::string>(it.first, it.second));
		for (const auto &it : changeLog)
			map[it.first] = it.second;
	}

	// classes for internal digraph representation

	struct DiBit
	{
		std::string fromPort, toPort;
		int fromBit, toBit;

		DiBit() : fromPort(), toPort(), fromBit(-1), toBit(-1) { }
		DiBit(std::string fromPort, int fromBit, std::string toPort, int toBit) : fromPort(fromPort), toPort(toPort), fromBit(fromBit), toBit(toBit) { }

		bool operator < (const DiBit &other) const
		{
			if (fromPort != other.fromPort)
				return fromPort < other.fromPort;
			if (toPort != other.toPort)
				return toPort < other.toPort;
			if (fromBit != other.fromBit)
				return fromBit < other.fromBit;
			return toBit < other.toBit;
		}

		std::string toString() const
		{
			return my_stringf("%s[%d]:%s[%d]", fromPort.c_str(), fromBit, toPort.c_str(), toBit);
		}
	};

	struct DiNode
	{
		std::string typeId;
		std::map<std::string, int> portSizes;

		DiNode()
		{
		}

		DiNode(const Graph &graph, int nodeIdx)
		{
			const Graph::Node &node = graph.nodes.at(nodeIdx);
			typeId = node.typeId;
			for (const auto &port : node.ports)
				portSizes[port.portId] = port.bits.size();
		}

		bool operator < (const DiNode &other) const
		{
			if (typeId != other.typeId)
				return typeId < other.typeId;
			return portSizes < other.portSizes;
		}

		std::string toString() const
		{
			std::string str;
			bool firstPort = true;
			for (const auto &it : portSizes) {
				str += my_stringf("%s%s[%d]", firstPort ? "" : ",", it.first.c_str(), it.second);
				firstPort = false;
			}
			return typeId + "(" + str + ")";
		}
	};

	struct DiEdge
	{
		DiNode fromNode, toNode;
		std::set<DiBit> bits;
		std::string userAnnotation;

		bool operator < (const DiEdge &other) const
		{
			if (fromNode < other.fromNode || other.fromNode < fromNode)
				return fromNode < other.fromNode;
			if (toNode < other.toNode || other.toNode < toNode)
				return toNode < other.toNode;
			if (bits < other.bits || other.bits < bits)
				return bits < other.bits;
			return userAnnotation < other.userAnnotation;
		}

		bool compare(const DiEdge &other, const std::map<std::string, std::string> &mapFromPorts, const std::map<std::string, std::string> &mapToPorts) const
		{
			// Rules for matching edges:
			//
			// For all bits in the needle edge:
			//   - ignore if needle ports don't exist in haystack edge
			//   - otherwise: matching bit in haystack edge must exist
			//
			// There is no need to check in the other direction, as checking
			// of the isExtern properties is already performed in node matching.
			//
			// Note: "this" is needle, "other" is haystack

			for (auto bit : bits)
			{
				if (mapFromPorts.count(bit.fromPort) > 0)
					bit.fromPort = mapFromPorts.at(bit.fromPort);
				if (mapToPorts.count(bit.toPort) > 0)
					bit.toPort = mapToPorts.at(bit.toPort);

				if (other.fromNode.portSizes.count(bit.fromPort) == 0)
					continue;
				if (other.toNode.portSizes.count(bit.toPort) == 0)
					continue;

				if (bit.fromBit >= other.fromNode.portSizes.at(bit.fromPort))
					continue;
				if (bit.toBit >= other.toNode.portSizes.at(bit.toPort))
					continue;

				if (other.bits.count(bit) == 0)
					return false;
			}

			return true;
		}

		bool compareWithFromAndToPermutations(const DiEdge &other, const std::map<std::string, std::string> &mapFromPorts, const std::map<std::string, std::string> &mapToPorts,
				const std::map<std::string, std::set<std::map<std::string, std::string>>> &swapPermutations) const
		{
			if (swapPermutations.count(fromNode.typeId) > 0)
				for (const auto &permutation : swapPermutations.at(fromNode.typeId)) {
					std::map<std::string, std::string> thisMapFromPorts = mapFromPorts;
					applyPermutation(thisMapFromPorts, permutation);
					if (compareWithToPermutations(other, thisMapFromPorts, mapToPorts, swapPermutations))
						return true;
				}
			return compareWithToPermutations(other, mapFromPorts, mapToPorts, swapPermutations);
		}

		bool compareWithToPermutations(const DiEdge &other, const std::map<std::string, std::string> &mapFromPorts, const std::map<std::string, std::string> &mapToPorts,
				const std::map<std::string, std::set<std::map<std::string, std::string>>> &swapPermutations) const
		{
			if (swapPermutations.count(toNode.typeId) > 0)
				for (const auto &permutation : swapPermutations.at(toNode.typeId)) {
					std::map<std::string, std::string> thisMapToPorts = mapToPorts;
					applyPermutation(thisMapToPorts, permutation);
					if (compare(other, mapFromPorts, thisMapToPorts))
						return true;
				}
			return compare(other, mapFromPorts, mapToPorts);
		}

		bool compare(const DiEdge &other, const std::map<std::string, std::set<std::set<std::string>>> &swapPorts,
				const std::map<std::string, std::set<std::map<std::string, std::string>>> &swapPermutations) const
		{
			// brute force method for port swapping: try all variations

			std::vector<std::vector<std::string>> swapFromPorts;
			std::vector<std::vector<std::string>> swapToPorts;

			// only use groups that are relevant for this edge

			if (swapPorts.count(fromNode.typeId) > 0)
				for (const auto &ports : swapPorts.at(fromNode.typeId)) {
					for (const auto &bit : bits)
						if (ports.count(bit.fromPort))
							goto foundFromPortMatch;
					if (0) {
				foundFromPortMatch:
						std::vector<std::string> portsVector;
						for (const auto &port : ports)
							portsVector.push_back(port);
						swapFromPorts.push_back(portsVector);
					}
				}

			if (swapPorts.count(toNode.typeId) > 0)
				for (const auto &ports : swapPorts.at(toNode.typeId)) {
					for (const auto &bit : bits)
						if (ports.count(bit.toPort))
							goto foundToPortMatch;
					if (0) {
				foundToPortMatch:
						std::vector<std::string> portsVector;
						for (const auto &port : ports)
							portsVector.push_back(port);
						swapToPorts.push_back(portsVector);
					}
				}

			// try all permutations

			std::map<std::string, std::string> mapFromPorts, mapToPorts;
			int fromPortsPermutations = numberOfPermutationsArray(swapFromPorts);
			int toPortsPermutations = numberOfPermutationsArray(swapToPorts);

			for (int i = 0; i < fromPortsPermutations; i++)
			{
				permutateVectorToMapArray(mapFromPorts, swapFromPorts, i);

				for (int j = 0; j < toPortsPermutations; j++) {
					permutateVectorToMapArray(mapToPorts, swapToPorts, j);
					if (compareWithFromAndToPermutations(other, mapFromPorts, mapToPorts, swapPermutations))
						return true;
				}
			}

			return false;
		}

		bool compare(const DiEdge &other, const std::map<std::string, std::string> &mapFromPorts, const std::map<std::string, std::set<std::set<std::string>>> &swapPorts,
				const std::map<std::string, std::set<std::map<std::string, std::string>>> &swapPermutations) const
		{
			// strip-down version of the last function: only try permutations for mapToPorts, mapFromPorts is already provided by the caller

			std::vector<std::vector<std::string>> swapToPorts;

			if (swapPorts.count(toNode.typeId) > 0)
				for (const auto &ports : swapPorts.at(toNode.typeId)) {
					for (const auto &bit : bits)
						if (ports.count(bit.toPort))
							goto foundToPortMatch;
					if (0) {
				foundToPortMatch:
						std::vector<std::string> portsVector;
						for (const auto &port : ports)
							portsVector.push_back(port);
						swapToPorts.push_back(portsVector);
					}
				}

			std::map<std::string, std::string> mapToPorts;
			int toPortsPermutations = numberOfPermutationsArray(swapToPorts);

			for (int j = 0; j < toPortsPermutations; j++) {
				permutateVectorToMapArray(mapToPorts, swapToPorts, j);
				if (compareWithToPermutations(other, mapFromPorts, mapToPorts, swapPermutations))
					return true;
			}

			return false;
		}

		std::string toString() const
		{
			std::string buffer = fromNode.toString() + " " + toNode.toString();
			for (const auto &bit : bits)
				buffer += " " + bit.toString();
			if (!userAnnotation.empty())
				buffer += " " + userAnnotation;
			return buffer;
		}

		static void findEdgesInGraph(const Graph &graph, std::map<std::pair<int, int>, DiEdge> &edges)
		{
			edges.clear();
			for (const auto &edge : graph.edges) {
				if (edge.constValue != 0)
					continue;
				for (const auto &fromBit : edge.portBits)
				for (const auto &toBit : edge.portBits)
					if (&fromBit != &toBit) {
						DiEdge &de = edges[std::pair<int, int>(fromBit.nodeIdx, toBit.nodeIdx)];
						de.fromNode = DiNode(graph, fromBit.nodeIdx);
						de.toNode = DiNode(graph, toBit.nodeIdx);
						std::string fromPortId = graph.nodes[fromBit.nodeIdx].ports[fromBit.portIdx].portId;
						std::string toPortId = graph.nodes[toBit.nodeIdx].ports[toBit.portIdx].portId;
						de.bits.insert(DiBit(fromPortId, fromBit.bitIdx, toPortId, toBit.bitIdx));
					}
			}
		}
	};

	struct DiCache
	{
		std::map<DiEdge, int> edgeTypesMap;
		std::vector<DiEdge> edgeTypes;
		std::map<std::pair<int, int>, bool> compareCache;

		void add(const Graph &graph, adjMatrix_t &adjMatrix, const std::string &graphId, Solver *userSolver)
		{
			std::map<std::pair<int, int>, DiEdge> edges;
			DiEdge::findEdgesInGraph(graph, edges);

			adjMatrix.clear();
			adjMatrix.resize(graph.nodes.size());

			for (auto &it : edges) {
				const Graph::Node &fromNode = graph.nodes[it.first.first];
				const Graph::Node &toNode = graph.nodes[it.first.second];
				it.second.userAnnotation = userSolver->userAnnotateEdge(graphId, fromNode.nodeId, fromNode.userData, toNode.nodeId, toNode.userData);
			}

			for (const auto &it : edges) {
				if (edgeTypesMap.count(it.second) == 0) {
					edgeTypesMap[it.second] = edgeTypes.size();
					edgeTypes.push_back(it.second);
				}
				adjMatrix[it.first.first][it.first.second] = edgeTypesMap[it.second];
			}
		}

		bool compare(int needleEdge, int haystackEdge, const std::map<std::string, std::set<std::set<std::string>>> &swapPorts,
				const std::map<std::string, std::set<std::map<std::string, std::string>>> &swapPermutations)
		{
			std::pair<int, int> key(needleEdge, haystackEdge);
			if (!compareCache.count(key))
				compareCache[key] = edgeTypes.at(needleEdge).compare(edgeTypes.at(haystackEdge), swapPorts, swapPermutations);
			return compareCache[key];
		}

		bool compare(int needleEdge, int haystackEdge, const std::map<std::string, std::string> &mapFromPorts, const std::map<std::string, std::set<std::set<std::string>>> &swapPorts,
				const std::map<std::string, std::set<std::map<std::string, std::string>>> &swapPermutations) const
		{
			return edgeTypes.at(needleEdge).compare(edgeTypes.at(haystackEdge), mapFromPorts, swapPorts, swapPermutations);
		}

		bool compare(int needleEdge, int haystackEdge, const std::map<std::string, std::string> &mapFromPorts, const std::map<std::string, std::string> &mapToPorts) const
		{
			return edgeTypes.at(needleEdge).compare(edgeTypes.at(haystackEdge), mapFromPorts, mapToPorts);
		}

		void printEdgeTypes() const
		{
			for (int i = 0; i < int(edgeTypes.size()); i++)
				my_printf("%5d: %s\n", i, edgeTypes[i].toString().c_str());
		}
	};

	// solver state variables

	Solver *userSolver;
	std::map<std::string, GraphData> graphData;
	std::map<std::string, std::set<std::string>> compatibleTypes;
	std::map<int, std::set<int>> compatibleConstants;
	std::map<std::string, std::set<std::set<std::string>>> swapPorts;
	std::map<std::string, std::set<std::map<std::string, std::string>>> swapPermutations;
	DiCache diCache;
	bool verbose;

	// main solver functions

	bool matchNodePorts(const Graph &needle, int needleNodeIdx, const Graph &haystack, int haystackNodeIdx, const std::map<std::string, std::string> &swaps) const
	{
		const Graph::Node &nn = needle.nodes[needleNodeIdx];
		const Graph::Node &hn = haystack.nodes[haystackNodeIdx];
		assert(nn.ports.size() == hn.ports.size());

		for (int i = 0; i < int(nn.ports.size()); i++)
		{
			std::string hnPortId = nn.ports[i].portId;
			if (swaps.count(hnPortId) > 0)
				hnPortId = swaps.at(hnPortId);

			if (hn.portMap.count(hnPortId) == 0)
				return false;

			const Graph::Port &np = nn.ports[i];
			const Graph::Port &hp = hn.ports[hn.portMap.at(hnPortId)];

			if (int(hp.bits.size()) < np.minWidth || hp.bits.size() > np.bits.size())
				return false;

			for (int j = 0; j < int(hp.bits.size()); j++)
			{
				const Graph::Edge &ne = needle.edges[np.bits[j].edgeIdx];
				const Graph::Edge &he = haystack.edges[hp.bits[j].edgeIdx];

				if (ne.constValue || he.constValue) {
					if (ne.constValue != he.constValue)
						if (compatibleConstants.count(ne.constValue) == 0 || compatibleConstants.at(ne.constValue).count(he.constValue) == 0)
							return false;
					continue;
				}

				if (ne.isExtern || needle.allExtern) {
					if (he.portBits.size() < ne.portBits.size())
						return false;
				} else {
					if (he.portBits.size() != ne.portBits.size())
						return false;
					if (he.isExtern || haystack.allExtern)
						return false;
				}
			}
		}

		return true;
	}

	bool matchNodes(const GraphData &needle, int needleNodeIdx, const GraphData &haystack, int haystackNodeIdx) const
	{
		// Rules for matching nodes:
		//
		// 1. their typeId must be identical or compatible
		//    (this is checked before calling this function)
		//
		// 2. they must have the same ports and the haystack port
		//    widths must match the needle port width range
		//
		// 3. All edges from the needle must match the haystack:
		//    a) if the needle edge is extern:
		//         - the haystack edge must have at least as many components as the needle edge
		//    b) if the needle edge is not extern:
		//         - the haystack edge must have the same number of components as the needle edge
		//         - the haystack edge must not be extern

		const Graph::Node &nn = needle.graph.nodes[needleNodeIdx];
		const Graph::Node &hn = haystack.graph.nodes[haystackNodeIdx];

		assert(nn.typeId == hn.typeId || (compatibleTypes.count(nn.typeId) > 0 && compatibleTypes.at(nn.typeId).count(hn.typeId) > 0));

		if (nn.ports.size() != hn.ports.size())
			return false;

		std::map<std::string, std::string> currentCandidate;

		for (const auto &port : needle.graph.nodes[needleNodeIdx].ports)
			currentCandidate[port.portId] = port.portId;

		if (swapPorts.count(needle.graph.nodes[needleNodeIdx].typeId) == 0)
		{
			if (matchNodePorts(needle.graph, needleNodeIdx, haystack.graph, haystackNodeIdx, currentCandidate) &&
					userSolver->userCompareNodes(needle.graphId, nn.nodeId, nn.userData, haystack.graphId, hn.nodeId, hn.userData, currentCandidate))
				return true;

			if (swapPermutations.count(needle.graph.nodes[needleNodeIdx].typeId) > 0)
				for (const auto &permutation : swapPermutations.at(needle.graph.nodes[needleNodeIdx].typeId)) {
					std::map<std::string, std::string> currentSubCandidate = currentCandidate;
					applyPermutation(currentSubCandidate, permutation);
					if (matchNodePorts(needle.graph, needleNodeIdx, haystack.graph, haystackNodeIdx, currentCandidate) &&
							userSolver->userCompareNodes(needle.graphId, nn.nodeId, nn.userData, haystack.graphId, hn.nodeId, hn.userData, currentCandidate))
						return true;
				}
		}
		else
		{
			std::vector<std::vector<std::string>> thisSwapPorts;
			for (const auto &ports : swapPorts.at(needle.graph.nodes[needleNodeIdx].typeId)) {
				std::vector<std::string> portsVector;
				for (const auto &port : ports)
					portsVector.push_back(port);
				thisSwapPorts.push_back(portsVector);
			}

			int thisPermutations = numberOfPermutationsArray(thisSwapPorts);
			for (int i = 0; i < thisPermutations; i++)
			{
				permutateVectorToMapArray(currentCandidate, thisSwapPorts, i);

				if (matchNodePorts(needle.graph, needleNodeIdx, haystack.graph, haystackNodeIdx, currentCandidate) &&
						userSolver->userCompareNodes(needle.graphId, nn.nodeId, nn.userData, haystack.graphId, hn.nodeId, hn.userData, currentCandidate))
					return true;

				if (swapPermutations.count(needle.graph.nodes[needleNodeIdx].typeId) > 0)
					for (const auto &permutation : swapPermutations.at(needle.graph.nodes[needleNodeIdx].typeId)) {
						std::map<std::string, std::string> currentSubCandidate = currentCandidate;
						applyPermutation(currentSubCandidate, permutation);
						if (matchNodePorts(needle.graph, needleNodeIdx, haystack.graph, haystackNodeIdx, currentCandidate) &&
								userSolver->userCompareNodes(needle.graphId, nn.nodeId, nn.userData, haystack.graphId, hn.nodeId, hn.userData, currentCandidate))
							return true;
					}
			}
		}

		return false;
	}

	void generateEnumerationMatrix(std::vector<std::set<int>> &enumerationMatrix, const GraphData &needle, const GraphData &haystack, const std::map<std::string, std::set<std::string>> &initialMappings) const
	{
		std::map<std::string, std::set<int>> haystackNodesByTypeId;
		for (int i = 0; i < int(haystack.graph.nodes.size()); i++)
			haystackNodesByTypeId[haystack.graph.nodes[i].typeId].insert(i);

		enumerationMatrix.clear();
		enumerationMatrix.resize(needle.graph.nodes.size());
		for (int i = 0; i < int(needle.graph.nodes.size()); i++)
		{
			const Graph::Node &nn = needle.graph.nodes[i];

			for (int j : haystackNodesByTypeId[nn.typeId]) {
				const Graph::Node &hn = haystack.graph.nodes[j];
				if (initialMappings.count(nn.nodeId) > 0 && initialMappings.at(nn.nodeId).count(hn.nodeId) == 0)
					continue;
				if (!matchNodes(needle, i, haystack, j))
					continue;
				enumerationMatrix[i].insert(j);
			}

			if (compatibleTypes.count(nn.typeId) > 0)
				for (const std::string &compatibleTypeId : compatibleTypes.at(nn.typeId))
					for (int j : haystackNodesByTypeId[compatibleTypeId]) {
						const Graph::Node &hn = haystack.graph.nodes[j];
						if (initialMappings.count(nn.nodeId) > 0 && initialMappings.at(nn.nodeId).count(hn.nodeId) == 0)
							continue;
						if (!matchNodes(needle, i, haystack, j))
							continue;
						enumerationMatrix[i].insert(j);
					}
		}
	}

	bool checkEnumerationMatrix(std::vector<std::set<int>> &enumerationMatrix, int i, int j, const GraphData &needle, const GraphData &haystack)
	{
		for (const auto &it_needle : needle.adjMatrix.at(i))
		{
			int needleNeighbour = it_needle.first;
			int needleEdgeType = it_needle.second;

			for (int haystackNeighbour : enumerationMatrix[needleNeighbour])
				if (haystack.adjMatrix.at(j).count(haystackNeighbour) > 0) {
					int haystackEdgeType = haystack.adjMatrix.at(j).at(haystackNeighbour);
					if (diCache.compare(needleEdgeType, haystackEdgeType, swapPorts, swapPermutations)) {
						const Graph::Node &needleFromNode = needle.graph.nodes[i];
						const Graph::Node &needleToNode = needle.graph.nodes[needleNeighbour];
						const Graph::Node &haystackFromNode = haystack.graph.nodes[j];
						const Graph::Node &haystackToNode = haystack.graph.nodes[haystackNeighbour];
						if (userSolver->userCompareEdge(needle.graphId, needleFromNode.nodeId,  needleFromNode.userData, needleToNode.nodeId,  needleToNode.userData,
								haystack.graphId, haystackFromNode.nodeId, haystackFromNode.userData, haystackToNode.nodeId, haystackToNode.userData))
							goto found_match;
					}
				}

			return false;
		found_match:;
		}

		return true;
	}

	bool pruneEnumerationMatrix(std::vector<std::set<int>> &enumerationMatrix, const GraphData &needle, const GraphData &haystack, int &nextRow, bool allowOverlap)
	{
		bool didSomething = true;
		while (didSomething)
		{
			nextRow = -1;
			didSomething = false;
			for (int i = 0; i < int(enumerationMatrix.size()); i++) {
				std::set<int> newRow;
				for (int j : enumerationMatrix[i]) {
					if (!checkEnumerationMatrix(enumerationMatrix, i, j, needle, haystack))
						didSomething = true;
					else if (!allowOverlap && haystack.usedNodes[j])
						didSomething = true;
					else
						newRow.insert(j);
				}
				if (newRow.size() == 0)
					return false;
				if (newRow.size() >= 2 && (nextRow < 0 || needle.adjMatrix.at(nextRow).size() < needle.adjMatrix.at(i).size()))
					nextRow = i;
				enumerationMatrix[i].swap(newRow);
			}
		}
		return true;
	}

	void printEnumerationMatrix(const std::vector<std::set<int>> &enumerationMatrix, int maxHaystackNodeIdx = -1) const
	{
		if (maxHaystackNodeIdx < 0) {
			for (const auto &it : enumerationMatrix)
				for (int idx : it)
					maxHaystackNodeIdx = std::max(maxHaystackNodeIdx, idx);
		}

		my_printf("       ");
		for (int j = 0; j < maxHaystackNodeIdx; j += 5)
			my_printf("%-6d", j);
		my_printf("\n");

		for (int i = 0; i < int(enumerationMatrix.size()); i++)
		{
			my_printf("%5d:", i);
			for (int j = 0; j < maxHaystackNodeIdx; j++) {
				if (j % 5 == 0)
					my_printf(" ");
				my_printf("%c", enumerationMatrix[i].count(j) > 0 ? '*' : '.');
			}
			my_printf("\n");
		}
	}

	bool checkPortmapCandidate(const std::vector<std::set<int>> &enumerationMatrix, const GraphData &needle,  const GraphData &haystack, int idx, const std::map<std::string, std::string> &currentCandidate)
	{
		assert(enumerationMatrix[idx].size() == 1);
		int idxHaystack = *enumerationMatrix[idx].begin();

		const Graph::Node &nn = needle.graph.nodes[idx];
		const Graph::Node &hn = haystack.graph.nodes[idxHaystack];

		if (!matchNodePorts(needle.graph, idx, haystack.graph, idxHaystack, currentCandidate) ||
				!userSolver->userCompareNodes(needle.graphId, nn.nodeId, nn.userData, haystack.graphId, hn.nodeId, hn.userData, currentCandidate))
			return false;

		for (const auto &it_needle : needle.adjMatrix.at(idx))
		{
			int needleNeighbour = it_needle.first;
			int needleEdgeType = it_needle.second;

			assert(enumerationMatrix[needleNeighbour].size() == 1);
			int haystackNeighbour = *enumerationMatrix[needleNeighbour].begin();

			assert(haystack.adjMatrix.at(idxHaystack).count(haystackNeighbour) > 0);
			int haystackEdgeType = haystack.adjMatrix.at(idxHaystack).at(haystackNeighbour);
			if (!diCache.compare(needleEdgeType, haystackEdgeType, currentCandidate, swapPorts, swapPermutations))
				return false;
		}

		return true;
	}

	void generatePortmapCandidates(std::set<std::map<std::string, std::string>> &portmapCandidates, const std::vector<std::set<int>> &enumerationMatrix,
			const GraphData &needle, const GraphData &haystack, int idx)
	{
		std::map<std::string, std::string> currentCandidate;

		for (const auto &port : needle.graph.nodes[idx].ports)
			currentCandidate[port.portId] = port.portId;

		if (swapPorts.count(needle.graph.nodes[idx].typeId) == 0)
		{
			if (checkPortmapCandidate(enumerationMatrix, needle, haystack, idx, currentCandidate))
				portmapCandidates.insert(currentCandidate);

			if (swapPermutations.count(needle.graph.nodes[idx].typeId) > 0)
				for (const auto &permutation : swapPermutations.at(needle.graph.nodes[idx].typeId)) {
					std::map<std::string, std::string> currentSubCandidate = currentCandidate;
					applyPermutation(currentSubCandidate, permutation);
					if (checkPortmapCandidate(enumerationMatrix, needle, haystack, idx, currentSubCandidate))
						portmapCandidates.insert(currentSubCandidate);
				}
		}
		else
		{
			std::vector<std::vector<std::string>> thisSwapPorts;
			for (const auto &ports : swapPorts.at(needle.graph.nodes[idx].typeId)) {
				std::vector<std::string> portsVector;
				for (const auto &port : ports)
					portsVector.push_back(port);
				thisSwapPorts.push_back(portsVector);
			}

			int thisPermutations = numberOfPermutationsArray(thisSwapPorts);
			for (int i = 0; i < thisPermutations; i++)
			{
				permutateVectorToMapArray(currentCandidate, thisSwapPorts, i);

				if (checkPortmapCandidate(enumerationMatrix, needle, haystack, idx, currentCandidate))
					portmapCandidates.insert(currentCandidate);

				if (swapPermutations.count(needle.graph.nodes[idx].typeId) > 0)
					for (const auto &permutation : swapPermutations.at(needle.graph.nodes[idx].typeId)) {
						std::map<std::string, std::string> currentSubCandidate = currentCandidate;
						applyPermutation(currentSubCandidate, permutation);
						if (checkPortmapCandidate(enumerationMatrix, needle, haystack, idx, currentSubCandidate))
							portmapCandidates.insert(currentSubCandidate);
					}
			}
		}
	}

	bool prunePortmapCandidates(std::vector<std::set<std::map<std::string, std::string>>> &portmapCandidates, std::vector<std::set<int>> enumerationMatrix, const GraphData &needle, const GraphData &haystack)
	{
		bool didSomething = false;

		// strategy #1: prune impossible port mappings

		for (int i = 0; i < int(needle.graph.nodes.size()); i++)
		{
			assert(enumerationMatrix[i].size() == 1);
			int j = *enumerationMatrix[i].begin();

			std::set<std::map<std::string, std::string>> thisCandidates;
			portmapCandidates[i].swap(thisCandidates);

			for (const auto &testCandidate : thisCandidates)
			{
				for (const auto &it_needle : needle.adjMatrix.at(i))
				{
					int needleNeighbour = it_needle.first;
					int needleEdgeType = it_needle.second;

					assert(enumerationMatrix[needleNeighbour].size() == 1);
					int haystackNeighbour = *enumerationMatrix[needleNeighbour].begin();

					assert(haystack.adjMatrix.at(j).count(haystackNeighbour) > 0);
					int haystackEdgeType = haystack.adjMatrix.at(j).at(haystackNeighbour);

					std::set<std::map<std::string, std::string>> &candidates =
							i == needleNeighbour ? thisCandidates : portmapCandidates[needleNeighbour];

					for (const auto &otherCandidate : candidates) {
						if (diCache.compare(needleEdgeType, haystackEdgeType, testCandidate, otherCandidate))
							goto found_match;
					}

					didSomething = true;
					goto purgeCandidate;
				found_match:;
				}

				portmapCandidates[i].insert(testCandidate);
			purgeCandidate:;
			}

			if (portmapCandidates[i].size() == 0)
				return false;
		}

		if (didSomething)
			return true;

		// strategy #2: prune a single random port mapping

		for (int i = 0; i < int(needle.graph.nodes.size()); i++)
			if (portmapCandidates[i].size() > 1) {
				// remove last mapping. this keeps ports unswapped in don't-care situations
				portmapCandidates[i].erase(--portmapCandidates[i].end());
				return true;
			}

		return false;
	}

	void ullmannRecursion(std::vector<Solver::Result> &results, std::vector<std::set<int>> &enumerationMatrix, int iter, const GraphData &needle, GraphData &haystack, bool allowOverlap, int limitResults)
	{
		int i = -1;
		if (!pruneEnumerationMatrix(enumerationMatrix, needle, haystack, i, allowOverlap))
			return;

		if (i < 0)
		{
			Solver::Result result;
			result.needleGraphId = needle.graphId;
			result.haystackGraphId = haystack.graphId;

			std::vector<std::set<std::map<std::string, std::string>>> portmapCandidates;
			portmapCandidates.resize(enumerationMatrix.size());

			for (int j = 0; j < int(enumerationMatrix.size()); j++) {
				Solver::ResultNodeMapping mapping;
				mapping.needleNodeId = needle.graph.nodes[j].nodeId;
				mapping.needleUserData = needle.graph.nodes[j].userData;
				mapping.haystackNodeId = haystack.graph.nodes[*enumerationMatrix[j].begin()].nodeId;
				mapping.haystackUserData = haystack.graph.nodes[*enumerationMatrix[j].begin()].userData;
				generatePortmapCandidates(portmapCandidates[j], enumerationMatrix, needle, haystack, j);
				result.mappings[needle.graph.nodes[j].nodeId] = mapping;
			}

			while (prunePortmapCandidates(portmapCandidates, enumerationMatrix, needle, haystack)) { }

			if (verbose) {
				my_printf("\nPortmapper results:\n");
				for (int j = 0; j < int(enumerationMatrix.size()); j++) {
					my_printf("%5d: %s\n", j, needle.graph.nodes[j].nodeId.c_str());
					int variantCounter = 0;
					for (auto &i2 : portmapCandidates.at(j)) {
						my_printf("%*s variant %2d:", 6, "", variantCounter++);
						int mapCounter = 0;
						for (auto &i3 : i2)
							my_printf("%s %s -> %s", mapCounter++ ? "," : "", i3.first.c_str(), i3.second.c_str());
						my_printf("\n");
					}
				}
			}

			for (int j = 0; j < int(enumerationMatrix.size()); j++) {
				if (portmapCandidates[j].size() == 0) {
					if (verbose) {
						my_printf("\nSolution (rejected by portmapper):\n");
						printEnumerationMatrix(enumerationMatrix, haystack.graph.nodes.size());
					}
					return;
				}
				result.mappings[needle.graph.nodes[j].nodeId].portMapping = *portmapCandidates[j].begin();
			}

			if (!userSolver->userCheckSolution(result)) {
				if (verbose) {
					my_printf("\nSolution (rejected by userCheckSolution):\n");
					printEnumerationMatrix(enumerationMatrix, haystack.graph.nodes.size());
				}
				return;
			}

			for (int j = 0; j < int(enumerationMatrix.size()); j++)
				if (!haystack.graph.nodes[*enumerationMatrix[j].begin()].shared)
					haystack.usedNodes[*enumerationMatrix[j].begin()] = true;

			if (verbose) {
				my_printf("\nSolution:\n");
				printEnumerationMatrix(enumerationMatrix, haystack.graph.nodes.size());
			}

			results.push_back(result);
			return;
		}

		if (verbose) {
			my_printf("\n");
			my_printf("Enumeration Matrix at recursion level %d (%d):\n", iter, i);
			printEnumerationMatrix(enumerationMatrix, haystack.graph.nodes.size());
		}

		std::set<int> activeRow;
		enumerationMatrix[i].swap(activeRow);

		for (int j : activeRow)
		{
			// found enough?
			if (limitResults >= 0 && int(results.size()) >= limitResults)
				return;

			// already used by other solution -> try next
			if (!allowOverlap && haystack.usedNodes[j])
				continue;

			// create enumeration matrix for child in recursion tree
			std::vector<std::set<int>> nextEnumerationMatrix = enumerationMatrix;
			for (int k = 0; k < int(nextEnumerationMatrix.size()); k++)
				nextEnumerationMatrix[k].erase(j);
			nextEnumerationMatrix[i].insert(j);

			// recursion
			ullmannRecursion(results, nextEnumerationMatrix, iter+1, needle, haystack, allowOverlap, limitResults);

			// we just have found something -> unroll to top recursion level
			if (!allowOverlap && haystack.usedNodes[j] && iter > 0)
				return;
		}
	}

	// additional data structes and functions for mining

	struct NodeSet {
		std::string graphId;
		std::set<int> nodes;
		NodeSet(std::string graphId, int node1, int node2) {
			this->graphId = graphId;
			nodes.insert(node1);
			nodes.insert(node2);
		}
		NodeSet(std::string graphId, const std::vector<int> &nodes) {
			this->graphId = graphId;
			for (int node : nodes)
				this->nodes.insert(node);
		}
		void extend(const NodeSet &other) {
			assert(this->graphId == other.graphId);
			for (int node : other.nodes)
				nodes.insert(node);
		}
		int extendCandidate(const NodeSet &other) const {
			if (graphId != other.graphId)
				return 0;
			int newNodes = 0;
			bool intersect = false;
			for (int node : other.nodes)
				if (nodes.count(node) > 0)
					intersect = true;
				else
					newNodes++;
			return intersect ? newNodes : 0;
		}
		bool operator <(const NodeSet &other) const {
			if (graphId != other.graphId)
				return graphId < other.graphId;
			return nodes < other.nodes;
		}
		std::string to_string() const {
			std::string str = graphId + "(";
			bool first = true;
			for (int node : nodes) {
				str += my_stringf("%s%d", first ? "" : " ", node);
				first = false;
			}
			return str + ")";
		}
	};

	void solveForMining(std::vector<Solver::Result> &results, const GraphData &needle)
	{
		bool backupVerbose = verbose;
		verbose = false;

		for (auto &it : graphData)
		{
			GraphData &haystack = it.second;

			std::vector<std::set<int>> enumerationMatrix;
			std::map<std::string, std::set<std::string>> initialMappings;
			generateEnumerationMatrix(enumerationMatrix, needle, haystack, initialMappings);

			haystack.usedNodes.resize(haystack.graph.nodes.size());
			ullmannRecursion(results, enumerationMatrix, 0, needle, haystack, true, -1);
		}

		verbose = backupVerbose;
	}

	int testForMining(std::vector<Solver::MineResult> &results, std::set<NodeSet> &usedSets, std::set<NodeSet> &nextPool, NodeSet &testSet,
			const std::string &graphId, const Graph &graph, int minNodes, int minMatches, int limitMatchesPerGraph)
	{
		// my_printf("test: %s\n", testSet.to_string().c_str());

		GraphData needle;
		std::vector<std::string> needle_nodes;
		for (int nodeIdx : testSet.nodes)
			needle_nodes.push_back(graph.nodes[nodeIdx].nodeId);
		needle.graph = Graph(graph, needle_nodes);
		needle.graph.markAllExtern();
		diCache.add(needle.graph, needle.adjMatrix, graphId, userSolver);

		std::vector<Solver::Result> ullmannResults;
		solveForMining(ullmannResults, needle);

		int matches = 0;
		std::map<std::string, int> matchesPerGraph;
		std::set<NodeSet> thisNodeSetSet;

		for (auto &it : ullmannResults)
		{
			std::vector<int> resultNodes;
			for (auto &i2 : it.mappings)
				resultNodes.push_back(graphData[it.haystackGraphId].graph.nodeMap[i2.second.haystackNodeId]);
			NodeSet resultSet(it.haystackGraphId, resultNodes);

			// my_printf("match: %s%s\n", resultSet.to_string().c_str(), usedSets.count(resultSet) > 0 ? " (dup)" : "");

#if 0
			if (usedSets.count(resultSet) > 0) {
				// Because of shorted pins isomorphisim is not always bidirectional!
				//
				// This means that the following assert is not true in all cases and subgraph A might
				// show up in the matches for subgraph B but not vice versa... This also means that the
				// order in which subgraphs are processed has an impact on the results set.
				//
				assert(thisNodeSetSet.count(resultSet) > 0);
				continue;
			}
#else
			if (thisNodeSetSet.count(resultSet) > 0)
				continue;
#endif

			usedSets.insert(resultSet);
			thisNodeSetSet.insert(resultSet);

			matchesPerGraph[it.haystackGraphId]++;
			if (limitMatchesPerGraph < 0 || matchesPerGraph[it.haystackGraphId] < limitMatchesPerGraph)
				matches++;
		}

		if (matches < minMatches)
			return matches;

		if (minNodes <= int(testSet.nodes.size()))
		{
			Solver::MineResult result;
			result.graphId = graphId;
			result.totalMatchesAfterLimits = matches;
			result.matchesPerGraph = matchesPerGraph;
			for (int nodeIdx : testSet.nodes) {
				Solver::MineResultNode resultNode;
				resultNode.nodeId = graph.nodes[nodeIdx].nodeId;
				resultNode.userData = graph.nodes[nodeIdx].userData;
				result.nodes.push_back(resultNode);
			}
			results.push_back(result);
		}

		nextPool.insert(thisNodeSetSet.begin(), thisNodeSetSet.end());
		return matches;
	}

	void findNodePairs(std::vector<Solver::MineResult> &results, std::set<NodeSet> &nodePairs, int minNodes, int minMatches, int limitMatchesPerGraph)
	{
		int groupCounter = 0;
		std::set<NodeSet> usedPairs;
		nodePairs.clear();

		if (verbose)
			my_printf("\nMining for frequent node pairs:\n");

		for (auto &graph_it : graphData)
		for (int node1 = 0; node1 < int(graph_it.second.graph.nodes.size()); node1++)
		for (auto &adj_it : graph_it.second.adjMatrix.at(node1))
		{
			const std::string &graphId = graph_it.first;
			const auto &graph = graph_it.second.graph;
			int node2 = adj_it.first;

			if (node1 == node2)
				continue;

			NodeSet pair(graphId, node1, node2);

			if (usedPairs.count(pair) > 0)
				continue;

			int matches = testForMining(results, usedPairs, nodePairs, pair, graphId, graph, minNodes, minMatches, limitMatchesPerGraph);

			if (verbose)
				my_printf("Pair %s[%s,%s] -> %d%s\n", graphId.c_str(), graph.nodes[node1].nodeId.c_str(),
						graph.nodes[node2].nodeId.c_str(), matches, matches < minMatches ? "  *purge*" : "");

			if (minMatches <= matches)
				groupCounter++;
		}

		if (verbose)
			my_printf("Found a total of %d subgraphs in %d groups.\n", int(nodePairs.size()), groupCounter);
	}

	void findNextPool(std::vector<Solver::MineResult> &results, std::set<NodeSet> &pool,
			int oldSetSize, int increment, int minNodes, int minMatches, int limitMatchesPerGraph)
	{
		int groupCounter = 0;
		std::map<std::string, std::vector<const NodeSet*>> poolPerGraph;
		std::set<NodeSet> nextPool;

		for (auto &it : pool)
			poolPerGraph[it.graphId].push_back(&it);

		if (verbose)
			my_printf("\nMining for frequent subcircuits of size %d using increment %d:\n", oldSetSize+increment, increment);

		int count = 0;
		for (auto &it : poolPerGraph)
		{
			std::map<int, std::set<int>> node2sets;
			std::set<NodeSet> usedSets;

			for (int idx = 0; idx < int(it.second.size()); idx++) {
				for (int node : it.second[idx]->nodes)
					node2sets[node].insert(idx);
			}

			for (int idx1 = 0; idx1 < int(it.second.size()); idx1++, count++)
			{
				std::set<int> idx2set;

				for (int node : it.second[idx1]->nodes)
					for (int idx2 : node2sets[node])
						if (idx2 > idx1)
							idx2set.insert(idx2);

				for (int idx2 : idx2set)
				{
					if (it.second[idx1]->extendCandidate(*it.second[idx2]) != increment)
						continue;

					NodeSet mergedSet = *it.second[idx1];
					mergedSet.extend(*it.second[idx2]);

					if (usedSets.count(mergedSet) > 0)
						continue;

					const std::string &graphId = it.first;
					const auto &graph = graphData[it.first].graph;

					if (verbose) {
						my_printf("<%d%%/%d> Found %s[", int(100*count/pool.size()), oldSetSize+increment, graphId.c_str());
						bool first = true;
						for (int nodeIdx : mergedSet.nodes) {
							my_printf("%s%s", first ? "" : ",", graph.nodes[nodeIdx].nodeId.c_str());
							first = false;
						}
						my_printf("] ->");
					}

					int matches = testForMining(results, usedSets, nextPool, mergedSet, graphId, graph, minNodes, minMatches, limitMatchesPerGraph);

					if (verbose)
						my_printf(" %d%s\n", matches, matches < minMatches ? "  *purge*" : "");

					if (minMatches <= matches)
						groupCounter++;
				}
			}
		}

		pool.swap(nextPool);

		if (verbose)
			my_printf("Found a total of %d subgraphs in %d groups.\n", int(pool.size()), groupCounter);
	}

	// interface to the public solver class

protected:
	SolverWorker(Solver *userSolver) : userSolver(userSolver), verbose(false)
	{
	}

	void setVerbose()
	{
		verbose = true;
	}

	void addGraph(std::string graphId, const Graph &graph)
	{
		assert(graphData.count(graphId) == 0);

		GraphData &gd = graphData[graphId];
		gd.graphId = graphId;
		gd.graph = graph;
		diCache.add(gd.graph, gd.adjMatrix, graphId, userSolver);
	}

	void addCompatibleTypes(std::string needleTypeId, std::string haystackTypeId)
	{
		compatibleTypes[needleTypeId].insert(haystackTypeId);
	}

	void addCompatibleConstants(int needleConstant, int haystackConstant)
	{
		compatibleConstants[needleConstant].insert(haystackConstant);
	}

	void addSwappablePorts(std::string needleTypeId, const std::set<std::string> &ports)
	{
		swapPorts[needleTypeId].insert(ports);
		diCache.compareCache.clear();
	}

	void addSwappablePortsPermutation(std::string needleTypeId, const std::map<std::string, std::string> &portMapping)
	{
		swapPermutations[needleTypeId].insert(portMapping);
		diCache.compareCache.clear();
	}

	void solve(std::vector<Solver::Result> &results, std::string needleGraphId, std::string haystackGraphId,
			const std::map<std::string, std::set<std::string>> &initialMappings, bool allowOverlap, int maxSolutions)
	{
		assert(graphData.count(needleGraphId) > 0);
		assert(graphData.count(haystackGraphId) > 0);

		const GraphData &needle = graphData[needleGraphId];
		GraphData &haystack = graphData[haystackGraphId];

		std::vector<std::set<int>> enumerationMatrix;
		generateEnumerationMatrix(enumerationMatrix, needle, haystack, initialMappings);

		if (verbose)
		{
			my_printf("\n");
			my_printf("Needle nodes:\n");
			for (int i = 0; i < int(needle.graph.nodes.size()); i++)
				my_printf("%5d: %s (%s)\n", i, needle.graph.nodes[i].nodeId.c_str(), needle.graph.nodes[i].typeId.c_str());

			my_printf("\n");
			my_printf("Haystack nodes:\n");
			for (int i = 0; i < int(haystack.graph.nodes.size()); i++)
				my_printf("%5d: %s (%s)\n", i, haystack.graph.nodes[i].nodeId.c_str(), haystack.graph.nodes[i].typeId.c_str());

			my_printf("\n");
			my_printf("Needle Adjecency Matrix:\n");
			printAdjMatrix(needle.adjMatrix);

			my_printf("\n");
			my_printf("Haystack Adjecency Matrix:\n");
			printAdjMatrix(haystack.adjMatrix);

			my_printf("\n");
			my_printf("Edge Types:\n");
			diCache.printEdgeTypes();

			my_printf("\n");
			my_printf("Enumeration Matrix (haystack nodes at column indices):\n");
			printEnumerationMatrix(enumerationMatrix, haystack.graph.nodes.size());
		}

		haystack.usedNodes.resize(haystack.graph.nodes.size());
		ullmannRecursion(results, enumerationMatrix, 0, needle, haystack, allowOverlap, maxSolutions > 0 ? results.size() + maxSolutions : -1);
	}

	void mine(std::vector<Solver::MineResult> &results, int minNodes, int maxNodes, int minMatches, int limitMatchesPerGraph)
	{
		int nodeSetSize = 2;
		std::set<NodeSet> pool;
		findNodePairs(results, pool, minNodes, minMatches, limitMatchesPerGraph);

		while ((maxNodes < 0 || nodeSetSize < maxNodes) && pool.size() > 0)
		{
			int increment = nodeSetSize - 1;
			if (nodeSetSize + increment >= minNodes)
				increment = minNodes - nodeSetSize;
			if (nodeSetSize >= minNodes)
				increment = 1;

			findNextPool(results, pool, nodeSetSize, increment, minNodes, minMatches, limitMatchesPerGraph);
			nodeSetSize += increment;
		}
	}

	void clearOverlapHistory()
	{
		for (auto &it : graphData)
			it.second.usedNodes.clear();
	}

	void clearConfig()
	{
		compatibleTypes.clear();
		compatibleConstants.clear();
		swapPorts.clear();
		swapPermutations.clear();
		diCache.compareCache.clear();
	}

	friend class Solver;
};

bool Solver::userCompareNodes(const std::string&, const std::string&, void*, const std::string&, const std::string&, void*, const std::map<std::string, std::string>&)
{
	return true;
}

std::string Solver::userAnnotateEdge(const std::string&, const std::string&, void*, const std::string&, void*)
{
	return std::string();
}

bool Solver::userCompareEdge(const std::string&, const std::string&, void*, const std::string&, void*, const std::string&, const std::string&, void*, const std::string&, void*)
{
	return true;
}

bool Solver::userCheckSolution(const Result&)
{
	return true;
}

SubCircuit::Solver::Solver()
{
	worker = new SolverWorker(this);
}

SubCircuit::Solver::~Solver()
{
	delete worker;
}

void SubCircuit::Solver::setVerbose()
{
	worker->setVerbose();
}

void SubCircuit::Solver::addGraph(std::string graphId, const Graph &graph)
{
	worker->addGraph(graphId, graph);
}

void SubCircuit::Solver::addCompatibleTypes(std::string needleTypeId, std::string haystackTypeId)
{
	worker->addCompatibleTypes(needleTypeId, haystackTypeId);
}

void SubCircuit::Solver::addCompatibleConstants(int needleConstant, int haystackConstant)
{
	worker->addCompatibleConstants(needleConstant, haystackConstant);
}

void SubCircuit::Solver::addSwappablePorts(std::string needleTypeId, std::string portId1, std::string portId2, std::string portId3, std::string portId4)
{
	std::set<std::string> ports;
	ports.insert(portId1);
	ports.insert(portId2);
	ports.insert(portId3);
	ports.insert(portId4);
	ports.erase(std::string());
	addSwappablePorts(needleTypeId, ports);
}

void SubCircuit::Solver::addSwappablePorts(std::string needleTypeId, std::set<std::string> ports)
{
	worker->addSwappablePorts(needleTypeId, ports);
}

void SubCircuit::Solver::addSwappablePortsPermutation(std::string needleTypeId, std::map<std::string, std::string> portMapping)
{
	worker->addSwappablePortsPermutation(needleTypeId, portMapping);
}

void SubCircuit::Solver::solve(std::vector<Result> &results, std::string needleGraphId, std::string haystackGraphId, bool allowOverlap, int maxSolutions)
{
	std::map<std::string, std::set<std::string>> emptyInitialMapping;
	worker->solve(results, needleGraphId, haystackGraphId, emptyInitialMapping, allowOverlap, maxSolutions);
}

void SubCircuit::Solver::solve(std::vector<Result> &results, std::string needleGraphId, std::string haystackGraphId,
		const std::map<std::string, std::set<std::string>> &initialMappings, bool allowOverlap, int maxSolutions)
{
	worker->solve(results, needleGraphId, haystackGraphId, initialMappings, allowOverlap, maxSolutions);
}

void SubCircuit::Solver::mine(std::vector<MineResult> &results, int minNodes, int maxNodes, int minMatches, int limitMatchesPerGraph)
{
	worker->mine(results, minNodes, maxNodes, minMatches, limitMatchesPerGraph);
}

void SubCircuit::Solver::clearOverlapHistory()
{
	worker->clearOverlapHistory();
}

void SubCircuit::Solver::clearConfig()
{
	worker->clearConfig();
}

