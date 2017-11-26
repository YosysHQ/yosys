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

#ifndef SUBCIRCUIT_H
#define SUBCIRCUIT_H

#include <string>
#include <vector>
#include <set>
#include <map>

namespace SubCircuit
{
	class SolverWorker;

	class Graph
	{
	protected:
		struct BitRef {
			int nodeIdx, portIdx, bitIdx;
			BitRef(int nodeIdx = -1, int portIdx = -1, int bitIdx = -1) : nodeIdx(nodeIdx), portIdx(portIdx), bitIdx(bitIdx) { };
			bool operator < (const BitRef &other) const;
		};

		struct Edge {
			std::set<BitRef> portBits;
			int constValue;
			bool isExtern;
			Edge() : constValue(0), isExtern(false) { };
		};

		struct PortBit {
			int edgeIdx;
			PortBit() : edgeIdx(-1) { };
		};

		struct Port {
			std::string portId;
			int minWidth;
			std::vector<PortBit> bits;
			Port() : minWidth(-1) { };
		};

		struct Node {
			std::string nodeId, typeId;
			std::map<std::string, int> portMap;
			std::vector<Port> ports;
			void *userData;
			bool shared;
			Node() : userData(NULL), shared(false) { };
		};

		bool allExtern;
		std::map<std::string, int> nodeMap;
		std::vector<Node> nodes;
		std::vector<Edge> edges;

	public:
		Graph() : allExtern(false) { };
		Graph(const Graph &other, const std::vector<std::string> &otherNodes);

		void createNode(std::string nodeId, std::string typeId, void *userData = NULL, bool shared = false);
		void createPort(std::string nodeId, std::string portId, int width = 1, int minWidth = -1);
		void createConnection(std::string fromNodeId, std::string fromPortId, int fromBit, std::string toNodeId, std::string toPortId, int toBit, int width = 1);
		void createConnection(std::string fromNodeId, std::string fromPortId, std::string toNodeId, std::string toPortId);
		void createConstant(std::string toNodeId, std::string toPortId, int toBit, int constValue);
		void createConstant(std::string toNodeId, std::string toPortId, int constValue);
		void markExtern(std::string nodeId, std::string portId, int bit = -1);
		void markAllExtern();
		void print();

		friend class SolverWorker;
	};

	class Solver
	{
	public:
		struct ResultNodeMapping {
			std::string needleNodeId, haystackNodeId;
			void *needleUserData, *haystackUserData;
			std::map<std::string, std::string> portMapping;
		};
		struct Result {
			std::string needleGraphId, haystackGraphId;
			std::map<std::string, ResultNodeMapping> mappings;
		};

		struct MineResultNode {
			std::string nodeId;
			void *userData;
		};
		struct MineResult {
			std::string graphId;
			int totalMatchesAfterLimits;
			std::map<std::string, int> matchesPerGraph;
			std::vector<MineResultNode> nodes;
		};

	private:
		SolverWorker *worker;

	protected:
		virtual bool userCompareNodes(const std::string &needleGraphId, const std::string &needleNodeId, void *needleUserData,
				const std::string &haystackGraphId, const std::string &haystackNodeId, void *haystackUserData, const std::map<std::string, std::string> &portMapping);

		virtual std::string userAnnotateEdge(const std::string &graphId, const std::string &fromNodeId, void *fromUserData, const std::string &toNodeId, void *toUserData);

		virtual bool userCompareEdge(const std::string &needleGraphId, const std::string &needleFromNodeId, void *needleFromUserData, const std::string &needleToNodeId, void *needleToUserData,
				const std::string &haystackGraphId, const std::string &haystackFromNodeId, void *haystackFromUserData, const std::string &haystackToNodeId, void *haystackToUserData);

		virtual bool userCheckSolution(const Result &result);

		friend class SolverWorker;

	public:
		Solver();
		virtual ~Solver();

		void setVerbose();
		void addGraph(std::string graphId, const Graph &graph);
		void addCompatibleTypes(std::string needleTypeId, std::string haystackTypeId);
		void addCompatibleConstants(int needleConstant, int haystackConstant);
		void addSwappablePorts(std::string needleTypeId, std::string portId1, std::string portId2, std::string portId3 = std::string(), std::string portId4 = std::string());
		void addSwappablePorts(std::string needleTypeId, std::set<std::string> ports);
		void addSwappablePortsPermutation(std::string needleTypeId, std::map<std::string, std::string> portMapping);

		void solve(std::vector<Result> &results, std::string needleGraphId, std::string haystackGraphId, bool allowOverlap = true, int maxSolutions = -1);
		void solve(std::vector<Result> &results, std::string needleGraphId, std::string haystackGraphId,
				const std::map<std::string, std::set<std::string>> &initialMapping, bool allowOverlap = true, int maxSolutions = -1);

		void mine(std::vector<MineResult> &results, int minNodes, int maxNodes, int minMatches, int limitMatchesPerGraph = -1);

		void clearOverlapHistory();
		void clearConfig();
	};
}

#endif /* SUBCIRCUIT_H */
