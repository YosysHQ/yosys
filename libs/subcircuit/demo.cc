#include "subcircuit.h"
#include <stdio.h>

#define VERBOSE

int main()
{
	SubCircuit::Graph needle, haystack;

	// create needle graph

	needle.createNode("mul_1", "product");
	needle.createPort("mul_1", "A", 4);
	needle.createPort("mul_1", "B", 4);
	needle.createPort("mul_1", "Y", 4);
	needle.markExtern("mul_1", "A");
	needle.markExtern("mul_1", "B");

	needle.createNode("mul_2", "product");
	needle.createPort("mul_2", "A", 4);
	needle.createPort("mul_2", "B", 4);
	needle.createPort("mul_2", "Y", 4);
	needle.markExtern("mul_2", "A");
	needle.markExtern("mul_2", "B");

	needle.createNode("add_1", "sum");
	needle.createPort("add_1", "A", 4);
	needle.createPort("add_1", "B", 4);
	needle.createPort("add_1", "Y", 4);
	needle.markExtern("add_1", "Y");

	needle.createConnection("mul_1", "Y", "add_1", "A");
	needle.createConnection("mul_2", "Y", "add_1", "B");

#ifdef VERBOSE
	printf("\n");
	needle.print();
#endif

	// create haystack graph

#if 0
	for (int i = 0; i < 4; i++) {
		char id[100];
		snprintf(id, 100, "mul_%d", i);
		haystack.createNode(id, "mul");
		haystack.createPort(id, "A", 4);
		haystack.createPort(id, "B", 4);
		haystack.createPort(id, "Y", 4);
		haystack.markExtern(id, "A");
		haystack.markExtern(id, "B");
	}

	for (int i = 0; i < 3; i++) {
		char id[100];
		snprintf(id, 100, "add_%d", i);
		haystack.createNode(id, "add");
		haystack.createPort(id, "A", 4);
		haystack.createPort(id, "B", 4);
		haystack.createPort(id, "Y", 4);
	}

	haystack.createConnection("mul_0", "Y", "add_0", "A");
	haystack.createConnection("mul_1", "Y", "add_0", "B");

	haystack.createConnection("mul_2", "Y", "add_1", "A");
	haystack.createConnection("mul_3", "Y", "add_1", "B");

	haystack.createConnection("add_0", "Y", "add_2", "A");
	haystack.createConnection("add_1", "Y", "add_2", "B");
	haystack.markExtern("add_2", "Y");
#else
	std::vector<std::string> cellIds;
	srand48(12345);

	for (int i = 0; i < 45; i++) {
		char id[100];
		snprintf(id, 100, "cell_%02d", i);
		haystack.createNode(id, i < 30 ? "mul" : "add");
		haystack.createPort(id, "A", 4);
		haystack.createPort(id, "B", 4);
		haystack.createPort(id, "Y", 4);
		cellIds.push_back(id);
	}

	for (int i = 0; i < int(cellIds.size()); i++) {
		if (lrand48() % (i < 20 ? 3 : 2) != 0)
			continue;
		const std::string &id = cellIds[i];
		const std::string &id_left = cellIds[lrand48() % cellIds.size()];
		const std::string &id_right = cellIds[lrand48() % cellIds.size()];
		haystack.createConnection(id_left, "Y", id, "A");
		haystack.createConnection(id_right, "Y", id, "B");
	}
#endif

#ifdef VERBOSE
	printf("\n");
	haystack.print();
#endif

	// search needle in haystack

	SubCircuit::Solver solver;
	std::vector<SubCircuit::Solver::Result> results;

#ifdef VERBOSE
	solver.setVerbose();
#endif

	solver.addCompatibleTypes("product", "mul");
	solver.addCompatibleTypes("sum", "add");

	solver.addSwappablePorts("product", "A", "B");
	solver.addSwappablePorts("sum", "A", "B");

	solver.addGraph("needle", needle);
	solver.addGraph("haystack", haystack);
	solver.solve(results, "needle", "haystack");

	for (int i = 0; i < int(results.size()); i++) {
		printf("\nMatch #%d: (%s in %s)\n", i, results[i].needleGraphId.c_str(), results[i].haystackGraphId.c_str());
		for (const auto &it : results[i].mappings) {
			printf("  %s -> %s", it.first.c_str(), it.second.haystackNodeId.c_str());
			for (const auto &it2 : it.second.portMapping)
				printf(" %s:%s", it2.first.c_str(), it2.second.c_str());
			printf("\n");
		}
	}

	printf("\n");
	return 0;
}

