#include "subcircuit.h"
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

std::vector<std::string> readLine()
{
	char buffer[4096];
	std::vector<std::string> tokenList;

	while (tokenList.size() == 0 && fgets(buffer, sizeof(buffer), stdin) != NULL) {
		for (char *p = buffer; char *tok = strtok(p, " \t\r\n"); p = NULL) {
			if (p != NULL && tok[0] == '#')
				break;
			tokenList.push_back(tok);
		}
	}

	return tokenList;
}

int main()
{
	std::string graphId;
	SubCircuit::Graph *graph = NULL;
	SubCircuit::Solver solver;
	std::map<std::string, std::set<std::string>> initialMappings;
	std::vector<SubCircuit::Solver::Result> results;
	std::vector<SubCircuit::Solver::MineResult> mineResults;
	std::vector<std::string> cmdBuffer;
	bool lastCommandExpect = false;

	while (1)
	{
		cmdBuffer = readLine();
		if (cmdBuffer.empty())
			break;

		printf(graph == NULL || cmdBuffer[0] == "endgraph" ? ">" : ">  ");
		for (const auto &tok : cmdBuffer)
			printf(" %s", tok.c_str());
		printf("\n");

		lastCommandExpect = false;

		if (graph != NULL)
		{
			if (cmdBuffer[0] == "node" && cmdBuffer.size() >= 3) {
				graph->createNode(cmdBuffer[1], cmdBuffer[2]);
				for (int i = 3; i < int(cmdBuffer.size()); i++) {
					std::string portId = cmdBuffer[i];
					int width = 1, minWidth = -1;
					if (i+1 < int(cmdBuffer.size()) && '0' <= cmdBuffer[i+1][0] && cmdBuffer[i+1][0] <= '9')
						width = atoi(cmdBuffer[++i].c_str());
					if (i+1 < int(cmdBuffer.size()) && '0' <= cmdBuffer[i+1][0] && cmdBuffer[i+1][0] <= '9')
						minWidth = atoi(cmdBuffer[++i].c_str());
					graph->createPort(cmdBuffer[1], portId, width, minWidth);
				}
				continue;
			}

			if (cmdBuffer[0] == "connect" && cmdBuffer.size() == 5) {
				graph->createConnection(cmdBuffer[1], cmdBuffer[2], cmdBuffer[3], cmdBuffer[4]);
				continue;
			}

			if (cmdBuffer[0] == "connect" && cmdBuffer.size() == 7) {
				graph->createConnection(cmdBuffer[1], cmdBuffer[2], atoi(cmdBuffer[3].c_str()), cmdBuffer[4], cmdBuffer[5], atoi(cmdBuffer[6].c_str()));
				continue;
			}

			if (cmdBuffer[0] == "connect" && cmdBuffer.size() == 8) {
				graph->createConnection(cmdBuffer[1], cmdBuffer[2], atoi(cmdBuffer[3].c_str()), cmdBuffer[4], cmdBuffer[5], atoi(cmdBuffer[6].c_str()), atoi(cmdBuffer[7].c_str()));
				continue;
			}

			if (cmdBuffer[0] == "constant" && cmdBuffer.size() == 5) {
				int constValue = cmdBuffer[4].size() > 1 && cmdBuffer[4][0] == '#' ? atoi(cmdBuffer[4].c_str()+1) : cmdBuffer[4][0];
				graph->createConstant(cmdBuffer[1], cmdBuffer[2], atoi(cmdBuffer[3].c_str()), constValue);
				continue;
			}

			if (cmdBuffer[0] == "constant" && cmdBuffer.size() == 4) {
				graph->createConstant(cmdBuffer[1], cmdBuffer[2], atoi(cmdBuffer[3].c_str()));
				continue;
			}

			if (cmdBuffer[0] == "extern" && cmdBuffer.size() >= 3) {
				for (int i = 2; i < int(cmdBuffer.size()); i++) {
					std::string portId = cmdBuffer[i];
					int bit = -1;
					if (i+1 < int(cmdBuffer.size()) && '0' <= cmdBuffer[i+1][0] && cmdBuffer[i+1][0] <= '9')
						bit = atoi(cmdBuffer[++i].c_str());
					graph->markExtern(cmdBuffer[1], portId, bit);
				}
				continue;
			}

			if (cmdBuffer[0] == "allextern" && cmdBuffer.size() == 1) {
				graph->markAllExtern();
				continue;
			}

			if (cmdBuffer[0] == "endgraph" && cmdBuffer.size() == 1) {
				solver.addGraph(graphId, *graph);
				delete graph;
				graph = NULL;
				continue;
			}
		}
		else
		{
			if (cmdBuffer[0] == "graph" && cmdBuffer.size() == 2) {
				graph = new SubCircuit::Graph;
				graphId = cmdBuffer[1];
				continue;
			}

			if (cmdBuffer[0] == "compatible" && cmdBuffer.size() == 3) {
				solver.addCompatibleTypes(cmdBuffer[1], cmdBuffer[2]);
				continue;
			}

			if (cmdBuffer[0] == "constcompat" && cmdBuffer.size() == 3) {
				int needleConstValue = cmdBuffer[1].size() > 1 && cmdBuffer[1][0] == '#' ? atoi(cmdBuffer[1].c_str()+1) : cmdBuffer[1][0];
				int haystackConstValue = cmdBuffer[2].size() > 1 && cmdBuffer[2][0] == '#' ? atoi(cmdBuffer[2].c_str()+1) : cmdBuffer[2][0];
				solver.addCompatibleConstants(needleConstValue, haystackConstValue);
				continue;
			}

			if (cmdBuffer[0] == "swapgroup" && cmdBuffer.size() >= 4) {
				std::set<std::string> ports;
				for (int i = 2; i < int(cmdBuffer.size()); i++)
					ports.insert(cmdBuffer[i]);
				solver.addSwappablePorts(cmdBuffer[1], ports);
				continue;
			}

			if (cmdBuffer[0] == "swapperm" && cmdBuffer.size() >= 4 && cmdBuffer.size() % 2 == 1 && cmdBuffer[cmdBuffer.size()/2 + 1] == ":") {
				std::map<std::string, std::string> portMapping;
				int n = (cmdBuffer.size()-3) / 2;
				for (int i = 0; i < n; i++)
					portMapping[cmdBuffer[i+2]] = cmdBuffer[i+3+n];
				solver.addSwappablePortsPermutation(cmdBuffer[1], portMapping);
				continue;
			}

			if (cmdBuffer[0] == "initmap" && cmdBuffer.size() >= 4) {
				for (int i = 2; i < int(cmdBuffer.size()); i++)
					initialMappings[cmdBuffer[1]].insert(cmdBuffer[i]);
				continue;
			}

			if (cmdBuffer[0] == "solve" && 3 <= cmdBuffer.size() && cmdBuffer.size() <= 5) {
				bool allowOverlap = true;
				int maxSolutions = -1;
				if (cmdBuffer.size() >= 4)
					allowOverlap = cmdBuffer[3] == "true" || atoi(cmdBuffer[3].c_str()) ? true : false;
				if (cmdBuffer.size() >= 5)
					maxSolutions = atoi(cmdBuffer[4].c_str());
				solver.solve(results, cmdBuffer[1], cmdBuffer[2], initialMappings, allowOverlap, maxSolutions);
				initialMappings.clear();
				continue;
			}

			if (cmdBuffer[0] == "mine" && 4 <= cmdBuffer.size() && cmdBuffer.size() <= 5) {
				solver.mine(mineResults, atoi(cmdBuffer[1].c_str()), atoi(cmdBuffer[2].c_str()),
						atoi(cmdBuffer[3].c_str()), cmdBuffer.size() == 5 ? atoi(cmdBuffer[4].c_str()) : -1);
				continue;
			}

			if (cmdBuffer[0] == "clearoverlap" && cmdBuffer.size() == 1) {
				solver.clearOverlapHistory();
				continue;
			}

			if (cmdBuffer[0] == "clearconfig" && cmdBuffer.size() == 1) {
				solver.clearConfig();
				continue;
			}

			if (cmdBuffer[0] == "verbose" && cmdBuffer.size() == 1) {
				solver.setVerbose();
				continue;
			}

			if (cmdBuffer[0] == "expect" && cmdBuffer.size() == 2) {
				int expected = atoi(cmdBuffer[1].c_str());
				printf("\n-- Expected %d, Got %d --\n", expected, int(results.size()) + int(mineResults.size()));
				for (int i = 0; i < int(results.size()); i++) {
					printf("\nMatch #%d: (%s in %s)\n", i, results[i].needleGraphId.c_str(), results[i].haystackGraphId.c_str());
					for (const auto &it : results[i].mappings) {
						printf("  %s -> %s", it.first.c_str(), it.second.haystackNodeId.c_str());
						for (const auto &it2 : it.second.portMapping)
							printf(" %s:%s", it2.first.c_str(), it2.second.c_str());
						printf("\n");
					}
				}
				for (auto &result : mineResults) {
					printf("\nFrequent SubCircuit with %d nodes and %d matches:\n", int(result.nodes.size()), result.totalMatchesAfterLimits);
					printf("  primary match in %s:", result.graphId.c_str());
					for (auto &node : result.nodes)
						printf(" %s", node.nodeId.c_str());
					printf("\n");
					for (auto &it : result.matchesPerGraph)
						printf("  matches in %s: %d\n", it.first.c_str(), it.second);
				}
				printf("\n");
				if (expected != int(results.size()) + int(mineResults.size())) {
					printf("^^ expected %d, Got %d ^^\n\n", expected, int(results.size()) + int(mineResults.size()));
					printf("   +----------------+\n");
					printf("   |  \\|/ ____ \\|/  |\n");
					printf("   |  \"@'/ ,. \\`@\"  |\n");
					printf("   |  /_| \\__/ |_\\  |\n");
					printf("   |     \\__U_/     |\n");
					printf("   |      |  |      |\n");
					printf("   +----------------+\n\n");
					return 1;
				}
				results.clear();
				mineResults.clear();
				lastCommandExpect = true;
				continue;
			}
		}

		printf("Invalid input command!\n");
		return 1;
	}

	if (graph)
		delete graph;

	if (!lastCommandExpect) {
		printf("\n-- Got %d --\n", int(results.size()) + int(mineResults.size()));
		for (int i = 0; i < int(results.size()); i++) {
			printf("\nMatch #%d: (%s in %s)\n", i, results[i].needleGraphId.c_str(), results[i].haystackGraphId.c_str());
			for (const auto &it : results[i].mappings) {
				printf("  %s -> %s", it.first.c_str(), it.second.haystackNodeId.c_str());
				for (const auto &it2 : it.second.portMapping)
					printf(" %s:%s", it2.first.c_str(), it2.second.c_str());
				printf("\n");
			}
		}
		for (auto &result : mineResults) {
			printf("\nFrequent SubCircuit with %d nodes and %d matches:\n", int(result.nodes.size()), result.totalMatchesAfterLimits);
			printf("  primary match in %s:", result.graphId.c_str());
			for (auto &node : result.nodes)
				printf(" %s", node.nodeId.c_str());
			printf("\n");
			for (auto &it : result.matchesPerGraph)
				printf("  matches in %s: %d\n", it.first.c_str(), it.second);
		}
	} else
		printf("PASSED.\n");

	printf("\n");

	return 0;
}

