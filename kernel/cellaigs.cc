/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#include "kernel/cellaigs.h"

YOSYS_NAMESPACE_BEGIN

bool AigNode::operator==(const AigNode &other) const
{
	if (portname != other.portname) return false;
	if (portbit != other.portbit) return false;
	if (inverter != other.inverter) return false;
	if (left_parent != other.left_parent) return false;
	if (right_parent != other.right_parent) return false;
	return true;
}

unsigned int AigNode::hash() const
{
	unsigned int h = mkhash_init;
	h = mkhash(portname.hash(), portbit);
	h = mkhash(h, inverter);
	h = mkhash(h, left_parent);
	h = mkhash(h, right_parent);
	return h;
}

struct AigMaker
{
	Aig *aig;
	idict<AigNode> aig_indices;

	AigMaker(Aig *aig) : aig(aig) { }

	int inport(IdString portname, int portbit, bool inverter = false)
	{
		AigNode node;
		node.portname = portname;
		node.portbit = portbit;
		node.inverter = inverter;
		node.left_parent = -1;
		node.right_parent = -1;

		if (!aig_indices.count(node)) {
			aig_indices.expect(node, GetSize(aig->nodes));
			aig->nodes.push_back(node);
		}

		return aig_indices.at(node);
	}

	int gate(int left_parent, int right_parent, bool inverter = false)
	{
		AigNode node;
		node.portbit = -1;
		node.inverter = inverter;
		node.left_parent = left_parent;
		node.right_parent = right_parent;

		if (!aig_indices.count(node)) {
			aig_indices.expect(node, GetSize(aig->nodes));
			aig->nodes.push_back(node);
		}

		return aig_indices.at(node);
	}

	void outport(int node, IdString portname, int portbit)
	{
		aig->nodes.at(node).outports.push_back(pair<IdString, int>(portname, portbit));
	}
};

Aig::Aig(Cell *cell)
{
	if (cell->type[0] != '$')
		return;

	AigMaker mk(this);
	name = cell->type.str();

	cell->parameters.sort();
	for (auto p : cell->parameters)
		name += stringf(":%d", p.second.as_int());

	if (cell->type == "$_AND_" || cell->type == "$_NAND_")
	{
		int A = mk.inport("A", 0);
		int B = mk.inport("B", 0);
		int Y = mk.gate(A, B, cell->type == "$_NAND_");
		mk.outport(Y, "Y", 0);
		return;
	}

	if (cell->type == "$_OR_" || cell->type == "$_NOR_")
	{
		int A = mk.inport("A", 0, true);
		int B = mk.inport("B", 0, true);
		int Y = mk.gate(A, B, cell->type == "$_OR_");
		mk.outport(Y, "Y", 0);
		return;
	}

	name.clear();
}

YOSYS_NAMESPACE_END
