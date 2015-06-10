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
	Cell *cell;
	idict<AigNode> aig_indices;

	int the_true_node;
	int the_false_node;

	AigMaker(Aig *aig, Cell *cell) : aig(aig), cell(cell)
	{
		the_true_node = -1;
		the_false_node = -1;
	}

	int bool_node(bool value)
	{
		AigNode node;
		node.portbit = -1;
		node.inverter = !value;
		node.left_parent = -1;
		node.right_parent = -1;

		if (!aig_indices.count(node)) {
			aig_indices.expect(node, GetSize(aig->nodes));
			aig->nodes.push_back(node);
		}

		return aig_indices.at(node);
	}

	int inport(IdString portname, int portbit = 0, bool inverter = false)
	{
		if (portbit >= GetSize(cell->getPort(portname))) {
			if (cell->parameters.count(portname.str() + "_SIGNED") && cell->getParam(portname.str() + "_SIGNED").as_bool())
				return inport(portname, GetSize(cell->getPort(portname))-1, inverter);
			return bool_node(inverter);
		}

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

	int not_inport(IdString portname, int portbit = 0)
	{
		return inport(portname, portbit, true);
	}

	int and_gate(int left_parent, int right_parent, bool inverter = false)
	{
		if (left_parent > right_parent)
			std::swap(left_parent, right_parent);

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

	int nand_gate(int left_parent, int right_parent)
	{
		return and_gate(left_parent, right_parent, true);
	}

	void outport(int node, IdString portname, int portbit = 0)
	{
		if (portbit < GetSize(cell->getPort(portname)))
			aig->nodes.at(node).outports.push_back(pair<IdString, int>(portname, portbit));
	}
};

Aig::Aig(Cell *cell)
{
	if (cell->type[0] != '$')
		return;

	AigMaker mk(this, cell);
	name = cell->type.str();

	cell->parameters.sort();
	for (auto p : cell->parameters)
		name += stringf(":%d", p.second.as_int());

	if (cell->type.in("$and", "$_AND_", "$_NAND_"))
	{
		for (int i = 0; i < GetSize(cell->getPort("\\Y")); i++) {
			int A = mk.inport("\\A", i);
			int B = mk.inport("\\B", i);
			int Y = mk.and_gate(A, B, cell->type == "$_NAND_");
			mk.outport(Y, "\\Y", i);
		}
		return;
	}

	if (cell->type.in("$or", "$_OR_", "$_NOR_"))
	{
		for (int i = 0; i < GetSize(cell->getPort("\\Y")); i++) {
			int A = mk.not_inport("\\A", i);
			int B = mk.not_inport("\\B", i);
			int Y = mk.and_gate(A, B, cell->type != "$_NOR_");
			mk.outport(Y, "\\Y", i);
		}
		return;
	}

	if (cell->type.in("$xor", "$xnor", "$_XOR_", "$_XNOR_"))
	{
		for (int i = 0; i < GetSize(cell->getPort("\\Y")); i++) {
			int A = mk.inport("\\A", i);
			int B = mk.inport("\\B", i);
			int NA = mk.not_inport("\\A", i);
			int NB = mk.not_inport("\\B", i);
			int NOT_AB = mk.nand_gate(A, B);
			int NOT_NAB = mk.nand_gate(NA, NB);
			int Y = mk.and_gate(NOT_AB, NOT_NAB, !cell->type.in("$xor", "$_XOR_"));
			mk.outport(Y, "\\Y", i);
		}
		return;
	}

	if (cell->type.in("$mux", "$_MUX_"))
	{
		int S = mk.inport("\\S");
		int NS = mk.not_inport("\\S");
		for (int i = 0; i < GetSize(cell->getPort("\\Y")); i++) {
			int A = mk.inport("\\A", i);
			int B = mk.inport("\\B", i);
			int NOT_SB = mk.nand_gate(S, B);
			int NOT_NSA = mk.nand_gate(NS, A);
			int Y = mk.nand_gate(NOT_SB, NOT_NSA);
			mk.outport(Y, "\\Y", i);
		}
		return;
	}

	if (cell->type == "$_AOI3_")
	{
		int A = mk.inport("\\A");
		int B = mk.inport("\\B");
		int NC = mk.not_inport("\\C");
		int NOT_AB = mk.nand_gate(A, B);
		int Y = mk.and_gate(NOT_AB, NC);
		mk.outport(Y, "\\Y");
		return;
	}

	if (cell->type == "$_OAI3_")
	{
		int NA = mk.not_inport("\\A");
		int NB = mk.not_inport("\\B");
		int C = mk.inport("\\C");
		int NOT_NAB = mk.nand_gate(NA, NB);
		int Y = mk.nand_gate(NOT_NAB, C);
		mk.outport(Y, "\\Y");
		return;
	}

	if (cell->type == "$_AOI4_")
	{
		int A = mk.inport("\\A");
		int B = mk.inport("\\B");
		int C = mk.inport("\\C");
		int D = mk.inport("\\D");
		int NOT_AB = mk.nand_gate(A, B);
		int NOT_CD = mk.nand_gate(C, D);
		int Y = mk.and_gate(NOT_AB, NOT_CD);
		mk.outport(Y, "\\Y");
		return;
	}

	if (cell->type == "$_OAI4_")
	{
		int NA = mk.not_inport("\\A");
		int NB = mk.not_inport("\\B");
		int NC = mk.not_inport("\\C");
		int ND = mk.not_inport("\\D");
		int NOT_NAB = mk.nand_gate(NA, NB);
		int NOT_NCD = mk.nand_gate(NC, ND);
		int Y = mk.nand_gate(NOT_NAB, NOT_NCD);
		mk.outport(Y, "\\Y");
		return;
	}

	name.clear();
}

YOSYS_NAMESPACE_END
