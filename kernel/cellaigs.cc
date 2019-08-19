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

AigNode::AigNode()
{
	portbit = -1;
	inverter = false;
	left_parent = -1;
	right_parent = -1;
}

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

bool Aig::operator==(const Aig &other) const
{
	return name == other.name;
}

unsigned int Aig::hash() const
{
	return hash_ops<std::string>::hash(name);
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

	int node2index(const AigNode &node)
	{
		if (node.left_parent > node.right_parent) {
			AigNode n(node);
			std::swap(n.left_parent, n.right_parent);
			return node2index(n);
		}

		if (!aig_indices.count(node)) {
			aig_indices.expect(node, GetSize(aig->nodes));
			aig->nodes.push_back(node);
		}

		return aig_indices.at(node);
	}

	int bool_node(bool value)
	{
		AigNode node;
		node.inverter = value;
		return node2index(node);
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
		return node2index(node);
	}

	vector<int> inport_vec(IdString portname, int width)
	{
		vector<int> vec;
		for (int i = 0; i < width; i++)
			vec.push_back(inport(portname, i));
		return vec;
	}

	int not_inport(IdString portname, int portbit = 0)
	{
		return inport(portname, portbit, true);
	}

	int not_gate(int A)
	{
		AigNode node(aig_indices[A]);
		node.outports.clear();
		node.inverter = !node.inverter;
		return node2index(node);
	}

	int and_gate(int A, int B, bool inverter = false)
	{
		if (A == B)
			return inverter ? not_gate(A) : A;

		const AigNode &nA = aig_indices[A];
		const AigNode &nB = aig_indices[B];

		AigNode nB_inv(nB);
		nB_inv.inverter = !nB_inv.inverter;

		if (nA == nB_inv)
			return bool_node(inverter);

		bool nA_bool = nA.portbit < 0 && nA.left_parent < 0 && nA.right_parent < 0;
		bool nB_bool = nB.portbit < 0 && nB.left_parent < 0 && nB.right_parent < 0;

		if (nA_bool && nB_bool) {
			bool bA = nA.inverter;
			bool bB = nB.inverter;
			return bool_node(inverter != (bA && bB));
		}

		if (nA_bool) {
			bool bA = nA.inverter;
			if (inverter)
				return bA ? not_gate(B) : bool_node(true);
			return bA ? B : bool_node(false);
		}

		if (nB_bool) {
			bool bB = nB.inverter;
			if (inverter)
				return bB ? not_gate(A) : bool_node(true);
			return bB ? A : bool_node(false);
		}

		AigNode node;
		node.inverter = inverter;
		node.left_parent = A;
		node.right_parent = B;
		return node2index(node);
	}

	int nand_gate(int A, int B)
	{
		return and_gate(A, B, true);
	}

	int or_gate(int A, int B)
	{
		return nand_gate(not_gate(A), not_gate(B));
	}

	int nor_gate(int A, int B)
	{
		return and_gate(not_gate(A), not_gate(B));
	}

	int xor_gate(int A, int B)
	{
		return nor_gate(and_gate(A, B), nor_gate(A, B));
	}

	int xnor_gate(int A, int B)
	{
		return or_gate(and_gate(A, B), nor_gate(A, B));
	}

	int andnot_gate(int A, int B)
	{
		return and_gate(A, not_gate(B));
	}

	int ornot_gate(int A, int B)
	{
		return or_gate(A, not_gate(B));
	}

	int mux_gate(int A, int B, int S)
	{
		return or_gate(and_gate(A, not_gate(S)), and_gate(B, S));
	}

	vector<int> adder(const vector<int> &A, const vector<int> &B, int carry, vector<int> *X = nullptr, vector<int> *CO = nullptr)
	{
		vector<int> Y(GetSize(A));
		log_assert(GetSize(A) == GetSize(B));
		for (int i = 0; i < GetSize(A); i++) {
			Y[i] = xor_gate(xor_gate(A[i], B[i]), carry);
			carry = or_gate(and_gate(A[i], B[i]), and_gate(or_gate(A[i], B[i]), carry));
			if (X != nullptr)
				X->at(i) = xor_gate(A[i], B[i]);
			if (CO != nullptr)
				CO->at(i) = carry;
		}
		return Y;
	}

	void outport(int node, IdString portname, int portbit = 0)
	{
		if (portbit < GetSize(cell->getPort(portname)))
			aig->nodes.at(node).outports.push_back(pair<IdString, int>(portname, portbit));
	}

	void outport_bool(int node, IdString portname)
	{
		outport(node, portname);
		for (int i = 1; i < GetSize(cell->getPort(portname)); i++)
			outport(bool_node(false), portname, i);
	}

	void outport_vec(const vector<int> &vec, IdString portname)
	{
		for (int i = 0; i < GetSize(vec); i++)
			outport(vec.at(i), portname, i);
	}
};

Aig::Aig(Cell *cell)
{
	if (cell->type[0] != '$')
		return;

	AigMaker mk(this, cell);
	name = cell->type.str();

	string mkname_last;
	bool mkname_a_signed = false;
	bool mkname_b_signed = false;
	bool mkname_is_signed = false;

	cell->parameters.sort();
	for (auto p : cell->parameters)
	{
		if (p.first == ID(A_WIDTH) && mkname_a_signed) {
			name = mkname_last + stringf(":%d%c", p.second.as_int(), mkname_is_signed ? 'S' : 'U');
		} else if (p.first == ID(B_WIDTH) && mkname_b_signed) {
			name = mkname_last + stringf(":%d%c", p.second.as_int(), mkname_is_signed ? 'S' : 'U');
		} else {
			mkname_last = name;
			name += stringf(":%d", p.second.as_int());
		}

		mkname_a_signed = false;
		mkname_b_signed = false;
		mkname_is_signed = false;
		if (p.first == ID(A_SIGNED)) {
			mkname_a_signed = true;
			mkname_is_signed = p.second.as_bool();
		}
		if (p.first == ID(B_SIGNED)) {
			mkname_b_signed = true;
			mkname_is_signed = p.second.as_bool();
		}
	}

	if (cell->type.in(ID($not), ID($_NOT_), ID($pos), ID($_BUF_)))
	{
		for (int i = 0; i < GetSize(cell->getPort(ID::Y)); i++) {
			int A = mk.inport(ID::A, i);
			int Y = cell->type.in(ID($not), ID($_NOT_)) ? mk.not_gate(A) : A;
			mk.outport(Y, ID::Y, i);
		}
		goto optimize;
	}

	if (cell->type.in(ID($and), ID($_AND_), ID($_NAND_), ID($or), ID($_OR_), ID($_NOR_), ID($xor), ID($xnor), ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_)))
	{
		for (int i = 0; i < GetSize(cell->getPort(ID::Y)); i++) {
			int A = mk.inport(ID::A, i);
			int B = mk.inport(ID::B, i);
			int Y = cell->type.in(ID($and), ID($_AND_))   ? mk.and_gate(A, B) :
			        cell->type.in(ID($_NAND_))          ? mk.nand_gate(A, B) :
			        cell->type.in(ID($or), ID($_OR_))     ? mk.or_gate(A, B) :
			        cell->type.in(ID($_NOR_))           ? mk.nor_gate(A, B) :
			        cell->type.in(ID($xor), ID($_XOR_))   ? mk.xor_gate(A, B) :
			        cell->type.in(ID($xnor), ID($_XNOR_)) ? mk.xnor_gate(A, B) :
			        cell->type.in(ID($_ANDNOT_))        ? mk.andnot_gate(A, B) :
			        cell->type.in(ID($_ORNOT_))         ? mk.ornot_gate(A, B) : -1;
			mk.outport(Y, ID::Y, i);
		}
		goto optimize;
	}

	if (cell->type.in(ID($mux), ID($_MUX_)))
	{
		int S = mk.inport(ID(S));
		for (int i = 0; i < GetSize(cell->getPort(ID::Y)); i++) {
			int A = mk.inport(ID::A, i);
			int B = mk.inport(ID::B, i);
			int Y = mk.mux_gate(A, B, S);
			if (cell->type == ID($_NMUX_))
				Y = mk.not_gate(Y);
			mk.outport(Y, ID::Y, i);
		}
		goto optimize;
	}

	if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool)))
	{
		int Y = mk.inport(ID::A, 0);
		for (int i = 1; i < GetSize(cell->getPort(ID::A)); i++) {
			int A = mk.inport(ID::A, i);
			if (cell->type == ID($reduce_and))  Y = mk.and_gate(A, Y);
			if (cell->type == ID($reduce_or))   Y = mk.or_gate(A, Y);
			if (cell->type == ID($reduce_bool)) Y = mk.or_gate(A, Y);
			if (cell->type == ID($reduce_xor))  Y = mk.xor_gate(A, Y);
			if (cell->type == ID($reduce_xnor)) Y = mk.xor_gate(A, Y);
		}
		if (cell->type == ID($reduce_xnor))
			Y = mk.not_gate(Y);
		mk.outport(Y, ID::Y, 0);
		for (int i = 1; i < GetSize(cell->getPort(ID::Y)); i++)
			mk.outport(mk.bool_node(false), ID::Y, i);
		goto optimize;
	}

	if (cell->type.in(ID($logic_not), ID($logic_and), ID($logic_or)))
	{
		int A = mk.inport(ID::A, 0), Y = -1;
		for (int i = 1; i < GetSize(cell->getPort(ID::A)); i++)
			A = mk.or_gate(mk.inport(ID::A, i), A);
		if (cell->type.in(ID($logic_and), ID($logic_or))) {
			int B = mk.inport(ID::B, 0);
			for (int i = 1; i < GetSize(cell->getPort(ID::B)); i++)
				B = mk.or_gate(mk.inport(ID::B, i), B);
			if (cell->type == ID($logic_and)) Y = mk.and_gate(A, B);
			if (cell->type == ID($logic_or))  Y = mk.or_gate(A, B);
		} else {
			if (cell->type == ID($logic_not)) Y = mk.not_gate(A);
		}
		mk.outport_bool(Y, ID::Y);
		goto optimize;
	}

	if (cell->type.in(ID($add), ID($sub)))
	{
		int width = GetSize(cell->getPort(ID::Y));
		vector<int> A = mk.inport_vec(ID::A, width);
		vector<int> B = mk.inport_vec(ID::B, width);
		int carry = mk.bool_node(false);
		if (cell->type == ID($sub)) {
			for (auto &n : B)
				n = mk.not_gate(n);
			carry = mk.not_gate(carry);
		}
		vector<int> Y = mk.adder(A, B, carry);
		mk.outport_vec(Y, ID::Y);
		goto optimize;
	}

	if (cell->type == ID($alu))
	{
		int width = GetSize(cell->getPort(ID::Y));
		vector<int> A = mk.inport_vec(ID::A, width);
		vector<int> B = mk.inport_vec(ID::B, width);
		int carry = mk.inport(ID(CI));
		int binv = mk.inport(ID(BI));
		for (auto &n : B)
			n = mk.xor_gate(n, binv);
		vector<int> X(width), CO(width);
		vector<int> Y = mk.adder(A, B, carry, &X, &CO);
		for (int i = 0; i < width; i++)
			X[i] = mk.xor_gate(A[i], B[i]);
		mk.outport_vec(Y, ID::Y);
		mk.outport_vec(X, ID(X));
		mk.outport_vec(CO, ID(CO));
		goto optimize;
	}

	if (cell->type.in(ID($eq), ID($ne)))
	{
		int width = max(GetSize(cell->getPort(ID::A)), GetSize(cell->getPort(ID::B)));
		vector<int> A = mk.inport_vec(ID::A, width);
		vector<int> B = mk.inport_vec(ID::B, width);
		int Y = mk.bool_node(false);
		for (int i = 0; i < width; i++)
			Y = mk.or_gate(Y, mk.xor_gate(A[i], B[i]));
		if (cell->type == ID($eq))
			Y = mk.not_gate(Y);
		mk.outport_bool(Y, ID::Y);
		goto optimize;
	}

	if (cell->type == ID($_AOI3_))
	{
		int A = mk.inport(ID::A);
		int B = mk.inport(ID::B);
		int C = mk.inport(ID(C));
		int Y = mk.nor_gate(mk.and_gate(A, B), C);
		mk.outport(Y, ID::Y);
		goto optimize;
	}

	if (cell->type == ID($_OAI3_))
	{
		int A = mk.inport(ID::A);
		int B = mk.inport(ID::B);
		int C = mk.inport(ID(C));
		int Y = mk.nand_gate(mk.or_gate(A, B), C);
		mk.outport(Y, ID::Y);
		goto optimize;
	}

	if (cell->type == ID($_AOI4_))
	{
		int A = mk.inport(ID::A);
		int B = mk.inport(ID::B);
		int C = mk.inport(ID(C));
		int D = mk.inport(ID(D));
		int Y = mk.nor_gate(mk.and_gate(A, B), mk.and_gate(C, D));
		mk.outport(Y, ID::Y);
		goto optimize;
	}

	if (cell->type == ID($_OAI4_))
	{
		int A = mk.inport(ID::A);
		int B = mk.inport(ID::B);
		int C = mk.inport(ID(C));
		int D = mk.inport(ID(D));
		int Y = mk.nand_gate(mk.or_gate(A, B), mk.or_gate(C, D));
		mk.outport(Y, ID::Y);
		goto optimize;
	}

	name.clear();
	return;

optimize:;
	pool<int> used_old_ids;
	vector<AigNode> new_nodes;
	dict<int, int> old_to_new_ids;
	old_to_new_ids[-1] = -1;

	for (int i = GetSize(nodes)-1; i >= 0; i--) {
		if (!nodes[i].outports.empty())
			used_old_ids.insert(i);
		if (!used_old_ids.count(i))
			continue;
		if (nodes[i].left_parent >= 0)
			used_old_ids.insert(nodes[i].left_parent);
		if (nodes[i].right_parent >= 0)
			used_old_ids.insert(nodes[i].right_parent);
	}

	for (int i = 0; i < GetSize(nodes); i++) {
		if (!used_old_ids.count(i))
			continue;
		nodes[i].left_parent = old_to_new_ids.at(nodes[i].left_parent);
		nodes[i].right_parent = old_to_new_ids.at(nodes[i].right_parent);
		old_to_new_ids[i] = GetSize(new_nodes);
		new_nodes.push_back(nodes[i]);
	}

	new_nodes.swap(nodes);
}

YOSYS_NAMESPACE_END
