/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
 *  ---
 *
 *  This is the AST frontend library.
 *
 *  The AST frontend library is not a frontend on it's own but provides a
 *  generic abstract syntax tree (AST) abstraction for HDL code and can be
 *  used by HDL frontends. See "ast.h" for an overview of the API and the
 *  Verilog frontend for an usage example.
 *
 */

#include "kernel/log.h"
#include "libs/sha1/sha1.h"
#include "frontends/verilog/verilog_frontend.h"
#include "ast.h"

#include <sstream>
#include <stdarg.h>
#include <stdlib.h>
#include <math.h>
// For std::gcd in C++17
// #include <numeric>

YOSYS_NAMESPACE_BEGIN

using namespace AST;
using namespace AST_INTERNAL;

// gcd computed by Euclidian division.
// To be replaced by C++17 std::gcd
template<class I> I gcd(I a, I b) {
	while (b != 0) {
		I tmp = b;
		b = a%b;
		a = tmp;
	}
	return std::abs(a);
}

void AstNode::set_in_lvalue_flag(bool flag, bool no_descend)
{
	if (flag != in_lvalue_from_above) {
		in_lvalue_from_above = flag;
		if (!no_descend)
			fixup_hierarchy_flags();
	}
}

void AstNode::set_in_param_flag(bool flag, bool no_descend)
{
	if (flag != in_param_from_above) {
		in_param_from_above = flag;
		if (!no_descend)
			fixup_hierarchy_flags();
	}
}

void AstNode::fixup_hierarchy_flags(bool force_descend)
{
	// With forced descend, we disable the implicit
	// descend from within the set_* functions, instead
	// we do an explicit descend at the end of this function

	in_param = in_param_from_above;

	switch (type) {
	case AST_PARAMETER:
	case AST_LOCALPARAM:
	case AST_DEFPARAM:
	case AST_PARASET:
	case AST_PREFIX:
		in_param = true;
		for (auto child : children)
			child->set_in_param_flag(true, force_descend);
		break;

	case AST_REPLICATE:
	case AST_WIRE:
	case AST_GENIF:
	case AST_GENCASE:
		for (auto child : children)
			child->set_in_param_flag(in_param, force_descend);
		if (children.size() >= 1)
			children[0]->set_in_param_flag(true, force_descend);
		break;

	case AST_GENFOR:
	case AST_FOR:
		for (auto child : children)
			child->set_in_param_flag(in_param, force_descend);
		if (children.size() >= 2)
			children[1]->set_in_param_flag(true, force_descend);
		break;

	default:
		in_param = in_param_from_above;
		for (auto child : children)
			child->set_in_param_flag(in_param, force_descend);
	}

	for (auto attr : attributes)
		attr.second->set_in_param_flag(true, force_descend);

	in_lvalue = in_lvalue_from_above;

	switch (type) {
	case AST_ASSIGN:
	case AST_ASSIGN_EQ:
	case AST_ASSIGN_LE:
		if (children.size() >= 1)
			children[0]->set_in_lvalue_flag(true, force_descend);
		if (children.size() >= 2)
			children[1]->set_in_lvalue_flag(in_lvalue, force_descend);
		break;

	default:
		for (auto child : children)
			child->set_in_lvalue_flag(in_lvalue, force_descend);
	}

	if (force_descend) {
		for (auto child : children)
			child->fixup_hierarchy_flags(true);
		for (auto attr : attributes)
			attr.second->fixup_hierarchy_flags(true);
	}
}

// Process a format string and arguments for $display, $write, $sprintf, etc

Fmt AstNode::processFormat(int stage, bool sformat_like, int default_base, size_t first_arg_at, bool may_fail) {
	std::vector<VerilogFmtArg> args;
	for (size_t index = first_arg_at; index < children.size(); index++) {
		AstNode *node_arg = children[index];
		while (node_arg->simplify(true, stage, -1, false)) { }

		VerilogFmtArg arg = {};
		arg.filename = filename;
		arg.first_line = location.first_line;
		if (node_arg->type == AST_CONSTANT && node_arg->is_string) {
			arg.type = VerilogFmtArg::STRING;
			arg.str = node_arg->bitsAsConst().decode_string();
			// and in case this will be used as an argument...
			arg.sig = node_arg->bitsAsConst();
			arg.signed_ = false;
		} else if (node_arg->type == AST_IDENTIFIER && node_arg->str == "$time") {
			arg.type = VerilogFmtArg::TIME;
		} else if (node_arg->type == AST_IDENTIFIER && node_arg->str == "$realtime") {
			arg.type = VerilogFmtArg::TIME;
			arg.realtime = true;
		} else if (node_arg->type == AST_CONSTANT) {
			arg.type = VerilogFmtArg::INTEGER;
			arg.sig = node_arg->bitsAsConst();
			arg.signed_ = node_arg->is_signed;
		} else if (may_fail) {
			log_file_info(filename, location.first_line, "Skipping system task `%s' with non-constant argument at position %zu.\n", str.c_str(), index + 1);
			return Fmt();
		} else {
			log_file_error(filename, location.first_line, "Failed to evaluate system task `%s' with non-constant argument at position %zu.\n", str.c_str(), index + 1);
		}
		args.push_back(arg);
	}

	Fmt fmt = {};
	fmt.parse_verilog(args, sformat_like, default_base, /*task_name=*/str, current_module->name);
	return fmt;
}

void AstNode::annotateTypedEnums(AstNode *template_node)
{
	//check if enum
	if (template_node->attributes.count(ID::enum_type)) {
		//get reference to enum node:
		std::string enum_type = template_node->attributes[ID::enum_type]->str.c_str();
		//			log("enum_type=%s (count=%lu)\n", enum_type.c_str(), current_scope.count(enum_type));
		//			log("current scope:\n");
		//			for (auto &it : current_scope)
		//				log("  %s\n", it.first.c_str());
		log_assert(current_scope.count(enum_type) == 1);
		AstNode *enum_node = current_scope.at(enum_type);
		log_assert(enum_node->type == AST_ENUM);
		while (enum_node->simplify(true, 1, -1, false)) { }
		//get width from 1st enum item:
		log_assert(enum_node->children.size() >= 1);
		AstNode *enum_item0 = enum_node->children[0];
		log_assert(enum_item0->type == AST_ENUM_ITEM);
		int width;
		if (!enum_item0->range_valid)
			width = 1;
		else if (enum_item0->range_swapped)
			width = enum_item0->range_right - enum_item0->range_left + 1;
		else
			width = enum_item0->range_left - enum_item0->range_right + 1;
		log_assert(width > 0);
		//add declared enum items:
		for (auto enum_item : enum_node->children){
			log_assert(enum_item->type == AST_ENUM_ITEM);
			//get is_signed
			bool is_signed;
			if (enum_item->children.size() == 1){
				is_signed = false;
			} else if (enum_item->children.size() == 2){
				log_assert(enum_item->children[1]->type == AST_RANGE);
				is_signed = enum_item->children[1]->is_signed;
			} else {
				log_error("enum_item children size==%zu, expected 1 or 2 for %s (%s)\n",
						  (size_t) enum_item->children.size(),
						  enum_item->str.c_str(), enum_node->str.c_str()
				);
			}
			//start building attribute string
			std::string enum_item_str = "\\enum_value_";
			//get enum item value
			if(enum_item->children[0]->type != AST_CONSTANT){
				log_error("expected const, got %s for %s (%s)\n",
						  type2str(enum_item->children[0]->type).c_str(),
						  enum_item->str.c_str(), enum_node->str.c_str()
						);
			}
			RTLIL::Const val = enum_item->children[0]->bitsAsConst(width, is_signed);
			enum_item_str.append(val.as_string());
			//set attribute for available val to enum item name mappings
			set_attribute(enum_item_str.c_str(), mkconst_str(enum_item->str));
		}
	}
}

static AstNode *make_range(int left, int right, bool is_signed = false)
{
	// generate a pre-validated range node for a fixed signal range.
	auto range = new AstNode(AST_RANGE);
	range->range_left = left;
	range->range_right = right;
	range->range_valid = true;
	range->children.push_back(AstNode::mkconst_int(left, true));
	range->children.push_back(AstNode::mkconst_int(right, true));
	range->is_signed = is_signed;
	return range;
}

static int range_width(AstNode *node, AstNode *rnode)
{
	log_assert(rnode->type==AST_RANGE);
	if (!rnode->range_valid) {
		node->input_error("Size must be constant in packed struct/union member %s\n", node->str.c_str());

	}
	// note: range swapping has already been checked for
	return rnode->range_left - rnode->range_right + 1;
}

[[noreturn]] static void struct_array_packing_error(AstNode *node)
{
	node->input_error("Unpacked array in packed struct/union member %s\n", node->str.c_str());
}

static void save_struct_range_dimensions(AstNode *node, AstNode *rnode)
{
	node->multirange_dimensions.push_back(rnode->range_right);
	node->multirange_dimensions.push_back(range_width(node, rnode));
	node->multirange_swapped.push_back(rnode->range_swapped);
}

static int get_struct_range_offset(AstNode *node, int dimension)
{
	return node->multirange_dimensions[2*dimension];
}

static int get_struct_range_width(AstNode *node, int dimension)
{
	return node->multirange_dimensions[2*dimension + 1];
}

static int size_packed_struct(AstNode *snode, int base_offset)
{
	// Struct members will be laid out in the structure contiguously from left to right.
	// Union members all have zero offset from the start of the union.
	// Determine total packed size and assign offsets.  Store these in the member node.
	bool is_union = (snode->type == AST_UNION);
	int offset = 0;
	int packed_width = -1;
	// examine members from last to first
	for (auto it = snode->children.rbegin(); it != snode->children.rend(); ++it) {
		auto node = *it;
		int width;
		if (node->type == AST_STRUCT || node->type == AST_UNION) {
			// embedded struct or union
			width = size_packed_struct(node, base_offset + offset);
			// set range of struct
			node->range_right = base_offset + offset;
			node->range_left = base_offset + offset + width - 1;
			node->range_valid = true;
		}
		else {
			log_assert(node->type == AST_STRUCT_ITEM);
			if (node->children.size() > 0 && node->children[0]->type == AST_RANGE) {
				// member width e.g. bit [7:0] a
				width = range_width(node, node->children[0]);
				if (node->children.size() == 2) {
					// Unpacked array. Note that this is a Yosys extension; only packed data types
					// and integer data types are allowed in packed structs / unions in SystemVerilog.
					if (node->children[1]->type == AST_RANGE) {
						// Unpacked array, e.g. bit [63:0] a [0:3]
						auto rnode = node->children[1];
						if (rnode->children.size() == 1) {
							// C-style array size, e.g. bit [63:0] a [4]
							node->multirange_dimensions.push_back(0);
							node->multirange_dimensions.push_back(rnode->range_left);
							node->multirange_swapped.push_back(true);
							width *= rnode->range_left;
						} else {
							save_struct_range_dimensions(node, rnode);
							width *= range_width(node, rnode);
						}
						save_struct_range_dimensions(node, node->children[0]);
					}
					else {
						// The Yosys extension for unpacked arrays in packed structs / unions
						// only supports memories, i.e. e.g. logic [7:0] a [256] - see above.
						struct_array_packing_error(node);
					}
				} else {
					// Vector
					save_struct_range_dimensions(node, node->children[0]);
				}
				// range nodes are now redundant
				for (AstNode *child : node->children)
					delete child;
				node->children.clear();
			}
			else if (node->children.size() > 0 && node->children[0]->type == AST_MULTIRANGE) {
				// Packed array, e.g. bit [3:0][63:0] a
				if (node->children.size() != 1) {
					// The Yosys extension for unpacked arrays in packed structs / unions
					// only supports memories, i.e. e.g. logic [7:0] a [256] - see above.
					struct_array_packing_error(node);
				}
				width = 1;
				for (auto rnode : node->children[0]->children) {
					save_struct_range_dimensions(node, rnode);
					width *= range_width(node, rnode);
				}
				// range nodes are now redundant
				for (AstNode *child : node->children)
					delete child;
				node->children.clear();
			}
			else if (node->range_left < 0) {
				// 1 bit signal: bit, logic or reg
				width = 1;
			}
			else {
				// already resolved and compacted
				width = node->range_left - node->range_right + 1;
			}
			if (is_union) {
				node->range_right = base_offset;
				node->range_left = base_offset + width - 1;
			}
			else {
				node->range_right = base_offset + offset;
				node->range_left = base_offset + offset + width - 1;
			}
			node->range_valid = true;
		}
		if (is_union) {
			// check that all members have the same size
			if (packed_width == -1) {
				// first member
				packed_width = width;
			}
			else {
				if (packed_width != width)
					node->input_error("member %s of a packed union has %d bits, expecting %d\n", node->str.c_str(), width, packed_width);
			}
		}
		else {
			offset += width;
		}
	}
	return (is_union ? packed_width : offset);
}

[[noreturn]] static void struct_op_error(AstNode *node)
{
	node->input_error("Unsupported operation for struct/union member %s\n", node->str.c_str()+1);
}

static AstNode *node_int(int ival)
{
	return AstNode::mkconst_int(ival, true);
}

static AstNode *multiply_by_const(AstNode *expr_node, int stride)
{
	return new AstNode(AST_MUL, expr_node, node_int(stride));
}

static AstNode *normalize_struct_index(AstNode *expr, AstNode *member_node, int dimension)
{
	expr = expr->clone();

	int offset = get_struct_range_offset(member_node, dimension);
	if (offset) {
		expr = new AstNode(AST_SUB, expr, node_int(offset));
	}

	if (member_node->multirange_swapped[dimension]) {
		// The dimension has swapped range; swap index into the struct accordingly.
		int msb = get_struct_range_width(member_node, dimension) - 1;
		expr = new AstNode(AST_SUB, node_int(msb), expr);
	}

	return expr;
}

static AstNode *struct_index_lsb_offset(AstNode *lsb_offset, AstNode *rnode, AstNode *member_node, int dimension, int &stride)
{
	stride /= get_struct_range_width(member_node, dimension);
	auto right = normalize_struct_index(rnode->children.back(), member_node, dimension);
	auto offset = stride > 1 ? multiply_by_const(right, stride) : right;
	return lsb_offset ? new AstNode(AST_ADD, lsb_offset, offset) : offset;
}

static AstNode *struct_index_msb_offset(AstNode *lsb_offset, AstNode *rnode, AstNode *member_node, int dimension, int stride)
{
	log_assert(rnode->children.size() <= 2);

	// Offset to add to LSB
	AstNode *offset;
	if (rnode->children.size() == 1) {
		// Index, e.g. s.a[i]
		offset = node_int(stride - 1);
	}
	else {
		// rnode->children.size() == 2
		// Slice, e.g. s.a[i:j]
		auto left = normalize_struct_index(rnode->children[0], member_node, dimension);
		auto right = normalize_struct_index(rnode->children[1], member_node, dimension);
		offset = new AstNode(AST_SUB, left, right);
		if (stride > 1) {
			// offset = (msb - lsb + 1)*stride - 1
			auto slice_width = new AstNode(AST_ADD, offset, node_int(1));
			offset = new AstNode(AST_SUB, multiply_by_const(slice_width, stride), node_int(1));
		}
	}

	return new AstNode(AST_ADD, lsb_offset, offset);
}


AstNode *AST::make_struct_member_range(AstNode *node, AstNode *member_node)
{
	// Work out the range in the packed array that corresponds to a struct member
	// taking into account any range operations applicable to the current node
	// such as array indexing or slicing
	int range_left = member_node->range_left;
	int range_right = member_node->range_right;
	if (node->children.empty()) {
		// no range operations apply, return the whole width
		return make_range(range_left - range_right, 0);
	}

	if (node->children.size() != 1) {
		struct_op_error(node);
	}

	// Range operations
	auto rnode = node->children[0];
	AstNode *lsb_offset = NULL;
	int stride = range_left - range_right + 1;
	size_t i = 0;

	// Calculate LSB offset for the final index / slice
	if (rnode->type == AST_RANGE) {
		lsb_offset = struct_index_lsb_offset(lsb_offset, rnode, member_node, i, stride);
	}
	else if (rnode->type == AST_MULTIRANGE) {
		// Add offset for each dimension
		auto mrnode = rnode;
		for (i = 0; i < mrnode->children.size(); i++) {
			rnode = mrnode->children[i];
			lsb_offset = struct_index_lsb_offset(lsb_offset, rnode, member_node, i, stride);
		}
		i--;  // Step back to the final index / slice
	}
	else {
		struct_op_error(node);
	}

	// Calculate MSB offset for the final index / slice
	auto msb_offset = struct_index_msb_offset(lsb_offset->clone(), rnode, member_node, i, stride);

	return new AstNode(AST_RANGE, msb_offset, lsb_offset);
}

AstNode *AST::get_struct_member(const AstNode *node)
{
	AST::AstNode *member_node;
	if (node->attributes.count(ID::wiretype) && (member_node = node->attributes.at(ID::wiretype)) &&
	    (member_node->type == AST_STRUCT_ITEM || member_node->type == AST_STRUCT || member_node->type == AST_UNION))
	{
		return member_node;
	}
	return NULL;
}

static void add_members_to_scope(AstNode *snode, std::string name)
{
	// add all the members in a struct or union to local scope
	// in case later referenced in assignments
	log_assert(snode->type==AST_STRUCT || snode->type==AST_UNION);
	for (auto *node : snode->children) {
		auto member_name = name + "." + node->str;
		current_scope[member_name] = node;
		if (node->type != AST_STRUCT_ITEM) {
			// embedded struct or union
			add_members_to_scope(node, name + "." + node->str);
		}
	}
}

static int get_max_offset(AstNode *node)
{
	// get the width from the MS member in the struct
	// as members are laid out from left to right in the packed wire
	log_assert(node->type==AST_STRUCT || node->type==AST_UNION);
	while (node->type != AST_STRUCT_ITEM) {
		node = node->children[0];
	}
	return node->range_left;
}

static AstNode *make_packed_struct(AstNode *template_node, std::string &name, decltype(AstNode::attributes) &attributes)
{
	// create a wire for the packed struct
	int offset = get_max_offset(template_node);
	auto wnode = new AstNode(AST_WIRE, make_range(offset, 0));
	wnode->str = name;
	wnode->is_logic = true;
	wnode->range_valid = true;
	wnode->is_signed = template_node->is_signed;
	for (auto &pair : attributes) {
		wnode->set_attribute(pair.first, pair.second->clone());
	}
	// make sure this node is the one in scope for this name
	current_scope[name] = wnode;
	// add all the struct members to scope under the wire's name
	add_members_to_scope(template_node, name);
	return wnode;
}

// check if a node or its children contains an assignment to the given variable
static bool node_contains_assignment_to(const AstNode* node, const AstNode* var)
{
	if (node->type == AST_ASSIGN_EQ || node->type == AST_ASSIGN_LE) {
		// current node is iteslf an assignment
		log_assert(node->children.size() >= 2);
		const AstNode* lhs = node->children[0];
		if (lhs->type == AST_IDENTIFIER && lhs->str == var->str)
			return false;
	}
	for (const AstNode* child : node->children) {
		// if this child shadows the given variable
		if (child != var && child->str == var->str && child->type == AST_WIRE)
			break; // skip the remainder of this block/scope
		// depth-first short circuit
		if (!node_contains_assignment_to(child, var))
			return false;
	}
	return true;
}

static std::string prefix_id(const std::string &prefix, const std::string &str)
{
	log_assert(!prefix.empty() && (prefix.front() == '$' || prefix.front() == '\\'));
	log_assert(!str.empty() && (str.front() == '$' || str.front() == '\\'));
	log_assert(prefix.back() == '.');
	if (str.front() == '\\')
		return prefix + str.substr(1);
	return prefix + str;
}

// direct access to this global should be limited to the following two functions
static const RTLIL::Design *simplify_design_context = nullptr;

void AST::set_simplify_design_context(const RTLIL::Design *design)
{
	log_assert(!simplify_design_context || !design);
	simplify_design_context = design;
}

// lookup the module with the given name in the current design context
static const RTLIL::Module* lookup_module(const std::string &name)
{
	return simplify_design_context->module(name);
}

const RTLIL::Module* AstNode::lookup_cell_module()
{
	log_assert(type == AST_CELL);

	auto reprocess_after = [this] (const std::string &modname) {
		if (!attributes.count(ID::reprocess_after))
			set_attribute(ID::reprocess_after, AstNode::mkconst_str(modname));
	};

	const AstNode *celltype = nullptr;
	for (const AstNode *child : children)
		if (child->type == AST_CELLTYPE) {
			celltype = child;
			break;
		}
	log_assert(celltype != nullptr);

	const RTLIL::Module *module = lookup_module(celltype->str);
	if (!module)
		module = lookup_module("$abstract" + celltype->str);
	if (!module) {
		if (celltype->str.at(0) != '$')
			reprocess_after(celltype->str);
		return nullptr;
	}

	// build a mapping from true param name to param value
	size_t para_counter = 0;
	dict<RTLIL::IdString, RTLIL::Const> cell_params_map;
	for (AstNode *child : children) {
		if (child->type != AST_PARASET)
			continue;

		if (child->str.empty() && para_counter >= module->avail_parameters.size())
			return nullptr; // let hierarchy handle this error
		IdString paraname = child->str.empty() ? module->avail_parameters[para_counter++] : child->str;

		const AstNode *value = child->children[0];
		if (value->type != AST_REALVALUE && value->type != AST_CONSTANT)
			return nullptr; // let genrtlil handle this error
		cell_params_map[paraname] = value->asParaConst();
	}

	// put the parameters in order and generate the derived module name
	std::vector<std::pair<RTLIL::IdString, RTLIL::Const>> named_parameters;
	for (RTLIL::IdString param : module->avail_parameters) {
		auto it = cell_params_map.find(param);
		if (it != cell_params_map.end())
			named_parameters.emplace_back(it->first, it->second);
	}
	std::string modname = celltype->str;
	if (cell_params_map.size()) // not named_parameters to cover hierarchical defparams
		modname = derived_module_name(celltype->str, named_parameters);

	// try to find the resolved module
	module = lookup_module(modname);
	if (!module) {
		reprocess_after(modname);
		return nullptr;
	}
	return module;
}

// returns whether an expression contains an unbased unsized literal; does not
// check the literal exists in a self-determined context
static bool contains_unbased_unsized(const AstNode *node)
{
	if (node->type == AST_CONSTANT)
		return node->is_unsized;
	for (const AstNode *child : node->children)
		if (contains_unbased_unsized(child))
			return true;
	return false;
}

// adds a wire to the current module with the given name that matches the
// dimensions of the given wire reference
void add_wire_for_ref(const RTLIL::Wire *ref, const std::string &str)
{
	AstNode *left = AstNode::mkconst_int(ref->width - 1 + ref->start_offset, true);
	AstNode *right = AstNode::mkconst_int(ref->start_offset, true);
	if (ref->upto)
		std::swap(left, right);
	AstNode *range = new AstNode(AST_RANGE, left, right);

	AstNode *wire = new AstNode(AST_WIRE, range);
	wire->is_signed = ref->is_signed;
	wire->is_logic = true;
	wire->str = str;

	current_ast_mod->children.push_back(wire);
	current_scope[str] = wire;
}

enum class IdentUsage {
	NotReferenced, // target variable is neither read or written in the block
	Assigned, // target variable is always assigned before use
	SyncRequired, // target variable may be used before it has been assigned
};

// determines whether a local variable a block is always assigned before it is
// used, meaning the nosync attribute can automatically be added to that
// variable
static IdentUsage always_asgn_before_use(const AstNode *node, const std::string &target)
{
	// This variable has been referenced before it has necessarily been assigned
	// a value in this procedure.
	if (node->type == AST_IDENTIFIER && node->str == target)
		return IdentUsage::SyncRequired;

	// For case statements (which are also used for if/else), we check each
	// possible branch. If the variable is assigned in all branches, then it is
	// assigned, and a sync isn't required. If it used before assignment in any
	// branch, then a sync is required.
	if (node->type == AST_CASE) {
		bool all_defined = true;
		bool any_used = false;
		bool has_default = false;
		for (const AstNode *child : node->children) {
			if (child->type == AST_COND && child->children.at(0)->type == AST_DEFAULT)
				has_default = true;
			IdentUsage nested = always_asgn_before_use(child, target);
			if (nested != IdentUsage::Assigned && child->type == AST_COND)
				all_defined = false;
			if (nested == IdentUsage::SyncRequired)
				any_used = true;
		}
		if (any_used)
			return IdentUsage::SyncRequired;
		else if (all_defined && has_default)
			return IdentUsage::Assigned;
		else
			return IdentUsage::NotReferenced;
	}

	// Check if this is an assignment to the target variable. For simplicity, we
	// don't analyze sub-ranges of the variable.
	if (node->type == AST_ASSIGN_EQ) {
		const AstNode *ident = node->children.at(0);
		if (ident->type == AST_IDENTIFIER && ident->str == target)
			return IdentUsage::Assigned;
	}

	for (const AstNode *child : node->children) {
		IdentUsage nested = always_asgn_before_use(child, target);
		if (nested != IdentUsage::NotReferenced)
			return nested;
	}
	return IdentUsage::NotReferenced;
}

AstNode *AstNode::clone_at_zero()
{
	int width_hint;
	bool sign_hint;
	AstNode *pointee;

	switch (type) {
	case AST_IDENTIFIER:
		if (id2ast)
			pointee = id2ast;
		else if (current_scope.count(str))
			pointee = current_scope[str];
		else
			break;

		if (pointee->type != AST_WIRE &&
				pointee->type != AST_AUTOWIRE &&
				pointee->type != AST_MEMORY)
			break;

		YS_FALLTHROUGH;
	case AST_MEMRD:
		detectSignWidth(width_hint, sign_hint);
		return mkconst_int(0, sign_hint, width_hint);

	default:
		break;
	}

	AstNode *that = new AstNode;
	*that = *this;
	for (auto &it : that->children)
		it = it->clone_at_zero();
	for (auto &it : that->attributes)
		it.second = it.second->clone();

	that->set_in_lvalue_flag(false);
	that->set_in_param_flag(false);
	that->fixup_hierarchy_flags();

	return that;
}

static bool try_determine_range_width(AstNode *range, int &result_width)
{
	log_assert(range->type == AST_RANGE);

	if (range->children.size() == 1) {
		result_width = 1;
		return true;
	}

	AstNode *left_at_zero_ast = range->children[0]->clone_at_zero();
	AstNode *right_at_zero_ast = range->children[1]->clone_at_zero();

	while (left_at_zero_ast->simplify(true, 1, -1, false)) {}
	while (right_at_zero_ast->simplify(true, 1, -1, false)) {}

	bool ok = false;
	if (left_at_zero_ast->type == AST_CONSTANT
			&& right_at_zero_ast->type == AST_CONSTANT) {
		ok = true;
		result_width = abs(int(left_at_zero_ast->integer - right_at_zero_ast->integer)) + 1;
	}

	delete left_at_zero_ast;
	delete right_at_zero_ast;
	return ok;
}

static const std::string auto_nosync_prefix = "\\AutoNosync";

// mark a local variable in an always_comb block for automatic nosync
// consideration
static void mark_auto_nosync(AstNode *block, const AstNode *wire)
{
	log_assert(block->type == AST_BLOCK);
	log_assert(wire->type == AST_WIRE);
	block->set_attribute(auto_nosync_prefix + wire->str, AstNode::mkconst_int(1, false));
}

// block names can be prefixed with an explicit scope during elaboration
static bool is_autonamed_block(const std::string &str) {
	size_t last_dot = str.rfind('.');
	// unprefixed names: autonamed if the first char is a dollar sign
	if (last_dot == std::string::npos)
		return str.at(0) == '$'; // e.g., `$fordecl_block$1`
	// prefixed names: autonamed if the final chunk begins with a dollar sign
	return str.rfind(".$") == last_dot; // e.g., `\foo.bar.$fordecl_block$1`
}

// check a procedural block for auto-nosync markings, remove them, and add
// nosync to local variables as necessary
static void check_auto_nosync(AstNode *node)
{
	std::vector<RTLIL::IdString> attrs_to_drop;
	for (const auto& elem : node->attributes) {
		// skip attributes that don't begin with the prefix
		if (elem.first.compare(0, auto_nosync_prefix.size(),
					auto_nosync_prefix.c_str()))
			continue;

		// delete and remove the attribute once we're done iterating
		attrs_to_drop.push_back(elem.first);

		// find the wire based on the attribute
		std::string wire_name = elem.first.substr(auto_nosync_prefix.size());
		auto it = current_scope.find(wire_name);
		if (it == current_scope.end())
			continue;

		// analyze the usage of the local variable in this block
		IdentUsage ident_usage = always_asgn_before_use(node, wire_name);
		if (ident_usage != IdentUsage::Assigned)
			continue;

		// mark the wire with `nosync`
		AstNode *wire = it->second;
		log_assert(wire->type == AST_WIRE);
		wire->set_attribute(ID::nosync, AstNode::mkconst_int(1, false));
	}

	// remove the attributes we've "consumed"
	for (const RTLIL::IdString &str : attrs_to_drop) {
		auto it = node->attributes.find(str);
		delete it->second;
		node->attributes.erase(it);
	}

	// check local variables in any nested blocks
	for (AstNode *child : node->children)
		check_auto_nosync(child);
}

// convert the AST into a simpler AST that has all parameters substituted by their
// values, unrolled for-loops, expanded generate blocks, etc. when this function
// is done with an AST it can be converted into RTLIL using genRTLIL().
//
// this function also does all name resolving and sets the id2ast member of all
// nodes that link to a different node using names and lexical scoping.
bool AstNode::simplify(bool const_fold, int stage, int width_hint, bool sign_hint)
{
	static int recursion_counter = 0;
	static bool deep_recursion_warning = false;

	if (recursion_counter++ == 1000 && deep_recursion_warning) {
		log_warning("Deep recursion in AST simplifier.\nDoes this design contain overly long or deeply nested expressions, or excessive recursion?\n");
		deep_recursion_warning = false;
	}

	static bool unevaluated_tern_branch = false;

	AstNode *newNode = NULL;
	bool did_something = false;

#if 0
	log("-------------\n");
	log("AST simplify[%d] depth %d at %s:%d on %s %p:\n", stage, recursion_counter, filename.c_str(), location.first_line, type2str(type).c_str(), this);
	log("const_fold=%d, stage=%d, width_hint=%d, sign_hint=%d\n",
			int(const_fold), int(stage), int(width_hint), int(sign_hint));
	// dumpAst(NULL, "> ");
#endif

	if (stage == 0)
	{
		log_assert(type == AST_MODULE || type == AST_INTERFACE);

		deep_recursion_warning = true;
		while (simplify(const_fold, 1, width_hint, sign_hint)) { }

		if (!flag_nomem2reg && !get_bool_attribute(ID::nomem2reg))
		{
			dict<AstNode*, pool<std::string>> mem2reg_places;
			dict<AstNode*, uint32_t> mem2reg_candidates, dummy_proc_flags;
			uint32_t flags = flag_mem2reg ? AstNode::MEM2REG_FL_ALL : 0;
			mem2reg_as_needed_pass1(mem2reg_places, mem2reg_candidates, dummy_proc_flags, flags);

			pool<AstNode*> mem2reg_set;
			for (auto &it : mem2reg_candidates)
			{
				AstNode *mem = it.first;
				uint32_t memflags = it.second;
				bool this_nomeminit = flag_nomeminit;
				log_assert((memflags & ~0x00ffff00) == 0);

				if (mem->get_bool_attribute(ID::nomem2reg))
					continue;

				if (mem->get_bool_attribute(ID::nomeminit) || get_bool_attribute(ID::nomeminit))
					this_nomeminit = true;

				if (memflags & AstNode::MEM2REG_FL_FORCED)
					goto silent_activate;

				if (memflags & AstNode::MEM2REG_FL_EQ2)
					goto verbose_activate;

				if (memflags & AstNode::MEM2REG_FL_SET_ASYNC)
					goto verbose_activate;

				if ((memflags & AstNode::MEM2REG_FL_SET_INIT) && (memflags & AstNode::MEM2REG_FL_SET_ELSE) && this_nomeminit)
					goto verbose_activate;

				if (memflags & AstNode::MEM2REG_FL_CMPLX_LHS)
					goto verbose_activate;

				if ((memflags & AstNode::MEM2REG_FL_CONST_LHS) && !(memflags & AstNode::MEM2REG_FL_VAR_LHS))
					goto verbose_activate;

				// log("Note: Not replacing memory %s with list of registers (flags=0x%08lx).\n", mem->str.c_str(), long(memflags));
				continue;

			verbose_activate:
				if (mem2reg_set.count(mem) == 0) {
					std::string message = stringf("Replacing memory %s with list of registers.", mem->str.c_str());
					bool first_element = true;
					for (auto &place : mem2reg_places[it.first]) {
						message += stringf("%s%s", first_element ? " See " : ", ", place.c_str());
						first_element = false;
					}
					log_warning("%s\n", message.c_str());
				}

			silent_activate:
				// log("Note: Replacing memory %s with list of registers (flags=0x%08lx).\n", mem->str.c_str(), long(memflags));
				mem2reg_set.insert(mem);
			}

			for (auto node : mem2reg_set)
			{
				int mem_width, mem_size, addr_bits;
				node->meminfo(mem_width, mem_size, addr_bits);

				int data_range_left = node->children[0]->range_left;
				int data_range_right = node->children[0]->range_right;

				if (node->children[0]->range_swapped)
					std::swap(data_range_left, data_range_right);

				for (int i = 0; i < mem_size; i++) {
					AstNode *reg = new AstNode(AST_WIRE, new AstNode(AST_RANGE,
							mkconst_int(data_range_left, true), mkconst_int(data_range_right, true)));
					reg->str = stringf("%s[%d]", node->str.c_str(), i);
					reg->is_reg = true;
					reg->is_signed = node->is_signed;
					for (auto &it : node->attributes)
						if (it.first != ID::mem2reg)
							reg->set_attribute(it.first, it.second->clone());
					reg->filename = node->filename;
					reg->location = node->location;
					children.push_back(reg);
					while (reg->simplify(true, 1, -1, false)) { }
				}
			}

			AstNode *async_block = NULL;
			while (mem2reg_as_needed_pass2(mem2reg_set, this, NULL, async_block)) { }

			vector<AstNode*> delnodes;
			mem2reg_remove(mem2reg_set, delnodes);

			for (auto node : delnodes)
				delete node;
		}

		while (simplify(const_fold, 2, width_hint, sign_hint)) { }
		recursion_counter--;
		return false;
	}

	current_filename = filename;

	// we do not look inside a task or function
	// (but as soon as a task or function is instantiated we process the generated AST as usual)
	if (type == AST_FUNCTION || type == AST_TASK) {
		recursion_counter--;
		return false;
	}

	// deactivate all calls to non-synthesis system tasks
	// note that $display, $finish, and $stop are used for synthesis-time DRC so they're not in this list
	if ((type == AST_FCALL || type == AST_TCALL) && (str == "$strobe" || str == "$monitor" || str == "$time" ||
			str == "$dumpfile" || str == "$dumpvars" || str == "$dumpon" || str == "$dumpoff" || str == "$dumpall")) {
		log_file_warning(filename, location.first_line, "Ignoring call to system %s %s.\n", type == AST_FCALL ? "function" : "task", str.c_str());
		delete_children();
		str = std::string();
	}

	if ((type == AST_TCALL) &&
	    (str == "$display" || str == "$displayb" || str == "$displayh" || str == "$displayo" ||
	     str == "$write"   || str == "$writeb"   || str == "$writeh"   || str == "$writeo"))
	{
		if (!current_always) {
			log_file_warning(filename, location.first_line, "System task `%s' outside initial or always block is unsupported.\n", str.c_str());
			delete_children();
			str = std::string();
		} else {
			// simplify the expressions and convert them to a special cell later in genrtlil
			for (auto node : children)
				while (node->simplify(true, stage, -1, false)) {}

			if (current_always->type == AST_INITIAL && !flag_nodisplay && stage == 2) {
				int default_base = 10;
				if (str.back() == 'b')
					default_base = 2;
				else if (str.back() == 'o')
					default_base = 8;
				else if (str.back() == 'h')
					default_base = 16;

				// when $display()/$write() functions are used in an initial block, print them during synthesis
				Fmt fmt = processFormat(stage, /*sformat_like=*/false, default_base, /*first_arg_at=*/0, /*may_fail=*/true);
				if (str.substr(0, 8) == "$display")
					fmt.append_string("\n");
				log("%s", fmt.render().c_str());
			}

			return false;
		}
	}

	// activate const folding if this is anything that must be evaluated statically (ranges, parameters, attributes, etc.)
	if (type == AST_WIRE || type == AST_PARAMETER || type == AST_LOCALPARAM || type == AST_ENUM_ITEM || type == AST_DEFPARAM || type == AST_PARASET || type == AST_RANGE || type == AST_PREFIX || type == AST_TYPEDEF)
		const_fold = true;
	if (type == AST_IDENTIFIER && current_scope.count(str) > 0 && (current_scope[str]->type == AST_PARAMETER || current_scope[str]->type == AST_LOCALPARAM || current_scope[str]->type == AST_ENUM_ITEM))
		const_fold = true;

	std::map<std::string, AstNode*> backup_scope;

	// create name resolution entries for all objects with names
	// also merge multiple declarations for the same wire (e.g. "output foobar; reg foobar;")
	if (type == AST_MODULE || type == AST_INTERFACE) {
		current_scope.clear();
		std::set<std::string> existing;
		int counter = 0;
		label_genblks(existing, counter);
		std::map<std::string, AstNode*> this_wire_scope;
		for (size_t i = 0; i < children.size(); i++) {
			AstNode *node = children[i];

			if (node->type == AST_WIRE) {
				if (node->children.size() == 1 && node->children[0]->type == AST_RANGE) {
					for (auto c : node->children[0]->children) {
						if (!c->is_simple_const_expr()) {
							if (attributes.count(ID::dynports))
								delete attributes.at(ID::dynports);
							set_attribute(ID::dynports, AstNode::mkconst_int(1, true));
						}
					}
				}
				if (this_wire_scope.count(node->str) > 0) {
					AstNode *first_node = this_wire_scope[node->str];
					if (first_node->is_input && node->is_reg)
						goto wires_are_incompatible;
					if (!node->is_input && !node->is_output && node->is_reg && node->children.size() == 0)
						goto wires_are_compatible;
					if (first_node->children.size() == 0 && node->children.size() == 1 && node->children[0]->type == AST_RANGE) {
						AstNode *r = node->children[0];
						if (r->range_valid && r->range_left == 0 && r->range_right == 0) {
							delete r;
							node->children.pop_back();
						}
					}
					if (first_node->children.size() != node->children.size())
						goto wires_are_incompatible;
					for (size_t j = 0; j < node->children.size(); j++) {
						AstNode *n1 = first_node->children[j], *n2 = node->children[j];
						if (n1->type == AST_RANGE && n2->type == AST_RANGE && n1->range_valid && n2->range_valid) {
							if (n1->range_left != n2->range_left)
								goto wires_are_incompatible;
							if (n1->range_right != n2->range_right)
								goto wires_are_incompatible;
						} else if (*n1 != *n2)
							goto wires_are_incompatible;
					}
					if (first_node->range_left != node->range_left)
						goto wires_are_incompatible;
					if (first_node->range_right != node->range_right)
						goto wires_are_incompatible;
					if (first_node->port_id == 0 && (node->is_input || node->is_output))
						goto wires_are_incompatible;
				wires_are_compatible:
					if (node->is_input)
						first_node->is_input = true;
					if (node->is_output)
						first_node->is_output = true;
					if (node->is_reg)
						first_node->is_reg = true;
					if (node->is_logic)
						first_node->is_logic = true;
					if (node->is_signed)
						first_node->is_signed = true;
					for (auto &it : node->attributes) {
						if (first_node->attributes.count(it.first) > 0)
							delete first_node->attributes[it.first];
						first_node->set_attribute(it.first, it.second->clone());
					}
					children.erase(children.begin()+(i--));
					did_something = true;
					delete node;
					continue;
				wires_are_incompatible:
					if (stage > 1)
						input_error("Incompatible re-declaration of wire %s.\n", node->str.c_str());
					continue;
				}
				this_wire_scope[node->str] = node;
			}
			// these nodes appear at the top level in a module and can define names
			if (node->type == AST_PARAMETER || node->type == AST_LOCALPARAM || node->type == AST_WIRE || node->type == AST_AUTOWIRE || node->type == AST_GENVAR ||
					node->type == AST_MEMORY || node->type == AST_FUNCTION || node->type == AST_TASK || node->type == AST_DPI_FUNCTION || node->type == AST_CELL ||
					node->type == AST_TYPEDEF) {
				backup_scope[node->str] = current_scope[node->str];
				current_scope[node->str] = node;
			}
			if (node->type == AST_ENUM) {
				current_scope[node->str] = node;
				for (auto enode : node->children) {
					log_assert(enode->type==AST_ENUM_ITEM);
					if (current_scope.count(enode->str) == 0)
						current_scope[enode->str] = enode;
					else
						input_error("enum item %s already exists\n", enode->str.c_str());
				}
			}
		}
		for (size_t i = 0; i < children.size(); i++) {
			AstNode *node = children[i];
			if (node->type == AST_PARAMETER || node->type == AST_LOCALPARAM || node->type == AST_WIRE || node->type == AST_AUTOWIRE || node->type == AST_MEMORY || node->type == AST_TYPEDEF)
				while (node->simplify(true, 1, -1, false))
					did_something = true;
			if (node->type == AST_ENUM) {
				for (auto enode : node->children){
					log_assert(enode->type==AST_ENUM_ITEM);
					while (node->simplify(true, 1, -1, false))
						did_something = true;
				}
			}
		}

		for (AstNode *child : children)
			if (child->type == AST_ALWAYS &&
					child->attributes.count(ID::always_comb))
				check_auto_nosync(child);
	}

	// create name resolution entries for all objects with names
	if (type == AST_PACKAGE) {
		//add names to package scope
		for (size_t i = 0; i < children.size(); i++) {
			AstNode *node = children[i];
			// these nodes appear at the top level in a package and can define names
			if (node->type == AST_PARAMETER || node->type == AST_LOCALPARAM || node->type == AST_TYPEDEF || node->type == AST_FUNCTION || node->type == AST_TASK) {
				current_scope[node->str] = node;
			}
			if (node->type == AST_ENUM) {
				current_scope[node->str] = node;
				for (auto enode : node->children) {
					log_assert(enode->type==AST_ENUM_ITEM);
					if (current_scope.count(enode->str) == 0)
						current_scope[enode->str] = enode;
					else
						input_error("enum item %s already exists in package\n", enode->str.c_str());
				}
			}
		}
	}


	auto backup_current_block = current_block;
	auto backup_current_block_child = current_block_child;
	auto backup_current_top_block = current_top_block;
	auto backup_current_always = current_always;
	auto backup_current_always_clocked = current_always_clocked;

	if (type == AST_ALWAYS || type == AST_INITIAL)
	{
		if (current_always != nullptr)
			input_error("Invalid nesting of always blocks and/or initializations.\n");

		current_always = this;
		current_always_clocked = false;

		if (type == AST_ALWAYS)
			for (auto child : children) {
				if (child->type == AST_POSEDGE || child->type == AST_NEGEDGE)
					current_always_clocked = true;
				if (child->type == AST_EDGE && GetSize(child->children) == 1 &&
						child->children[0]->type == AST_IDENTIFIER && child->children[0]->str == "\\$global_clock")
					current_always_clocked = true;
			}
	}

	if (type == AST_CELL) {
		bool lookup_suggested = false;

		for (AstNode *child : children) {
			// simplify any parameters to constants
			if (child->type == AST_PARASET)
				while (child->simplify(true, 1, -1, false)) { }

			// look for patterns which _may_ indicate ambiguity requiring
			// resolution of the underlying module
			if (child->type == AST_ARGUMENT) {
				if (child->children.size() != 1)
					continue;
				const AstNode *value = child->children[0];
				if (value->type == AST_IDENTIFIER) {
					const AstNode *elem = value->id2ast;
					if (elem == nullptr) {
						if (current_scope.count(value->str))
							elem = current_scope.at(value->str);
						else
							continue;
					}
					if (elem->type == AST_MEMORY)
						// need to determine is the is a read or wire
						lookup_suggested = true;
					else if (elem->type == AST_WIRE && elem->is_signed && !value->children.empty())
						// this may be a fully sliced signed wire which needs
						// to be indirected to produce an unsigned connection
						lookup_suggested = true;
				}
				else if (contains_unbased_unsized(value))
					// unbased unsized literals extend to width of the context
					lookup_suggested = true;
			}
		}

		const RTLIL::Module *module = nullptr;
		if (lookup_suggested)
			module = lookup_cell_module();
		if (module) {
			size_t port_counter = 0;
			for (AstNode *child : children) {
				if (child->type != AST_ARGUMENT)
					continue;

				// determine the full name of port this argument is connected to
				RTLIL::IdString port_name;
				if (child->str.size())
					port_name = child->str;
				else {
					if (port_counter >= module->ports.size())
						input_error("Cell instance has more ports than the module!\n");
					port_name = module->ports[port_counter++];
				}

				// find the port's wire in the underlying module
				const RTLIL::Wire *ref = module->wire(port_name);
				if (ref == nullptr)
					input_error("Cell instance refers to port %s which does not exist in module %s!.\n",
							log_id(port_name), log_id(module->name));

				// select the argument, if present
				log_assert(child->children.size() <= 1);
				if (child->children.empty())
					continue;
				AstNode *arg = child->children[0];

				// plain identifiers never need indirection; this also prevents
				// adding infinite levels of indirection
				if (arg->type == AST_IDENTIFIER && arg->children.empty())
					continue;

				// only add indirection for standard inputs or outputs
				if (ref->port_input == ref->port_output)
					continue;

				did_something = true;

				// create the indirection wire
				std::stringstream sstr;
				sstr << "$indirect$" << ref->name.c_str() << "$" << RTLIL::encode_filename(filename) << ":" << location.first_line << "$" << (autoidx++);
				std::string tmp_str = sstr.str();
				add_wire_for_ref(ref, tmp_str);

				AstNode *asgn = new AstNode(AST_ASSIGN);
				current_ast_mod->children.push_back(asgn);

				AstNode *ident = new AstNode(AST_IDENTIFIER);
				ident->str = tmp_str;
				child->children[0] = ident->clone();

				if (ref->port_input && !ref->port_output) {
					asgn->children.push_back(ident);
					asgn->children.push_back(arg);
				} else {
					log_assert(!ref->port_input && ref->port_output);
					asgn->children.push_back(arg);
					asgn->children.push_back(ident);
				}
				asgn->fixup_hierarchy_flags();
			}


		}
	}

	int backup_width_hint = width_hint;
	bool backup_sign_hint = sign_hint;

	bool detect_width_simple = false;
	bool child_0_is_self_determined = false;
	bool child_1_is_self_determined = false;
	bool child_2_is_self_determined = false;
	bool children_are_self_determined = false;
	bool reset_width_after_children = false;

	switch (type)
	{
	case AST_ASSIGN_EQ:
	case AST_ASSIGN_LE:
	case AST_ASSIGN:
		while (!children[0]->basic_prep && children[0]->simplify(false, stage, -1, false) == true)
			did_something = true;
		while (!children[1]->basic_prep && children[1]->simplify(false, stage, -1, false) == true)
			did_something = true;
		children[0]->detectSignWidth(backup_width_hint, backup_sign_hint);
		children[1]->detectSignWidth(width_hint, sign_hint);
		width_hint = max(width_hint, backup_width_hint);
		child_0_is_self_determined = true;
		// test only once, before optimizations and memory mappings but after assignment LHS was mapped to an identifier
		if (children[0]->id2ast && !children[0]->was_checked) {
			if ((type == AST_ASSIGN_LE || type == AST_ASSIGN_EQ) && children[0]->id2ast->is_logic)
				children[0]->id2ast->is_reg = true; // if logic type is used in a block asignment
			if ((type == AST_ASSIGN_LE || type == AST_ASSIGN_EQ) && !children[0]->id2ast->is_reg)
				log_warning("wire '%s' is assigned in a block at %s.\n", children[0]->str.c_str(), loc_string().c_str());
			if (type == AST_ASSIGN && children[0]->id2ast->is_reg) {
				bool is_rand_reg = false;
				if (children[1]->type == AST_FCALL) {
					if (children[1]->str == "\\$anyconst")
						is_rand_reg = true;
					if (children[1]->str == "\\$anyseq")
						is_rand_reg = true;
					if (children[1]->str == "\\$allconst")
						is_rand_reg = true;
					if (children[1]->str == "\\$allseq")
						is_rand_reg = true;
				}
				if (!is_rand_reg)
					log_warning("reg '%s' is assigned in a continuous assignment at %s.\n", children[0]->str.c_str(), loc_string().c_str());
			}
			children[0]->was_checked = true;
		}
		break;

	case AST_STRUCT:
	case AST_UNION:
		if (!basic_prep) {
			for (auto *node : children) {
				// resolve any ranges
				while (!node->basic_prep && node->simplify(true, stage, -1, false)) {
					did_something = true;
				}
			}
			// determine member offsets and widths
			size_packed_struct(this, 0);

			// instance rather than just a type in a typedef or outer struct?
			if (!str.empty() && str[0] == '\\') {
				// instance so add a wire for the packed structure
				auto wnode = make_packed_struct(this, str, attributes);
				log_assert(current_ast_mod);
				current_ast_mod->children.push_back(wnode);
			}
			basic_prep = true;
		}
		break;

	case AST_STRUCT_ITEM:
		if (is_custom_type) {
			log_assert(children.size() == 1);
			log_assert(children[0]->type == AST_WIRETYPE);
			auto type_name = children[0]->str;
			if (!current_scope.count(type_name)) {
				log_file_error(filename, location.first_line, "Unknown identifier `%s' used as type name\n", type_name.c_str());
			}
			AstNode *resolved_type_node = current_scope.at(type_name);
			if (resolved_type_node->type != AST_TYPEDEF)
				log_file_error(filename, location.first_line, "`%s' does not name a type\n", type_name.c_str());
			log_assert(resolved_type_node->children.size() == 1);
			AstNode *template_node = resolved_type_node->children[0];

			// Ensure typedef itself is fully simplified
			while (template_node->simplify(const_fold, stage, width_hint, sign_hint)) {};

			// Remove type reference
			delete children[0];
			children.pop_back();

			switch (template_node->type) {
			case AST_WIRE:
				type = AST_STRUCT_ITEM;
				break;
			case AST_STRUCT:
			case AST_UNION:
				type = template_node->type;
				break;
			default:
				log_file_error(filename, location.first_line, "Invalid type for struct member: %s", type2str(template_node->type).c_str());
			}

			is_reg = template_node->is_reg;
			is_logic = template_node->is_logic;
			is_signed = template_node->is_signed;
			is_string = template_node->is_string;
			is_custom_type = template_node->is_custom_type;

			range_valid = template_node->range_valid;
			range_swapped = template_node->range_swapped;
			range_left = template_node->range_left;
			range_right = template_node->range_right;

			set_attribute(ID::wiretype, mkconst_str(resolved_type_node->str));

			// Copy clones of children from template
			for (auto template_child : template_node->children) {
				children.push_back(template_child->clone());
			}

			did_something = true;

		}
		log_assert(!is_custom_type);
		break;

	case AST_ENUM:
		//log("\nENUM %s: %d child %d\n", str.c_str(), basic_prep, children[0]->basic_prep);
		if (!basic_prep) {
			for (auto item_node : children) {
				while (!item_node->basic_prep && item_node->simplify(false, stage, -1, false))
					did_something = true;
			}
			// allocate values (called more than once)
			allocateDefaultEnumValues();
		}
		break;

	case AST_PARAMETER:
	case AST_LOCALPARAM:
		// if parameter is implicit type which is the typename of a struct or union,
		// save information about struct in wiretype attribute
		if (children[0]->type == AST_IDENTIFIER && current_scope.count(children[0]->str) > 0) {
			auto item_node = current_scope[children[0]->str];
			if (item_node->type == AST_STRUCT || item_node->type == AST_UNION) {
				set_attribute(ID::wiretype, item_node->clone());
				size_packed_struct(attributes[ID::wiretype], 0);
				add_members_to_scope(attributes[ID::wiretype], str);
			}
		}
		while (!children[0]->basic_prep && children[0]->simplify(false, stage, -1, false) == true)
			did_something = true;
		children[0]->detectSignWidth(width_hint, sign_hint);
		if (children.size() > 1 && children[1]->type == AST_RANGE) {
			while (!children[1]->basic_prep && children[1]->simplify(false, stage, -1, false) == true)
				did_something = true;
			if (!children[1]->range_valid)
				input_error("Non-constant width range on parameter decl.\n");
			width_hint = max(width_hint, children[1]->range_left - children[1]->range_right + 1);
		}
		break;
	case AST_ENUM_ITEM:
		while (!children[0]->basic_prep && children[0]->simplify(false, stage, -1, false))
			did_something = true;
		children[0]->detectSignWidth(width_hint, sign_hint);
		if (children.size() > 1 && children[1]->type == AST_RANGE) {
			while (!children[1]->basic_prep && children[1]->simplify(false, stage, -1, false))
				did_something = true;
			if (!children[1]->range_valid)
				input_error("Non-constant width range on enum item decl.\n");
			width_hint = max(width_hint, children[1]->range_left - children[1]->range_right + 1);
		}
		break;

	case AST_TO_BITS:
	case AST_TO_SIGNED:
	case AST_TO_UNSIGNED:
	case AST_SELFSZ:
	case AST_CAST_SIZE:
	case AST_CONCAT:
	case AST_REPLICATE:
	case AST_REDUCE_AND:
	case AST_REDUCE_OR:
	case AST_REDUCE_XOR:
	case AST_REDUCE_XNOR:
	case AST_REDUCE_BOOL:
		detect_width_simple = true;
		children_are_self_determined = true;
		break;

	case AST_NEG:
	case AST_BIT_NOT:
	case AST_POS:
	case AST_BIT_AND:
	case AST_BIT_OR:
	case AST_BIT_XOR:
	case AST_BIT_XNOR:
	case AST_ADD:
	case AST_SUB:
	case AST_MUL:
	case AST_DIV:
	case AST_MOD:
		detect_width_simple = true;
		break;

	case AST_SHIFT_LEFT:
	case AST_SHIFT_RIGHT:
	case AST_SHIFT_SLEFT:
	case AST_SHIFT_SRIGHT:
	case AST_POW:
		detect_width_simple = true;
		child_1_is_self_determined = true;
		break;

	case AST_LT:
	case AST_LE:
	case AST_EQ:
	case AST_NE:
	case AST_EQX:
	case AST_NEX:
	case AST_GE:
	case AST_GT:
		width_hint = -1;
		sign_hint = true;
		for (auto child : children) {
			while (!child->basic_prep && child->simplify(false, stage, -1, false) == true)
				did_something = true;
			child->detectSignWidthWorker(width_hint, sign_hint);
		}
		reset_width_after_children = true;
		break;

	case AST_LOGIC_AND:
	case AST_LOGIC_OR:
	case AST_LOGIC_NOT:
		detect_width_simple = true;
		children_are_self_determined = true;
		break;

	case AST_TERNARY:
		child_0_is_self_determined = true;
		break;

	case AST_MEMRD:
		detect_width_simple = true;
		children_are_self_determined = true;
		break;

	case AST_FCALL:
	case AST_TCALL:
		children_are_self_determined = true;
		break;

	default:
		width_hint = -1;
		sign_hint = false;
	}

	if (detect_width_simple && width_hint < 0) {
		if (type == AST_REPLICATE)
			while (children[0]->simplify(true, stage, -1, false) == true)
				did_something = true;
		for (auto child : children)
			while (!child->basic_prep && child->simplify(false, stage, -1, false) == true)
				did_something = true;
		detectSignWidth(width_hint, sign_hint);
	}

	if (type == AST_FCALL && str == "\\$past")
		detectSignWidth(width_hint, sign_hint);

	if (type == AST_TERNARY) {
		if (width_hint < 0) {
			while (!children[0]->basic_prep && children[0]->simplify(true, stage, -1, false))
				did_something = true;

			bool backup_unevaluated_tern_branch = unevaluated_tern_branch;
			AstNode *chosen = get_tern_choice().first;

			unevaluated_tern_branch = backup_unevaluated_tern_branch || chosen == children[2];
			while (!children[1]->basic_prep && children[1]->simplify(false, stage, -1, false))
				did_something = true;

			unevaluated_tern_branch = backup_unevaluated_tern_branch || chosen == children[1];
			while (!children[2]->basic_prep && children[2]->simplify(false, stage, -1, false))
				did_something = true;

			unevaluated_tern_branch = backup_unevaluated_tern_branch;
			detectSignWidth(width_hint, sign_hint);
		}
		int width_hint_left, width_hint_right;
		bool sign_hint_left, sign_hint_right;
		bool found_real_left, found_real_right;
		children[1]->detectSignWidth(width_hint_left, sign_hint_left, &found_real_left);
		children[2]->detectSignWidth(width_hint_right, sign_hint_right, &found_real_right);
		if (found_real_left || found_real_right) {
			child_1_is_self_determined = true;
			child_2_is_self_determined = true;
		}
	}

	if (type == AST_CONDX && children.size() > 0 && children.at(0)->type == AST_CONSTANT) {
		for (auto &bit : children.at(0)->bits)
			if (bit == State::Sz || bit == State::Sx)
				bit = State::Sa;
	}

	if (type == AST_CONDZ && children.size() > 0 && children.at(0)->type == AST_CONSTANT) {
		for (auto &bit : children.at(0)->bits)
			if (bit == State::Sz)
				bit = State::Sa;
	}

	if (const_fold && type == AST_CASE)
	{
		detectSignWidth(width_hint, sign_hint);
		while (children[0]->simplify(const_fold, stage, width_hint, sign_hint)) { }
		if (children[0]->type == AST_CONSTANT && children[0]->bits_only_01()) {
			children[0]->is_signed = sign_hint;
			RTLIL::Const case_expr = children[0]->bitsAsConst(width_hint, sign_hint);
			std::vector<AstNode*> new_children;
			new_children.push_back(children[0]);
			for (int i = 1; i < GetSize(children); i++) {
				AstNode *child = children[i];
				log_assert(child->type == AST_COND || child->type == AST_CONDX || child->type == AST_CONDZ);
				for (auto v : child->children) {
					if (v->type == AST_DEFAULT)
						goto keep_const_cond;
					if (v->type == AST_BLOCK)
						continue;
					while (v->simplify(const_fold, stage, width_hint, sign_hint)) { }
					if (v->type == AST_CONSTANT && v->bits_only_01()) {
						RTLIL::Const case_item_expr = v->bitsAsConst(width_hint, sign_hint);
						RTLIL::Const match = const_eq(case_expr, case_item_expr, sign_hint, sign_hint, 1);
						log_assert(match.bits.size() == 1);
						if (match.bits.front() == RTLIL::State::S1) {
							while (i+1 < GetSize(children))
								delete children[++i];
							goto keep_const_cond;
						}
						continue;
					}
					goto keep_const_cond;
				}
				if (0)
			keep_const_cond:
					new_children.push_back(child);
				else
					delete child;
			}
			new_children.swap(children);
		}
	}

	dict<std::string, pool<int>> backup_memwr_visible;
	dict<std::string, pool<int>> final_memwr_visible;

	if (type == AST_CASE && stage == 2) {
		backup_memwr_visible = current_memwr_visible;
		final_memwr_visible = current_memwr_visible;
	}

	// simplify all children first
	// (iterate by index as e.g. auto wires can add new children in the process)
	for (size_t i = 0; i < children.size(); i++) {
		bool did_something_here = true;
		bool backup_flag_autowire = flag_autowire;
		bool backup_unevaluated_tern_branch = unevaluated_tern_branch;
		if ((type == AST_GENFOR || type == AST_FOR) && i >= 3)
			break;
		if ((type == AST_GENIF || type == AST_GENCASE) && i >= 1)
			break;
		if (type == AST_GENBLOCK)
			break;
		if (type == AST_CELLARRAY && children[i]->type == AST_CELL)
			continue;
		if (type == AST_BLOCK && !str.empty())
			break;
		if (type == AST_PREFIX && i >= 1)
			break;
		if (type == AST_DEFPARAM && i == 0)
			flag_autowire = true;
		if (type == AST_TERNARY && i > 0 && !unevaluated_tern_branch) {
			AstNode *chosen = get_tern_choice().first;
			unevaluated_tern_branch = chosen && chosen != children[i];
		}
		while (did_something_here && i < children.size()) {
			bool const_fold_here = const_fold;
			int width_hint_here = width_hint;
			bool sign_hint_here = sign_hint;
			if (i == 0 && (type == AST_REPLICATE || type == AST_WIRE))
				const_fold_here = true;
			if (type == AST_PARAMETER || type == AST_LOCALPARAM)
				const_fold_here = true;
			if (type == AST_BLOCK) {
				current_block = this;
				current_block_child = children[i];
			}
			if ((type == AST_ALWAYS || type == AST_INITIAL) && children[i]->type == AST_BLOCK)
				current_top_block = children[i];
			if (i == 0 && child_0_is_self_determined)
				width_hint_here = -1, sign_hint_here = false;
			if (i == 1 && child_1_is_self_determined)
				width_hint_here = -1, sign_hint_here = false;
			if (i == 2 && child_2_is_self_determined)
				width_hint_here = -1, sign_hint_here = false;
			if (children_are_self_determined)
				width_hint_here = -1, sign_hint_here = false;
			did_something_here = children[i]->simplify(const_fold_here, stage, width_hint_here, sign_hint_here);
			if (did_something_here)
				did_something = true;
		}
		if (stage == 2 && children[i]->type == AST_INITIAL && current_ast_mod != this) {
			current_ast_mod->children.push_back(children[i]);
			children.erase(children.begin() + (i--));
			did_something = true;
		}
		flag_autowire = backup_flag_autowire;
		unevaluated_tern_branch = backup_unevaluated_tern_branch;
		if (stage == 2 && type == AST_CASE) {
			for (auto &x : current_memwr_visible) {
				for (int y : x.second)
					final_memwr_visible[x.first].insert(y);
			}
			current_memwr_visible = backup_memwr_visible;
		}
	}
	for (auto &attr : attributes) {
		while (attr.second->simplify(true, stage, -1, false))
			did_something = true;
	}
	if (type == AST_CASE && stage == 2) {
		current_memwr_visible = final_memwr_visible;
	}
	if (type == AST_ALWAYS && stage == 2) {
		current_memwr_visible.clear();
		current_memwr_count.clear();
	}

	if (reset_width_after_children) {
		width_hint = backup_width_hint;
		sign_hint = backup_sign_hint;
		if (width_hint < 0)
			detectSignWidth(width_hint, sign_hint);
	}

	current_block = backup_current_block;
	current_block_child = backup_current_block_child;
	current_top_block = backup_current_top_block;
	current_always = backup_current_always;
	current_always_clocked = backup_current_always_clocked;

	for (auto it = backup_scope.begin(); it != backup_scope.end(); it++) {
		if (it->second == NULL)
			current_scope.erase(it->first);
		else
			current_scope[it->first] = it->second;
	}

	current_filename = filename;

	if (type == AST_MODULE || type == AST_INTERFACE)
		current_scope.clear();

	// convert defparam nodes to cell parameters
	if (type == AST_DEFPARAM && !children.empty())
	{
		if (children[0]->type != AST_IDENTIFIER)
			input_error("Module name in defparam contains non-constant expressions!\n");

		string modname, paramname = children[0]->str;

		size_t pos = paramname.rfind('.');

		while (pos != 0 && pos != std::string::npos)
		{
			modname = paramname.substr(0, pos);

			if (current_scope.count(modname))
				break;

			pos = paramname.rfind('.', pos - 1);
		}

		if (pos == std::string::npos)
			input_error("Can't find object for defparam `%s`!\n", RTLIL::unescape_id(paramname).c_str());

		paramname = "\\" + paramname.substr(pos+1);

		if (current_scope.at(modname)->type != AST_CELL)
			input_error("Defparam argument `%s . %s` does not match a cell!\n",
					RTLIL::unescape_id(modname).c_str(), RTLIL::unescape_id(paramname).c_str());

		AstNode *paraset = new AstNode(AST_PARASET, children[1]->clone(), GetSize(children) > 2 ? children[2]->clone() : NULL);
		paraset->str = paramname;

		AstNode *cell = current_scope.at(modname);
		cell->children.insert(cell->children.begin() + 1, paraset);
		delete_children();
	}

	// resolve typedefs
	if (type == AST_TYPEDEF) {
		log_assert(children.size() == 1);
		auto type_node = children[0];
		log_assert(type_node->type == AST_WIRE || type_node->type == AST_MEMORY || type_node->type == AST_STRUCT || type_node->type == AST_UNION);
		while (type_node->simplify(const_fold, stage, width_hint, sign_hint)) {
			did_something = true;
		}
		log_assert(!type_node->is_custom_type);
	}

	// resolve types of wires
	if (type == AST_WIRE || type == AST_MEMORY) {
		if (is_custom_type) {
			log_assert(children.size() >= 1);
			log_assert(children[0]->type == AST_WIRETYPE);
			auto type_name = children[0]->str;
			if (!current_scope.count(type_name)) {
				input_error("Unknown identifier `%s' used as type name\n", type_name.c_str());
			}
			AstNode *resolved_type_node = current_scope.at(type_name);
			if (resolved_type_node->type != AST_TYPEDEF)
				input_error("`%s' does not name a type\n", type_name.c_str());
			log_assert(resolved_type_node->children.size() == 1);
			AstNode *template_node = resolved_type_node->children[0];

			// Ensure typedef itself is fully simplified
			while (template_node->simplify(const_fold, stage, width_hint, sign_hint)) {};

			if (!str.empty() && str[0] == '\\' && (template_node->type == AST_STRUCT || template_node->type == AST_UNION)) {
				// replace instance with wire representing the packed structure
				newNode = make_packed_struct(template_node, str, attributes);
				newNode->set_attribute(ID::wiretype, mkconst_str(resolved_type_node->str));
				// add original input/output attribute to resolved wire
				newNode->is_input = this->is_input;
				newNode->is_output = this->is_output;
				current_scope[str] = this;
				goto apply_newNode;
			}

			// Remove type reference
			delete children[0];
			children.erase(children.begin());

			if (type == AST_WIRE)
				type = template_node->type;
			is_reg = template_node->is_reg;
			is_logic = template_node->is_logic;
			is_signed = template_node->is_signed;
			is_string = template_node->is_string;
			is_custom_type = template_node->is_custom_type;

			range_valid = template_node->range_valid;
			range_swapped = template_node->range_swapped;
			range_left = template_node->range_left;
			range_right = template_node->range_right;

			set_attribute(ID::wiretype, mkconst_str(resolved_type_node->str));

			// if an enum then add attributes to support simulator tracing
			annotateTypedEnums(template_node);

			// Insert clones children from template at beginning
			for (int i  = 0; i < GetSize(template_node->children); i++)
				children.insert(children.begin() + i, template_node->children[i]->clone());

			if (type == AST_MEMORY && GetSize(children) == 1) {
				// Single-bit memories must have [0:0] range
				AstNode *rng = make_range(0, 0);
				children.insert(children.begin(), rng);
			}
			fixup_hierarchy_flags();
			did_something = true;
		}
		log_assert(!is_custom_type);
	}

	// resolve types of parameters
	if (type == AST_LOCALPARAM || type == AST_PARAMETER) {
		if (is_custom_type) {
			log_assert(children.size() == 2);
			log_assert(children[1]->type == AST_WIRETYPE);
			auto type_name = children[1]->str;
			if (!current_scope.count(type_name)) {
				input_error("Unknown identifier `%s' used as type name\n", type_name.c_str());
			}
			AstNode *resolved_type_node = current_scope.at(type_name);
			if (resolved_type_node->type != AST_TYPEDEF)
				input_error("`%s' does not name a type\n", type_name.c_str());
			log_assert(resolved_type_node->children.size() == 1);
			AstNode *template_node = resolved_type_node->children[0];

			// Ensure typedef itself is fully simplified
			while (template_node->simplify(const_fold, stage, width_hint, sign_hint)) {};

			if (template_node->type == AST_STRUCT || template_node->type == AST_UNION) {
				// replace with wire representing the packed structure
				newNode = make_packed_struct(template_node, str, attributes);
				newNode->set_attribute(ID::wiretype, mkconst_str(resolved_type_node->str));
				newNode->type = type;
				current_scope[str] = this;
				// copy param value, it needs to be 1st value
				delete children[1];
				children.pop_back();
				newNode->children.insert(newNode->children.begin(), children[0]->clone());
				goto apply_newNode;
			}
			delete children[1];
			children.pop_back();

			if (template_node->type == AST_MEMORY)
				input_error("unpacked array type `%s' cannot be used for a parameter\n", children[1]->str.c_str());
			is_signed = template_node->is_signed;
			is_string = template_node->is_string;
			is_custom_type = template_node->is_custom_type;

			range_valid = template_node->range_valid;
			range_swapped = template_node->range_swapped;
			range_left = template_node->range_left;
			range_right = template_node->range_right;
			set_attribute(ID::wiretype, mkconst_str(resolved_type_node->str));
			for (auto template_child : template_node->children)
				children.push_back(template_child->clone());
			fixup_hierarchy_flags();
			did_something = true;
		}
		log_assert(!is_custom_type);
	}

	// resolve constant prefixes
	if (type == AST_PREFIX) {
		if (children[0]->type != AST_CONSTANT) {
			// dumpAst(NULL, ">   ");
			input_error("Index in generate block prefix syntax is not constant!\n");
		}
		if (children[1]->type == AST_PREFIX)
			children[1]->simplify(const_fold, stage, width_hint, sign_hint);
		log_assert(children[1]->type == AST_IDENTIFIER);
		newNode = children[1]->clone();
		const char *second_part = children[1]->str.c_str();
		if (second_part[0] == '\\')
			second_part++;
		newNode->str = stringf("%s[%d].%s", str.c_str(), children[0]->integer, second_part);
		goto apply_newNode;
	}

	// evaluate TO_BITS nodes
	if (type == AST_TO_BITS) {
		if (children[0]->type != AST_CONSTANT)
			input_error("Left operand of to_bits expression is not constant!\n");
		if (children[1]->type != AST_CONSTANT)
			input_error("Right operand of to_bits expression is not constant!\n");
		RTLIL::Const new_value = children[1]->bitsAsConst(children[0]->bitsAsConst().as_int(), children[1]->is_signed);
		newNode = mkconst_bits(new_value.bits, children[1]->is_signed);
		goto apply_newNode;
	}

	// annotate constant ranges
	if (type == AST_RANGE) {
		bool old_range_valid = range_valid;
		range_valid = false;
		range_swapped = false;
		range_left = -1;
		range_right = 0;
		log_assert(children.size() >= 1);
		if (children[0]->type == AST_CONSTANT) {
			range_valid = true;
			range_left = children[0]->integer;
			if (children.size() == 1)
				range_right = range_left;
		}
		if (children.size() >= 2) {
			if (children[1]->type == AST_CONSTANT)
				range_right = children[1]->integer;
			else
				range_valid = false;
		}
		if (old_range_valid != range_valid)
			did_something = true;
		if (range_valid && range_right > range_left) {
			int tmp = range_right;
			range_right = range_left;
			range_left = tmp;
			range_swapped = true;
		}
	}

	// annotate wires with their ranges
	if (type == AST_WIRE) {
		if (children.size() > 0) {
			if (children[0]->range_valid) {
				if (!range_valid)
					did_something = true;
				range_valid = true;
				range_swapped = children[0]->range_swapped;
				range_left = children[0]->range_left;
				range_right = children[0]->range_right;
				bool force_upto = false, force_downto = false;
				if (attributes.count(ID::force_upto)) {
					AstNode *val = attributes[ID::force_upto];
					if (val->type != AST_CONSTANT)
						input_error("Attribute `force_upto' with non-constant value!\n");
					force_upto = val->asAttrConst().as_bool();
				}
				if (attributes.count(ID::force_downto)) {
					AstNode *val = attributes[ID::force_downto];
					if (val->type != AST_CONSTANT)
						input_error("Attribute `force_downto' with non-constant value!\n");
					force_downto = val->asAttrConst().as_bool();
				}
				if (force_upto && force_downto)
					input_error("Attributes `force_downto' and `force_upto' cannot be both set!\n");
				if ((force_upto && !range_swapped) || (force_downto && range_swapped)) {
					std::swap(range_left, range_right);
					range_swapped = force_upto;
				}
			}
		} else {
			if (!range_valid)
				did_something = true;
			range_valid = true;
			range_swapped = false;
			range_left = 0;
			range_right = 0;
		}
	}

	// resolve multiranges on memory decl
	if (type == AST_MEMORY && children.size() > 1 && children[1]->type == AST_MULTIRANGE)
	{
		int total_size = 1;
		multirange_dimensions.clear();
		multirange_swapped.clear();
		for (auto range : children[1]->children) {
			if (!range->range_valid)
				input_error("Non-constant range on memory decl.\n");
			multirange_dimensions.push_back(min(range->range_left, range->range_right));
			multirange_dimensions.push_back(max(range->range_left, range->range_right) - min(range->range_left, range->range_right) + 1);
			multirange_swapped.push_back(range->range_swapped);
			total_size *= multirange_dimensions.back();
		}
		delete children[1];
		children[1] = new AstNode(AST_RANGE, AstNode::mkconst_int(0, true), AstNode::mkconst_int(total_size-1, true));
		fixup_hierarchy_flags();
		did_something = true;
	}

	// resolve multiranges on memory access
	if (type == AST_IDENTIFIER && id2ast && id2ast->type == AST_MEMORY && children.size() > 0 && children[0]->type == AST_MULTIRANGE)
	{
		AstNode *index_expr = nullptr;

		integer = children[0]->children.size(); // save original number of dimensions for $size() etc.
		for (int i = 0; 2*i < GetSize(id2ast->multirange_dimensions); i++)
		{
			if (GetSize(children[0]->children) <= i)
				input_error("Insufficient number of array indices for %s.\n", log_id(str));

			AstNode *new_index_expr = children[0]->children[i]->children.at(0)->clone();

			if (id2ast->multirange_dimensions[2*i])
				new_index_expr = new AstNode(AST_SUB, new_index_expr, AstNode::mkconst_int(id2ast->multirange_dimensions[2*i], true));

			if (i == 0)
				index_expr = new_index_expr;
			else
				index_expr = new AstNode(AST_ADD, new AstNode(AST_MUL, index_expr, AstNode::mkconst_int(id2ast->multirange_dimensions[2*i+1], true)), new_index_expr);
		}

		for (int i = GetSize(id2ast->multirange_dimensions)/2; i < GetSize(children[0]->children); i++)
			children.push_back(children[0]->children[i]->clone());

		delete children[0];
		if (index_expr == nullptr)
			children.erase(children.begin());
		else
			children[0] = new AstNode(AST_RANGE, index_expr);

		fixup_hierarchy_flags();
		did_something = true;
	}

	// trim/extend parameters
	if (type == AST_PARAMETER || type == AST_LOCALPARAM || type == AST_ENUM_ITEM) {
		if (children.size() > 1 && children[1]->type == AST_RANGE) {
			if (!children[1]->range_valid)
				input_error("Non-constant width range on parameter decl.\n");
			int width = std::abs(children[1]->range_left - children[1]->range_right) + 1;
			if (children[0]->type == AST_REALVALUE) {
				RTLIL::Const constvalue = children[0]->realAsConst(width);
				log_file_warning(filename, location.first_line, "converting real value %e to binary %s.\n",
						children[0]->realvalue, log_signal(constvalue));
				delete children[0];
				children[0] = mkconst_bits(constvalue.bits, sign_hint);
				fixup_hierarchy_flags();
				did_something = true;
			}
			if (children[0]->type == AST_CONSTANT) {
				if (width != int(children[0]->bits.size())) {
					RTLIL::SigSpec sig(children[0]->bits);
					sig.extend_u0(width, children[0]->is_signed);
					AstNode *old_child_0 = children[0];
					children[0] = mkconst_bits(sig.as_const().bits, is_signed);
					delete old_child_0;
					fixup_hierarchy_flags();
				}
				children[0]->is_signed = is_signed;
			}
			range_valid = true;
			range_swapped = children[1]->range_swapped;
			range_left = children[1]->range_left;
			range_right = children[1]->range_right;
		} else
		if (children.size() > 1 && children[1]->type == AST_REALVALUE && children[0]->type == AST_CONSTANT) {
			double as_realvalue = children[0]->asReal(sign_hint);
			delete children[0];
			children[0] = new AstNode(AST_REALVALUE);
			children[0]->realvalue = as_realvalue;
			fixup_hierarchy_flags();
			did_something = true;
		}
	}

	if (type == AST_IDENTIFIER && !basic_prep) {
		// check if a plausible struct member sss.mmmm
		if (!str.empty() && str[0] == '\\' && current_scope.count(str)) {
			auto item_node = current_scope[str];
			if (item_node->type == AST_STRUCT_ITEM || item_node->type == AST_STRUCT || item_node->type == AST_UNION) {
				// Traverse any hierarchical path until the full name for the referenced struct/union is found.
				std::string sname;
				bool found_sname = false;
				for (std::string::size_type pos = 0; (pos = str.find('.', pos)) != std::string::npos; pos++) {
					sname = str.substr(0, pos);
					if (current_scope.count(sname)) {
						auto stype = current_scope[sname]->type;
						if (stype == AST_WIRE || stype == AST_PARAMETER || stype == AST_LOCALPARAM) {
							found_sname = true;
							break;
						}
					}
				}

				if (found_sname) {
					// structure member, rewrite this node to reference the packed struct wire
					auto range = make_struct_member_range(this, item_node);
					newNode = new AstNode(AST_IDENTIFIER, range);
					newNode->str = sname;
					// save type and original number of dimensions for $size() etc.
					newNode->set_attribute(ID::wiretype, item_node->clone());
					if (!item_node->multirange_dimensions.empty() && children.size() > 0) {
						if (children[0]->type == AST_RANGE)
							newNode->integer = 1;
						else if (children[0]->type == AST_MULTIRANGE)
							newNode->integer = children[0]->children.size();
					}
					newNode->basic_prep = true;
					if (item_node->is_signed)
						newNode = new AstNode(AST_TO_SIGNED, newNode);
					goto apply_newNode;
				}
			}
		}
	}
	// annotate identifiers using scope resolution and create auto-wires as needed
	if (type == AST_IDENTIFIER) {
		if (current_scope.count(str) == 0) {
			AstNode *current_scope_ast = (current_ast_mod == nullptr) ? current_ast : current_ast_mod;
			str = try_pop_module_prefix();
			for (auto node : current_scope_ast->children) {
				//log("looking at mod scope child %s\n", type2str(node->type).c_str());
				switch (node->type) {
				case AST_PARAMETER:
				case AST_LOCALPARAM:
				case AST_WIRE:
				case AST_AUTOWIRE:
				case AST_GENVAR:
				case AST_MEMORY:
				case AST_FUNCTION:
				case AST_TASK:
				case AST_DPI_FUNCTION:
					//log("found child %s, %s\n", type2str(node->type).c_str(), node->str.c_str());
					if (str == node->str) {
						//log("add %s, type %s to scope\n", str.c_str(), type2str(node->type).c_str());
						current_scope[node->str] = node;
					}
					break;
				case AST_ENUM:
					current_scope[node->str] = node;
					for (auto enum_node : node->children) {
						log_assert(enum_node->type==AST_ENUM_ITEM);
						if (str == enum_node->str) {
							//log("\nadding enum item %s to scope\n", str.c_str());
							current_scope[str] = enum_node;
						}
					}
					break;
				default:
					break;
				}
			}
		}
		if (current_scope.count(str) == 0) {
			if (current_ast_mod == nullptr) {
				input_error("Identifier `%s' is implicitly declared outside of a module.\n", str.c_str());
			} else if (flag_autowire || str == "\\$global_clock") {
				AstNode *auto_wire = new AstNode(AST_AUTOWIRE);
				auto_wire->str = str;
				current_ast_mod->children.push_back(auto_wire);
				current_scope[str] = auto_wire;
				did_something = true;
			} else {
				input_error("Identifier `%s' is implicitly declared and `default_nettype is set to none.\n", str.c_str());
			}
		}
		if (id2ast != current_scope[str]) {
			id2ast = current_scope[str];
			did_something = true;
		}
	}

	// split memory access with bit select to individual statements
	if (type == AST_IDENTIFIER && children.size() == 2 && children[0]->type == AST_RANGE && children[1]->type == AST_RANGE && !in_lvalue && stage == 2)
	{
		if (id2ast == NULL || id2ast->type != AST_MEMORY || children[0]->children.size() != 1)
			input_error("Invalid bit-select on memory access!\n");

		int mem_width, mem_size, addr_bits;
		id2ast->meminfo(mem_width, mem_size, addr_bits);

		int data_range_left = id2ast->children[0]->range_left;
		int data_range_right = id2ast->children[0]->range_right;

		if (id2ast->children[0]->range_swapped)
			std::swap(data_range_left, data_range_right);

		std::stringstream sstr;
		sstr << "$mem2bits$" << str << "$" << RTLIL::encode_filename(filename) << ":" << location.first_line << "$" << (autoidx++);
		std::string wire_id = sstr.str();

		AstNode *wire = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(data_range_left, true), mkconst_int(data_range_right, true)));
		wire->str = wire_id;
		if (current_block)
			wire->set_attribute(ID::nosync, AstNode::mkconst_int(1, false));
		current_ast_mod->children.push_back(wire);
		while (wire->simplify(true, 1, -1, false)) { }

		AstNode *data = clone();
		delete data->children[1];
		data->children.pop_back();

		AstNode *assign = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), data);
		assign->children[0]->str = wire_id;
		assign->children[0]->was_checked = true;

		if (current_block)
		{
			size_t assign_idx = 0;
			while (assign_idx < current_block->children.size() && current_block->children[assign_idx] != current_block_child)
				assign_idx++;
			log_assert(assign_idx < current_block->children.size());
			current_block->children.insert(current_block->children.begin()+assign_idx, assign);
			wire->is_reg = true;
		}
		else
		{
			AstNode *proc = new AstNode(AST_ALWAYS, new AstNode(AST_BLOCK));
			proc->children[0]->children.push_back(assign);
			current_ast_mod->children.push_back(proc);
		}

		newNode = new AstNode(AST_IDENTIFIER, children[1]->clone());
		newNode->str = wire_id;
		newNode->integer = integer; // save original number of dimensions for $size() etc.
		newNode->id2ast = wire;
		goto apply_newNode;
	}

	if (type == AST_WHILE)
		input_error("While loops are only allowed in constant functions!\n");

	if (type == AST_REPEAT)
	{
		AstNode *count = children[0];
		AstNode *body = children[1];

		// eval count expression
		while (count->simplify(true, stage, 32, true)) { }

		if (count->type != AST_CONSTANT)
			input_error("Repeat loops outside must have constant repeat counts!\n");

		// convert to a block with the body repeated n times
		type = AST_BLOCK;
		children.clear();
		for (int i = 0; i < count->bitsAsConst().as_int(); i++)
			children.insert(children.begin(), body->clone());

		delete count;
		delete body;
		did_something = true;
	}

	// unroll for loops and generate-for blocks
	if ((type == AST_GENFOR || type == AST_FOR) && children.size() != 0)
	{
		AstNode *init_ast = children[0];
		AstNode *while_ast = children[1];
		AstNode *next_ast = children[2];
		AstNode *body_ast = children[3];

		while (body_ast->type == AST_GENBLOCK && body_ast->str.empty() &&
				body_ast->children.size() == 1 && body_ast->children.at(0)->type == AST_GENBLOCK)
			body_ast = body_ast->children.at(0);

		const char* loop_type_str = "procedural";
		const char* var_type_str = "register";
		AstNodeType var_type = AST_WIRE;
		if (type == AST_GENFOR) {
			loop_type_str = "generate";
			var_type_str = "genvar";
			var_type = AST_GENVAR;
		}

		if (init_ast->type != AST_ASSIGN_EQ)
			input_error("Unsupported 1st expression of %s for-loop!\n", loop_type_str);
		if (next_ast->type != AST_ASSIGN_EQ)
			input_error("Unsupported 3rd expression of %s for-loop!\n", loop_type_str);

		if (init_ast->children[0]->id2ast == NULL || init_ast->children[0]->id2ast->type != var_type)
			input_error("Left hand side of 1st expression of %s for-loop is not a %s!\n", loop_type_str, var_type_str);
		if (next_ast->children[0]->id2ast == NULL || next_ast->children[0]->id2ast->type != var_type)
			input_error("Left hand side of 3rd expression of %s for-loop is not a %s!\n", loop_type_str, var_type_str);

		if (init_ast->children[0]->id2ast != next_ast->children[0]->id2ast)
			input_error("Incompatible left-hand sides in 1st and 3rd expression of %s for-loop!\n", loop_type_str);

		// eval 1st expression
		AstNode *varbuf = init_ast->children[1]->clone();
		{
			int expr_width_hint = -1;
			bool expr_sign_hint = true;
			varbuf->detectSignWidth(expr_width_hint, expr_sign_hint);
			while (varbuf->simplify(true, stage, 32, true)) { }
		}

		if (varbuf->type != AST_CONSTANT)
			input_error("Right hand side of 1st expression of %s for-loop is not constant!\n", loop_type_str);

		auto resolved = current_scope.at(init_ast->children[0]->str);
		if (resolved->range_valid) {
			int const_size = varbuf->range_left - varbuf->range_right;
			int resolved_size = resolved->range_left - resolved->range_right;
			if (const_size < resolved_size) {
				for (int i = const_size; i < resolved_size; i++)
					varbuf->bits.push_back(resolved->is_signed ? varbuf->bits.back() : State::S0);
				varbuf->range_left = resolved->range_left;
				varbuf->range_right = resolved->range_right;
				varbuf->range_swapped = resolved->range_swapped;
				varbuf->range_valid = resolved->range_valid;
			}
		}

		varbuf = new AstNode(AST_LOCALPARAM, varbuf);
		varbuf->str = init_ast->children[0]->str;

		AstNode *backup_scope_varbuf = current_scope[varbuf->str];
		current_scope[varbuf->str] = varbuf;

		size_t current_block_idx = 0;
		if (type == AST_FOR) {
			while (current_block_idx < current_block->children.size() &&
					current_block->children[current_block_idx] != current_block_child)
				current_block_idx++;
		}

		while (1)
		{
			// eval 2nd expression
			AstNode *buf = while_ast->clone();
			{
				int expr_width_hint = -1;
				bool expr_sign_hint = true;
				buf->detectSignWidth(expr_width_hint, expr_sign_hint);
				while (buf->simplify(true, stage, expr_width_hint, expr_sign_hint)) { }
			}

			if (buf->type != AST_CONSTANT)
				input_error("2nd expression of %s for-loop is not constant!\n", loop_type_str);

			if (buf->integer == 0) {
				delete buf;
				break;
			}
			delete buf;

			// expand body
			int index = varbuf->children[0]->integer;
			log_assert(body_ast->type == AST_GENBLOCK || body_ast->type == AST_BLOCK);
			log_assert(!body_ast->str.empty());
			buf = body_ast->clone();

			std::stringstream sstr;
			sstr << buf->str << "[" << index << "].";
			std::string prefix = sstr.str();

			// create a scoped localparam for the current value of the loop variable
			AstNode *local_index = varbuf->clone();
			size_t pos = local_index->str.rfind('.');
			if (pos != std::string::npos) // remove outer prefix
				local_index->str = "\\" + local_index->str.substr(pos + 1);
			local_index->str = prefix_id(prefix, local_index->str);
			current_scope[local_index->str] = local_index;
			current_ast_mod->children.push_back(local_index);

			buf->expand_genblock(prefix);

			if (type == AST_GENFOR) {
				for (size_t i = 0; i < buf->children.size(); i++) {
					buf->children[i]->simplify(const_fold, stage, -1, false);
					current_ast_mod->children.push_back(buf->children[i]);
				}
			} else {
				for (size_t i = 0; i < buf->children.size(); i++)
					current_block->children.insert(current_block->children.begin() + current_block_idx++, buf->children[i]);
			}
			buf->children.clear();
			delete buf;

			// eval 3rd expression
			buf = next_ast->children[1]->clone();
			buf->set_in_param_flag(true);
			{
				int expr_width_hint = -1;
				bool expr_sign_hint = true;
				buf->detectSignWidth(expr_width_hint, expr_sign_hint);
				while (buf->simplify(true, stage, expr_width_hint, expr_sign_hint)) { }
			}

			if (buf->type != AST_CONSTANT)
				input_error("Right hand side of 3rd expression of %s for-loop is not constant (%s)!\n", loop_type_str, type2str(buf->type).c_str());

			delete varbuf->children[0];
			varbuf->children[0] = buf;
		}

		if (type == AST_FOR) {
			AstNode *buf = next_ast->clone();
			delete buf->children[1];
			buf->children[1] = varbuf->children[0]->clone();
			current_block->children.insert(current_block->children.begin() + current_block_idx++, buf);
		}

		current_scope[varbuf->str] = backup_scope_varbuf;
		delete varbuf;
		delete_children();
		did_something = true;
	}

	// check for local objects in unnamed block
	if (type == AST_BLOCK && str.empty())
	{
		for (size_t i = 0; i < children.size(); i++)
			if (children[i]->type == AST_WIRE || children[i]->type == AST_MEMORY || children[i]->type == AST_PARAMETER || children[i]->type == AST_LOCALPARAM || children[i]->type == AST_TYPEDEF)
			{
				log_assert(!VERILOG_FRONTEND::sv_mode);
				children[i]->input_error("Local declaration in unnamed block is only supported in SystemVerilog mode!\n");
			}
	}

	// transform block with name
	if (type == AST_BLOCK && !str.empty())
	{
		expand_genblock(str + ".");

		// if this is an autonamed block is in an always_comb
		if (current_always && current_always->attributes.count(ID::always_comb)
				&& is_autonamed_block(str))
			// track local variables in this block so we can consider adding
			// nosync once the block has been fully elaborated
			for (AstNode *child : children)
				if (child->type == AST_WIRE &&
						!child->attributes.count(ID::nosync))
					mark_auto_nosync(this, child);

		std::vector<AstNode*> new_children;
		for (size_t i = 0; i < children.size(); i++)
			if (children[i]->type == AST_WIRE || children[i]->type == AST_MEMORY || children[i]->type == AST_PARAMETER || children[i]->type == AST_LOCALPARAM || children[i]->type == AST_TYPEDEF) {
				children[i]->simplify(false, stage, -1, false);
				current_ast_mod->children.push_back(children[i]);
				current_scope[children[i]->str] = children[i];
			} else
				new_children.push_back(children[i]);

		children.swap(new_children);
		did_something = true;
		str.clear();
	}

	// simplify unconditional generate block
	if (type == AST_GENBLOCK && children.size() != 0)
	{
		if (!str.empty()) {
			expand_genblock(str + ".");
		}

		for (size_t i = 0; i < children.size(); i++) {
			children[i]->simplify(const_fold, stage, -1, false);
			current_ast_mod->children.push_back(children[i]);
		}

		children.clear();
		did_something = true;
	}

	// simplify generate-if blocks
	if (type == AST_GENIF && children.size() != 0)
	{
		AstNode *buf = children[0]->clone();
		while (buf->simplify(true, stage, width_hint, sign_hint)) { }
		if (buf->type != AST_CONSTANT) {
			// for (auto f : log_files)
			// 	dumpAst(f, "verilog-ast> ");
			input_error("Condition for generate if is not constant!\n");
		}
		if (buf->asBool() != 0) {
			delete buf;
			buf = children[1]->clone();
		} else {
			delete buf;
			buf = children.size() > 2 ? children[2]->clone() : NULL;
		}

		if (buf)
		{
			if (buf->type != AST_GENBLOCK)
				buf = new AstNode(AST_GENBLOCK, buf);

			if (!buf->str.empty()) {
				buf->expand_genblock(buf->str + ".");
			}

			for (size_t i = 0; i < buf->children.size(); i++) {
				buf->children[i]->simplify(const_fold, stage, -1, false);
				current_ast_mod->children.push_back(buf->children[i]);
			}

			buf->children.clear();
			delete buf;
		}

		delete_children();
		did_something = true;
	}

	// simplify generate-case blocks
	if (type == AST_GENCASE && children.size() != 0)
	{
		AstNode *buf = children[0]->clone();
		while (buf->simplify(true, stage, width_hint, sign_hint)) { }
		if (buf->type != AST_CONSTANT) {
			// for (auto f : log_files)
			// 	dumpAst(f, "verilog-ast> ");
			input_error("Condition for generate case is not constant!\n");
		}

		bool ref_signed = buf->is_signed;
		RTLIL::Const ref_value = buf->bitsAsConst();
		delete buf;

		AstNode *selected_case = NULL;
		for (size_t i = 1; i < children.size(); i++)
		{
			log_assert(children.at(i)->type == AST_COND || children.at(i)->type == AST_CONDX || children.at(i)->type == AST_CONDZ);

			AstNode *this_genblock = NULL;
			for (auto child : children.at(i)->children) {
				log_assert(this_genblock == NULL);
				if (child->type == AST_GENBLOCK)
					this_genblock = child;
			}

			for (auto child : children.at(i)->children)
			{
				if (child->type == AST_DEFAULT) {
					if (selected_case == NULL)
						selected_case = this_genblock;
					continue;
				}
				if (child->type == AST_GENBLOCK)
					continue;

				buf = child->clone();
				buf->set_in_param_flag(true);
				while (buf->simplify(true, stage, width_hint, sign_hint)) { }
				if (buf->type != AST_CONSTANT) {
					// for (auto f : log_files)
					// 	dumpAst(f, "verilog-ast> ");
					input_error("Expression in generate case is not constant!\n");
				}

				bool is_selected = RTLIL::const_eq(ref_value, buf->bitsAsConst(), ref_signed && buf->is_signed, ref_signed && buf->is_signed, 1).as_bool();
				delete buf;

				if (is_selected) {
					selected_case = this_genblock;
					i = children.size();
					break;
				}
			}
		}

		if (selected_case != NULL)
		{
			log_assert(selected_case->type == AST_GENBLOCK);
			buf = selected_case->clone();

			if (!buf->str.empty()) {
				buf->expand_genblock(buf->str + ".");
			}

			for (size_t i = 0; i < buf->children.size(); i++) {
				buf->children[i]->simplify(const_fold, stage, -1, false);
				current_ast_mod->children.push_back(buf->children[i]);
			}

			buf->children.clear();
			delete buf;
		}

		delete_children();
		did_something = true;
	}

	// unroll cell arrays
	if (type == AST_CELLARRAY)
	{
		if (!children.at(0)->range_valid)
			input_error("Non-constant array range on cell array.\n");

		newNode = new AstNode(AST_GENBLOCK);
		int num = max(children.at(0)->range_left, children.at(0)->range_right) - min(children.at(0)->range_left, children.at(0)->range_right) + 1;

		for (int i = 0; i < num; i++) {
			int idx = children.at(0)->range_left > children.at(0)->range_right ? children.at(0)->range_right + i : children.at(0)->range_right - i;
			AstNode *new_cell = children.at(1)->clone();
			newNode->children.push_back(new_cell);
			new_cell->str += stringf("[%d]", idx);
			if (new_cell->type == AST_PRIMITIVE) {
				input_error("Cell arrays of primitives are currently not supported.\n");
			} else {
				log_assert(new_cell->children.at(0)->type == AST_CELLTYPE);
				new_cell->children.at(0)->str = stringf("$array:%d:%d:%s", i, num, new_cell->children.at(0)->str.c_str());
			}
		}

		goto apply_newNode;
	}

	// replace primitives with assignments
	if (type == AST_PRIMITIVE)
	{
		if (children.size() < 2)
			input_error("Insufficient number of arguments for primitive `%s'!\n", str.c_str());

		std::vector<AstNode*> children_list;
		for (auto child : children) {
			log_assert(child->type == AST_ARGUMENT);
			log_assert(child->children.size() == 1);
			children_list.push_back(child->children[0]);
			child->children.clear();
			delete child;
		}
		children.clear();

		if (str == "bufif0" || str == "bufif1" || str == "notif0" || str == "notif1")
		{
			if (children_list.size() != 3)
				input_error("Invalid number of arguments for primitive `%s'!\n", str.c_str());

			std::vector<RTLIL::State> z_const(1, RTLIL::State::Sz);

			AstNode *mux_input = children_list.at(1);
			if (str == "notif0" || str == "notif1") {
				mux_input = new AstNode(AST_BIT_NOT, mux_input);
			}
			AstNode *node = new AstNode(AST_TERNARY, children_list.at(2));
			if (str == "bufif0") {
				node->children.push_back(AstNode::mkconst_bits(z_const, false));
				node->children.push_back(mux_input);
			} else {
				node->children.push_back(mux_input);
				node->children.push_back(AstNode::mkconst_bits(z_const, false));
			}

			str.clear();
			type = AST_ASSIGN;
			children.push_back(children_list.at(0));
			children.back()->was_checked = true;
			children.push_back(node);
			fixup_hierarchy_flags();
			did_something = true;
		}
		else if (str == "buf" || str == "not")
		{
			AstNode *input = children_list.back();
			if (str == "not")
				input = new AstNode(AST_BIT_NOT, input);

			newNode = new AstNode(AST_GENBLOCK);
			for (auto it = children_list.begin(); it != std::prev(children_list.end()); it++) {
				newNode->children.push_back(new AstNode(AST_ASSIGN, *it, input->clone()));
				newNode->children.back()->was_checked = true;
			}
			delete input;

			did_something = true;
		}
		else
		{
			AstNodeType op_type = AST_NONE;
			bool invert_results = false;

			if (str == "and")
				op_type = AST_BIT_AND;
			if (str == "nand")
				op_type = AST_BIT_AND, invert_results = true;
			if (str == "or")
				op_type = AST_BIT_OR;
			if (str == "nor")
				op_type = AST_BIT_OR, invert_results = true;
			if (str == "xor")
				op_type = AST_BIT_XOR;
			if (str == "xnor")
				op_type = AST_BIT_XOR, invert_results = true;
			log_assert(op_type != AST_NONE);

			AstNode *node = children_list[1];
			if (op_type != AST_POS)
				for (size_t i = 2; i < children_list.size(); i++) {
					node = new AstNode(op_type, node, children_list[i]);
					node->location = location;
				}
			if (invert_results)
				node = new AstNode(AST_BIT_NOT, node);

			str.clear();
			type = AST_ASSIGN;
			children.push_back(children_list[0]);
			children.back()->was_checked = true;
			children.push_back(node);
			fixup_hierarchy_flags();
			did_something = true;
		}
	}

	// replace dynamic ranges in left-hand side expressions (e.g. "foo[bar] <= 1'b1;") with
	// either a big case block that selects the correct single-bit assignment, or mask and
	// shift operations.
	if (type == AST_ASSIGN_EQ || type == AST_ASSIGN_LE)
	{
		if (children[0]->type != AST_IDENTIFIER || children[0]->children.size() == 0)
			goto skip_dynamic_range_lvalue_expansion;
		if (children[0]->children[0]->range_valid || did_something)
			goto skip_dynamic_range_lvalue_expansion;
		if (children[0]->id2ast == NULL || children[0]->id2ast->type != AST_WIRE)
			goto skip_dynamic_range_lvalue_expansion;
		if (!children[0]->id2ast->range_valid)
			goto skip_dynamic_range_lvalue_expansion;

		AST::AstNode *member_node = get_struct_member(children[0]);
		int wire_width = member_node ?
			member_node->range_left - member_node->range_right + 1 :
			children[0]->id2ast->range_left - children[0]->id2ast->range_right + 1;
		int wire_offset = children[0]->id2ast->range_right;
		int result_width = 1;

		AstNode *shift_expr = NULL;
		AstNode *range = children[0]->children[0];

		if (!try_determine_range_width(range, result_width))
			input_error("Unsupported expression on dynamic range select on signal `%s'!\n", str.c_str());

		if (range->children.size() >= 2)
			shift_expr = range->children[1]->clone();
		else
			shift_expr = range->children[0]->clone();

		bool use_case_method = children[0]->id2ast->get_bool_attribute(ID::nowrshmsk);

		if (!use_case_method && current_always->detect_latch(children[0]->str))
			use_case_method = true;

		if (use_case_method) {
			// big case block

			int stride = 1;
			long long bitno_div = stride;

			int case_width_hint;
			bool case_sign_hint;
			shift_expr->detectSignWidth(case_width_hint, case_sign_hint);
			int max_width = case_width_hint;

			if (member_node) {  // Member in packed struct/union
				// Clamp chunk to range of member within struct/union.
				log_assert(!wire_offset && !children[0]->id2ast->range_swapped);

				// When the (* nowrshmsk *) attribute is set, a CASE block is generated below
				// to select the indexed bit slice. When a multirange array is indexed, the
				// start of each possible slice is separated by the bit stride of the last
				// index dimension, and we can optimize the CASE block accordingly.
				// The dimension of the original array expression is saved in the 'integer' field.
				int dims = children[0]->integer;
				stride = wire_width;
				for (int dim = 0; dim < dims; dim++) {
					stride /= get_struct_range_width(member_node, dim);
				}
				bitno_div = stride;
			} else {
				// Extract (index)*(width) from non_opt_range pattern ((@selfsz@((index)*(width)))+(0)).
				AstNode *lsb_expr =
					shift_expr->type == AST_ADD && shift_expr->children[0]->type == AST_SELFSZ &&
					shift_expr->children[1]->type == AST_CONSTANT && shift_expr->children[1]->integer == 0 ?
					shift_expr->children[0]->children[0] :
					shift_expr;

				// Extract stride from indexing of two-dimensional packed arrays and
				// variable slices on the form dst[i*stride +: width] = src.
				if (lsb_expr->type == AST_MUL &&
				    (lsb_expr->children[0]->type == AST_CONSTANT ||
				     lsb_expr->children[1]->type == AST_CONSTANT))
				{
					int stride_ix = lsb_expr->children[1]->type == AST_CONSTANT;
					stride = (int)lsb_expr->children[stride_ix]->integer;
					bitno_div = stride != 0 ? stride : 1;

					// Check whether i*stride can overflow.
					int i_width;
					bool i_sign;
					lsb_expr->children[1 - stride_ix]->detectSignWidth(i_width, i_sign);
					int stride_width;
					bool stride_sign;
					lsb_expr->children[stride_ix]->detectSignWidth(stride_width, stride_sign);
					max_width = std::max(i_width, stride_width);
					// Stride width calculated from actual stride value.
					stride_width = std::ceil(std::log2(std::abs(stride)));

					if (i_width + stride_width > max_width) {
						// For (truncated) i*stride to be within the range of dst, the following must hold:
						//   i*stride ≡ bitno (mod shift_mod), i.e.
						//   i*stride = k*shift_mod + bitno
						//
						// The Diophantine equation on the form ax + by = c:
						//   stride*i - shift_mod*k = bitno
						// has solutions iff c is a multiple of d = gcd(a, b), i.e.
						//   bitno mod gcd(stride, shift_mod) = 0
						//
						// long long is at least 64 bits in C++11
						long long shift_mod = 1ll << (max_width - case_sign_hint);
						// std::gcd requires C++17
						// bitno_div = std::gcd(stride, shift_mod);
						bitno_div = gcd((long long)stride, shift_mod);
					}
				}
			}

			// long long is at least 64 bits in C++11
			long long max_offset = (1ll << (max_width - case_sign_hint)) - 1;
			long long min_offset = case_sign_hint ? -(1ll << (max_width - 1)) : 0;

			// A temporary register holds the result of the (possibly complex) rvalue expression,
			// avoiding repetition in each AST_COND below.
			int rvalue_width;
			bool rvalue_sign;
			children[1]->detectSignWidth(rvalue_width, rvalue_sign);
			AstNode *rvalue = mktemp_logic("$bitselwrite$rvalue$", current_ast_mod, true, rvalue_width - 1, 0, rvalue_sign);
			AstNode *caseNode = new AstNode(AST_CASE, shift_expr);
			newNode = new AstNode(AST_BLOCK,
					      new AstNode(AST_ASSIGN_EQ, rvalue, children[1]->clone()),
					      caseNode);

			did_something = true;
			for (int i = 1 - result_width; i < wire_width; i++) {
				// Out of range indexes are handled in genrtlil.cc
				int start_bit = wire_offset + i;
				int end_bit = start_bit + result_width - 1;
				// Check whether the current index can be generated by shift_expr.
				if (start_bit < min_offset || start_bit > max_offset)
					continue;
				if (start_bit%bitno_div != 0 || (stride == 0 && start_bit != 0))
					continue;

				AstNode *cond = new AstNode(AST_COND, mkconst_int(start_bit, case_sign_hint, max_width));
				AstNode *lvalue = children[0]->clone();
				lvalue->delete_children();
				if (member_node)
					lvalue->set_attribute(ID::wiretype, member_node->clone());
				lvalue->children.push_back(new AstNode(AST_RANGE,
						mkconst_int(end_bit, true), mkconst_int(start_bit, true)));
				cond->children.push_back(new AstNode(AST_BLOCK, new AstNode(type, lvalue, rvalue->clone())));
				caseNode->children.push_back(cond);
			}
		} else {
			// mask and shift operations
			// dst = (dst & ~(width'1 << lsb)) | unsigned'(width'(src)) << lsb)

			AstNode *lvalue = children[0]->clone();
			lvalue->delete_children();
			if (member_node)
				lvalue->set_attribute(ID::wiretype, member_node->clone());

			AstNode *old_data = lvalue->clone();
			if (type == AST_ASSIGN_LE)
				old_data->lookahead = true;

			int shift_width_hint;
			bool shift_sign_hint;
			shift_expr->detectSignWidth(shift_width_hint, shift_sign_hint);

			// All operations are carried out in a new block.
			newNode = new AstNode(AST_BLOCK);

			// Temporary register holding the result of the bit- or part-select position expression.
			AstNode *pos = mktemp_logic("$bitselwrite$pos$", current_ast_mod, true, shift_width_hint - 1, 0, shift_sign_hint);
			newNode->children.push_back(new AstNode(AST_ASSIGN_EQ, pos, shift_expr));

			// Calculate lsb from position.
			AstNode *shift_val = pos->clone();

			// If the expression is signed, we must add an extra bit for possible negation of the most negative number.
			// If the expression is unsigned, we must add an extra bit for sign.
			shift_val = new AstNode(AST_CAST_SIZE, mkconst_int(shift_width_hint + 1, true), shift_val);
			if (!shift_sign_hint)
				shift_val = new AstNode(AST_TO_SIGNED, shift_val);

			// offset the shift amount by the lower bound of the dimension
			if (wire_offset != 0)
				shift_val = new AstNode(AST_SUB, shift_val, mkconst_int(wire_offset, true));

			// reflect the shift amount if the dimension is swapped
			if (children[0]->id2ast->range_swapped)
				shift_val = new AstNode(AST_SUB, mkconst_int(wire_width - result_width, true), shift_val);

			// AST_SHIFT uses negative amounts for shifting left
			shift_val = new AstNode(AST_NEG, shift_val);

			// dst = (dst & ~(width'1 << lsb)) | unsigned'(width'(src)) << lsb)
			did_something = true;
			AstNode *bitmask = mkconst_bits(std::vector<RTLIL::State>(result_width, State::S1), false);
			newNode->children.push_back(
				new AstNode(type,
					    lvalue,
					    new AstNode(AST_BIT_OR,
							new AstNode(AST_BIT_AND,
								    old_data,
								    new AstNode(AST_BIT_NOT,
										new AstNode(AST_SHIFT,
											    bitmask,
											    shift_val->clone()))),
							new AstNode(AST_SHIFT,
								    new AstNode(AST_TO_UNSIGNED,
										new AstNode(AST_CAST_SIZE,
											    mkconst_int(result_width, true),
											    children[1]->clone())),
								    shift_val))));

			newNode->fixup_hierarchy_flags(true);
		}

		goto apply_newNode;
	}
skip_dynamic_range_lvalue_expansion:;

	if (stage > 1 && (type == AST_ASSERT || type == AST_ASSUME || type == AST_LIVE || type == AST_FAIR || type == AST_COVER) && current_block != NULL)
	{
		std::stringstream sstr;
		sstr << "$formal$" << RTLIL::encode_filename(filename) << ":" << location.first_line << "$" << (autoidx++);
		std::string id_check = sstr.str() + "_CHECK", id_en = sstr.str() + "_EN";

		AstNode *wire_check = new AstNode(AST_WIRE);
		wire_check->str = id_check;
		wire_check->was_checked = true;
		current_ast_mod->children.push_back(wire_check);
		current_scope[wire_check->str] = wire_check;
		while (wire_check->simplify(true, 1, -1, false)) { }

		AstNode *wire_en = new AstNode(AST_WIRE);
		wire_en->str = id_en;
		wire_en->was_checked = true;
		current_ast_mod->children.push_back(wire_en);
		if (current_always_clocked) {
			current_ast_mod->children.push_back(new AstNode(AST_INITIAL, new AstNode(AST_BLOCK, new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), AstNode::mkconst_int(0, false, 1)))));
			current_ast_mod->children.back()->children[0]->children[0]->children[0]->str = id_en;
			current_ast_mod->children.back()->children[0]->children[0]->children[0]->was_checked = true;
		}
		current_scope[wire_en->str] = wire_en;
		while (wire_en->simplify(true, 1, -1, false)) { }

		AstNode *check_defval;
		if (type == AST_LIVE || type == AST_FAIR) {
			check_defval = new AstNode(AST_REDUCE_BOOL, children[0]->clone());
		} else {
			std::vector<RTLIL::State> x_bit;
			x_bit.push_back(RTLIL::State::Sx);
			check_defval = mkconst_bits(x_bit, false);
		}

		AstNode *assign_check = new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), check_defval);
		assign_check->children[0]->str = id_check;
		assign_check->children[0]->was_checked = true;

		AstNode *assign_en = new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), mkconst_int(0, false, 1));
		assign_en->children[0]->str = id_en;
		assign_en->children[0]->was_checked = true;

		AstNode *default_signals = new AstNode(AST_BLOCK);
		default_signals->children.push_back(assign_check);
		default_signals->children.push_back(assign_en);
		current_top_block->children.insert(current_top_block->children.begin(), default_signals);

		if (type == AST_LIVE || type == AST_FAIR) {
			assign_check = nullptr;
		} else {
			assign_check = new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), new AstNode(AST_REDUCE_BOOL, children[0]->clone()));
			assign_check->children[0]->str = id_check;
			assign_check->children[0]->was_checked = true;
			assign_check->fixup_hierarchy_flags();
		}

		if (current_always == nullptr || current_always->type != AST_INITIAL) {
			assign_en = new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), mkconst_int(1, false, 1));
		} else {
			assign_en = new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), new AstNode(AST_FCALL));
			assign_en->children[1]->str = "\\$initstate";
		}
		assign_en->children[0]->str = id_en;
		assign_en->children[0]->was_checked = true;
		assign_en->fixup_hierarchy_flags();

		newNode = new AstNode(AST_BLOCK);
		if (assign_check != nullptr)
			newNode->children.push_back(assign_check);
		newNode->children.push_back(assign_en);

		AstNode *assertnode = new AstNode(type);
		assertnode->location = location;
		assertnode->str = str;
		assertnode->children.push_back(new AstNode(AST_IDENTIFIER));
		assertnode->children.push_back(new AstNode(AST_IDENTIFIER));
		assertnode->children[0]->str = id_check;
		assertnode->children[1]->str = id_en;
		assertnode->attributes.swap(attributes);
		current_ast_mod->children.push_back(assertnode);

		goto apply_newNode;
	}

	if (stage > 1 && (type == AST_ASSERT || type == AST_ASSUME || type == AST_LIVE || type == AST_FAIR || type == AST_COVER) && children.size() == 1)
	{
		children.push_back(mkconst_int(1, false, 1));
		fixup_hierarchy_flags();
		did_something = true;
	}

	// found right-hand side identifier for memory -> replace with memory read port
	if (stage > 1 && type == AST_IDENTIFIER && id2ast != NULL && id2ast->type == AST_MEMORY && !in_lvalue &&
			children.size() == 1 && children[0]->type == AST_RANGE && children[0]->children.size() == 1) {
		newNode = new AstNode(AST_MEMRD, children[0]->children[0]->clone());
		newNode->str = str;
		newNode->id2ast = id2ast;
		goto apply_newNode;
	}

	// assignment with nontrivial member in left-hand concat expression -> split assignment
	if ((type == AST_ASSIGN_EQ || type == AST_ASSIGN_LE) && children[0]->type == AST_CONCAT && width_hint > 0)
	{
		bool found_nontrivial_member = false;

		for (auto child : children[0]->children) {
			if (child->type == AST_IDENTIFIER && child->id2ast != NULL && child->id2ast->type == AST_MEMORY)
				found_nontrivial_member = true;
		}

		if (found_nontrivial_member)
		{
			newNode = new AstNode(AST_BLOCK);

			AstNode *wire_tmp = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(width_hint-1, true), mkconst_int(0, true)));
			wire_tmp->str = stringf("$splitcmplxassign$%s:%d$%d", RTLIL::encode_filename(filename).c_str(), location.first_line, autoidx++);
			current_ast_mod->children.push_back(wire_tmp);
			current_scope[wire_tmp->str] = wire_tmp;
			wire_tmp->set_attribute(ID::nosync, AstNode::mkconst_int(1, false));
			while (wire_tmp->simplify(true, 1, -1, false)) { }
			wire_tmp->is_logic = true;

			AstNode *wire_tmp_id = new AstNode(AST_IDENTIFIER);
			wire_tmp_id->str = wire_tmp->str;

			newNode->children.push_back(new AstNode(AST_ASSIGN_EQ, wire_tmp_id, children[1]->clone()));
			newNode->children.back()->was_checked = true;

			int cursor = 0;
			for (auto child : children[0]->children)
			{
				int child_width_hint = -1;
				bool child_sign_hint = true;
				child->detectSignWidth(child_width_hint, child_sign_hint);

				AstNode *rhs = wire_tmp_id->clone();
				rhs->children.push_back(new AstNode(AST_RANGE, AstNode::mkconst_int(cursor+child_width_hint-1, true), AstNode::mkconst_int(cursor, true)));
				newNode->children.push_back(new AstNode(type, child->clone(), rhs));

				cursor += child_width_hint;
			}

			goto apply_newNode;
		}
	}

	// assignment with memory in left-hand side expression -> replace with memory write port
	if (stage > 1 && (type == AST_ASSIGN_EQ || type == AST_ASSIGN_LE) && children[0]->type == AST_IDENTIFIER &&
			children[0]->id2ast && children[0]->id2ast->type == AST_MEMORY && children[0]->id2ast->children.size() >= 2 &&
			children[0]->id2ast->children[0]->range_valid && children[0]->id2ast->children[1]->range_valid &&
			(children[0]->children.size() == 1 || children[0]->children.size() == 2) && children[0]->children[0]->type == AST_RANGE)
	{
		std::stringstream sstr;
		sstr << "$memwr$" << children[0]->str << "$" << RTLIL::encode_filename(filename) << ":" << location.first_line << "$" << (autoidx++);
		std::string id_addr = sstr.str() + "_ADDR", id_data = sstr.str() + "_DATA", id_en = sstr.str() + "_EN";

		int mem_width, mem_size, addr_bits;
		bool mem_signed = children[0]->id2ast->is_signed;
		children[0]->id2ast->meminfo(mem_width, mem_size, addr_bits);

		newNode = new AstNode(AST_BLOCK);
		AstNode *defNode = new AstNode(AST_BLOCK);

		int data_range_left = children[0]->id2ast->children[0]->range_left;
		int data_range_right = children[0]->id2ast->children[0]->range_right;
		int mem_data_range_offset = std::min(data_range_left, data_range_right);

		int addr_width_hint = -1;
		bool addr_sign_hint = true;
		children[0]->children[0]->children[0]->detectSignWidthWorker(addr_width_hint, addr_sign_hint);
		addr_bits = std::max(addr_bits, addr_width_hint);

		std::vector<RTLIL::State> x_bits_addr, x_bits_data, set_bits_en;
		for (int i = 0; i < addr_bits; i++)
			x_bits_addr.push_back(RTLIL::State::Sx);
		for (int i = 0; i < mem_width; i++)
			x_bits_data.push_back(RTLIL::State::Sx);
		for (int i = 0; i < mem_width; i++)
			set_bits_en.push_back(RTLIL::State::S1);

		AstNode *node_addr = nullptr;
		if (children[0]->children[0]->children[0]->isConst()) {
			node_addr = children[0]->children[0]->children[0]->clone();
		} else {
			AstNode *wire_addr = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(addr_bits-1, true), mkconst_int(0, true)));
			wire_addr->str = id_addr;
			wire_addr->was_checked = true;
			current_ast_mod->children.push_back(wire_addr);
			current_scope[wire_addr->str] = wire_addr;
			while (wire_addr->simplify(true, 1, -1, false)) { }

			AstNode *assign_addr = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), mkconst_bits(x_bits_addr, false));
			assign_addr->children[0]->str = id_addr;
			assign_addr->children[0]->was_checked = true;
			defNode->children.push_back(assign_addr);

			assign_addr = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), children[0]->children[0]->children[0]->clone());
			assign_addr->children[0]->str = id_addr;
			assign_addr->children[0]->was_checked = true;
			newNode->children.push_back(assign_addr);

			node_addr = new AstNode(AST_IDENTIFIER);
			node_addr->str = id_addr;
		}

		AstNode *node_data = nullptr;
		if (children[0]->children.size() == 1 && children[1]->isConst()) {
			node_data = children[1]->clone();
		} else {
			AstNode *wire_data = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(mem_width-1, true), mkconst_int(0, true)));
			wire_data->str = id_data;
			wire_data->was_checked = true;
			wire_data->is_signed = mem_signed;
			current_ast_mod->children.push_back(wire_data);
			current_scope[wire_data->str] = wire_data;
			while (wire_data->simplify(true, 1, -1, false)) { }

			AstNode *assign_data = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), mkconst_bits(x_bits_data, false));
			assign_data->children[0]->str = id_data;
			assign_data->children[0]->was_checked = true;
			defNode->children.push_back(assign_data);

			node_data = new AstNode(AST_IDENTIFIER);
			node_data->str = id_data;
		}

		AstNode *wire_en = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(mem_width-1, true), mkconst_int(0, true)));
		wire_en->str = id_en;
		wire_en->was_checked = true;
		current_ast_mod->children.push_back(wire_en);
		current_scope[wire_en->str] = wire_en;
		while (wire_en->simplify(true, 1, -1, false)) { }

		AstNode *assign_en_first = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), mkconst_int(0, false, mem_width));
		assign_en_first->children[0]->str = id_en;
		assign_en_first->children[0]->was_checked = true;
		defNode->children.push_back(assign_en_first);

		AstNode *node_en = new AstNode(AST_IDENTIFIER);
		node_en->str = id_en;

		if (!defNode->children.empty())
			current_top_block->children.insert(current_top_block->children.begin(), defNode);
		else
			delete defNode;

		AstNode *assign_data = nullptr;
		AstNode *assign_en = nullptr;
		if (children[0]->children.size() == 2)
		{
			if (children[0]->children[1]->range_valid)
			{
				int offset = children[0]->children[1]->range_right;
				int width = children[0]->children[1]->range_left - offset + 1;
				offset -= mem_data_range_offset;

				std::vector<RTLIL::State> padding_x(offset, RTLIL::State::Sx);

				assign_data = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER),
						new AstNode(AST_CONCAT, mkconst_bits(padding_x, false), children[1]->clone()));
				assign_data->children[0]->str = id_data;
				assign_data->children[0]->was_checked = true;

				for (int i = 0; i < mem_width; i++)
					set_bits_en[i] = offset <= i && i < offset+width ? RTLIL::State::S1 : RTLIL::State::S0;
				assign_en = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), mkconst_bits(set_bits_en, false));
				assign_en->children[0]->str = id_en;
				assign_en->children[0]->was_checked = true;
			}
			else
			{
				AstNode *the_range = children[0]->children[1];
				AstNode *offset_ast;
				int width;

				if (!try_determine_range_width(the_range, width))
					input_error("Unsupported expression on dynamic range select on signal `%s'!\n", str.c_str());

				if (the_range->children.size() >= 2)
					offset_ast = the_range->children[1]->clone();
				else
					offset_ast = the_range->children[0]->clone();

				if (mem_data_range_offset)
					offset_ast = new AstNode(AST_SUB, offset_ast, mkconst_int(mem_data_range_offset, true));

				assign_data = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER),
						new AstNode(AST_SHIFT_LEFT, children[1]->clone(), offset_ast->clone()));
				assign_data->children[0]->str = id_data;
				assign_data->children[0]->was_checked = true;

				for (int i = 0; i < mem_width; i++)
					set_bits_en[i] = i < width ? RTLIL::State::S1 : RTLIL::State::S0;
				assign_en = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER),
						new AstNode(AST_SHIFT_LEFT, mkconst_bits(set_bits_en, false), offset_ast->clone()));
				assign_en->children[0]->str = id_en;
				assign_en->children[0]->was_checked = true;
				delete offset_ast;
			}
		}
		else
		{
			if (!(children[0]->children.size() == 1 && children[1]->isConst())) {
				assign_data = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), children[1]->clone());
				assign_data->children[0]->str = id_data;
				assign_data->children[0]->was_checked = true;
			}

			assign_en = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), mkconst_bits(set_bits_en, false));
			assign_en->children[0]->str = id_en;
			assign_en->children[0]->was_checked = true;
		}
		if (assign_data)
			newNode->children.push_back(assign_data);
		if (assign_en)
			newNode->children.push_back(assign_en);

		AstNode *wrnode;
		if (current_always->type == AST_INITIAL)
			wrnode = new AstNode(AST_MEMINIT, node_addr, node_data, node_en, mkconst_int(1, false));
		else
			wrnode = new AstNode(AST_MEMWR, node_addr, node_data, node_en);
		wrnode->str = children[0]->str;
		wrnode->id2ast = children[0]->id2ast;
		wrnode->location = location;
		if (wrnode->type == AST_MEMWR) {
			int portid = current_memwr_count[wrnode->str]++;
			wrnode->children.push_back(mkconst_int(portid, false));
			std::vector<RTLIL::State> priority_mask;
			for (int i = 0; i < portid; i++) {
				bool has_prio = current_memwr_visible[wrnode->str].count(i);
				priority_mask.push_back(State(has_prio));
			}
			wrnode->children.push_back(mkconst_bits(priority_mask, false));
			current_memwr_visible[wrnode->str].insert(portid);
			current_always->children.push_back(wrnode);
		} else {
			current_ast_mod->children.push_back(wrnode);
		}

		if (newNode->children.empty()) {
			delete newNode;
			newNode = new AstNode();
		}
		goto apply_newNode;
	}

	// replace function and task calls with the code from the function or task
	if ((type == AST_FCALL || type == AST_TCALL) && !str.empty())
	{
		if (type == AST_FCALL)
		{
			if (str == "\\$initstate")
			{
				int myidx = autoidx++;

				AstNode *wire = new AstNode(AST_WIRE);
				wire->str = stringf("$initstate$%d_wire", myidx);
				current_ast_mod->children.push_back(wire);
				while (wire->simplify(true, 1, -1, false)) { }

				AstNode *cell = new AstNode(AST_CELL, new AstNode(AST_CELLTYPE), new AstNode(AST_ARGUMENT, new AstNode(AST_IDENTIFIER)));
				cell->str = stringf("$initstate$%d", myidx);
				cell->children[0]->str = "$initstate";
				cell->children[1]->str = "\\Y";
				cell->children[1]->children[0]->str = wire->str;
				cell->children[1]->children[0]->id2ast = wire;
				current_ast_mod->children.push_back(cell);
				while (cell->simplify(true, 1, -1, false)) { }

				newNode = new AstNode(AST_IDENTIFIER);
				newNode->str = wire->str;
				newNode->id2ast = wire;
				goto apply_newNode;
			}

			if (str == "\\$past")
			{
				if (width_hint < 0)
					goto replace_fcall_later;

				int num_steps = 1;

				if (GetSize(children) != 1 && GetSize(children) != 2)
					input_error("System function %s got %d arguments, expected 1 or 2.\n",
							RTLIL::unescape_id(str).c_str(), int(children.size()));

				if (!current_always_clocked)
					input_error("System function %s is only allowed in clocked blocks.\n",
							RTLIL::unescape_id(str).c_str());

				if (GetSize(children) == 2)
				{
					AstNode *buf = children[1]->clone();
					while (buf->simplify(true, stage, -1, false)) { }
					if (buf->type != AST_CONSTANT)
						input_error("Failed to evaluate system function `%s' with non-constant value.\n", str.c_str());

					num_steps = buf->asInt(true);
					delete buf;
				}

				AstNode *block = nullptr;

				for (auto child : current_always->children)
					if (child->type == AST_BLOCK)
						block = child;

				log_assert(block != nullptr);

				if (num_steps == 0) {
					newNode = children[0]->clone();
					goto apply_newNode;
				}

				int myidx = autoidx++;
				AstNode *outreg = nullptr;

				for (int i = 0; i < num_steps; i++)
				{
					AstNode *reg = new AstNode(AST_WIRE, new AstNode(AST_RANGE,
							mkconst_int(width_hint-1, true), mkconst_int(0, true)));

					reg->str = stringf("$past$%s:%d$%d$%d", RTLIL::encode_filename(filename).c_str(), location.first_line, myidx, i);
					reg->is_reg = true;
					reg->is_signed = sign_hint;

					current_ast_mod->children.push_back(reg);

					while (reg->simplify(true, 1, -1, false)) { }

					AstNode *regid = new AstNode(AST_IDENTIFIER);
					regid->str = reg->str;
					regid->id2ast = reg;
					regid->was_checked = true;

					AstNode *rhs = nullptr;

					if (outreg == nullptr) {
						rhs = children.at(0)->clone();
					} else {
						rhs = new AstNode(AST_IDENTIFIER);
						rhs->str = outreg->str;
						rhs->id2ast = outreg;
					}

					block->children.push_back(new AstNode(AST_ASSIGN_LE, regid, rhs));
					outreg = reg;
				}

				newNode = new AstNode(AST_IDENTIFIER);
				newNode->str = outreg->str;
				newNode->id2ast = outreg;
				goto apply_newNode;
			}

			if (str == "\\$stable" || str == "\\$rose" || str == "\\$fell" || str == "\\$changed")
			{
				if (GetSize(children) != 1)
					input_error("System function %s got %d arguments, expected 1.\n",
							RTLIL::unescape_id(str).c_str(), int(children.size()));

				if (!current_always_clocked)
					input_error("System function %s is only allowed in clocked blocks.\n",
							RTLIL::unescape_id(str).c_str());

				AstNode *present = children.at(0)->clone();
				AstNode *past = clone();
				past->str = "\\$past";

				if (str == "\\$stable")
					newNode = new AstNode(AST_EQ, past, present);

				else if (str == "\\$changed")
					newNode = new AstNode(AST_NE, past, present);

				else if (str == "\\$rose")
					newNode = new AstNode(AST_LOGIC_AND,
							new AstNode(AST_LOGIC_NOT, new AstNode(AST_BIT_AND, past, mkconst_int(1,false))),
							new AstNode(AST_BIT_AND, present, mkconst_int(1,false)));

				else if (str == "\\$fell")
					newNode = new AstNode(AST_LOGIC_AND,
							new AstNode(AST_BIT_AND, past, mkconst_int(1,false)),
							new AstNode(AST_LOGIC_NOT, new AstNode(AST_BIT_AND, present, mkconst_int(1,false))));

				else
					log_abort();

				goto apply_newNode;
			}

			// $anyconst and $anyseq are mapped in AstNode::genRTLIL()
			if (str == "\\$anyconst" || str == "\\$anyseq" || str == "\\$allconst" || str == "\\$allseq") {
				recursion_counter--;
				return false;
			}

			if (str == "\\$clog2")
			{
				if (children.size() != 1)
					input_error("System function %s got %d arguments, expected 1.\n",
							RTLIL::unescape_id(str).c_str(), int(children.size()));

				AstNode *buf = children[0]->clone();
				while (buf->simplify(true, stage, width_hint, sign_hint)) { }
				if (buf->type != AST_CONSTANT)
					input_error("Failed to evaluate system function `%s' with non-constant value.\n", str.c_str());

				RTLIL::Const arg_value = buf->bitsAsConst();
				if (arg_value.as_bool())
					arg_value = const_sub(arg_value, 1, false, false, GetSize(arg_value));
				delete buf;

				uint32_t result = 0;
				for (size_t i = 0; i < arg_value.bits.size(); i++)
					if (arg_value.bits.at(i) == RTLIL::State::S1)
						result = i + 1;

				newNode = mkconst_int(result, true);
				goto apply_newNode;
			}

			if (str == "\\$size" || str == "\\$bits" || str == "\\$high" || str == "\\$low" || str == "\\$left" || str == "\\$right")
			{
				int dim = 1;
				if (str == "\\$bits") {
					if (children.size() != 1)
						input_error("System function %s got %d arguments, expected 1.\n",
								RTLIL::unescape_id(str).c_str(), int(children.size()));
				} else {
					if (children.size() != 1 && children.size() != 2)
						input_error("System function %s got %d arguments, expected 1 or 2.\n",
							RTLIL::unescape_id(str).c_str(), int(children.size()));
					if (children.size() == 2) {
						AstNode *buf = children[1]->clone();
						// Evaluate constant expression
						while (buf->simplify(true, stage, width_hint, sign_hint)) { }
						dim = buf->asInt(false);
						delete buf;
					}
				}
				AstNode *buf = children[0]->clone();
				int mem_depth = 1;
				int result, high = 0, low = 0, left = 0, right = 0, width = 1; // defaults for a simple wire
				AstNode *id_ast = NULL;

				// Is this needed?
				//while (buf->simplify(true, false, stage, width_hint, sign_hint, false)) { }
				buf->detectSignWidth(width_hint, sign_hint);

				if (buf->type == AST_IDENTIFIER) {
					id_ast = buf->id2ast;
					if (id_ast == NULL && current_scope.count(buf->str))
						id_ast = current_scope.at(buf->str);
					if (!id_ast)
						input_error("Failed to resolve identifier %s for width detection!\n", buf->str.c_str());

					// Check for item in packed struct / union
					AST::AstNode *item_node = get_struct_member(buf);
					if (id_ast->type == AST_WIRE && item_node) {
						// The dimension of the original array expression is saved in the 'integer' field
						dim += buf->integer;
						if (item_node->multirange_dimensions.empty()) {
							if (dim != 1)
								input_error("Dimension %d out of range in `%s', as it only has one dimension!\n", dim, item_node->str.c_str());
							left  = high = item_node->range_left;
							right = low  = item_node->range_right;
						} else {
							int dims = GetSize(item_node->multirange_dimensions)/2;
							if (dim < 1 || dim > dims)
								input_error("Dimension %d out of range in `%s', as it only has dimensions 1..%d!\n", dim, item_node->str.c_str(), dims);
							right = low  = get_struct_range_offset(item_node, dim - 1);
							left  = high = low + get_struct_range_width(item_node, dim - 1) - 1;
							if (item_node->multirange_swapped[dim - 1]) {
								std::swap(left, right);
							}
							for (int i = dim; i < dims; i++) {
							    mem_depth *= get_struct_range_width(item_node, i);
							}
						}
					}
					// Otherwise, we have 4 cases:
					// wire x;                ==> AST_WIRE, no AST_RANGE children
					// wire [1:0]x;           ==> AST_WIRE, AST_RANGE children
					// wire [1:0]x[1:0];      ==> AST_MEMORY, two AST_RANGE children (1st for packed, 2nd for unpacked)
					// wire [1:0]x[1:0][1:0]; ==> AST_MEMORY, one AST_RANGE child (0) for packed, then AST_MULTIRANGE child (1) for unpacked
					// (updated: actually by the time we are here, AST_MULTIRANGE is converted into one big AST_RANGE)
					// case 0 handled by default
					else if ((id_ast->type == AST_WIRE || id_ast->type == AST_MEMORY) && id_ast->children.size() > 0) {
						// handle packed array left/right for case 1, and cases 2/3 when requesting the last dimension (packed side)
						AstNode *wire_range = id_ast->children[0];
						left = wire_range->children[0]->integer;
						right = wire_range->children[1]->integer;
						high = max(left, right);
						low  = min(left, right);
					}
					if (id_ast->type == AST_MEMORY) {
						// a slice of our identifier means we advance to the next dimension, e.g. $size(a[3])
						if (buf->children.size() > 0) {
							// something is hanging below this identifier
							if (buf->children[0]->type == AST_RANGE && buf->integer == 0)
								// if integer == 0, this node was originally created as AST_RANGE so it's dimension is 1
								dim++;
							// more than one range, e.g. $size(a[3][2])
							else // created an AST_MULTIRANGE, converted to AST_RANGE, but original dimension saved in 'integer' field
								dim += buf->integer; // increment by multirange size
						}

						// We got here only if the argument is a memory
						// Otherwise $size() and $bits() return the expression width
						AstNode *mem_range = id_ast->children[1];
						if (str == "\\$bits") {
							if (mem_range->type == AST_RANGE) {
								if (!mem_range->range_valid)
									input_error("Failed to detect width of memory access `%s'!\n", buf->str.c_str());
								mem_depth = mem_range->range_left - mem_range->range_right + 1;
							} else
								input_error("Unknown memory depth AST type in `%s'!\n", buf->str.c_str());
						} else {
							// $size(), $left(), $right(), $high(), $low()
							int dims = 1;
							if (mem_range->type == AST_RANGE) {
								if (id_ast->multirange_dimensions.empty()) {
									if (!mem_range->range_valid)
										input_error("Failed to detect width of memory access `%s'!\n", buf->str.c_str());
									if (dim == 1) {
										left  = mem_range->range_right;
										right = mem_range->range_left;
										high = max(left, right);
										low  = min(left, right);
									}
								} else {
									dims = GetSize(id_ast->multirange_dimensions)/2;
									if (dim <= dims) {
										width_hint = id_ast->multirange_dimensions[2*dim-1];
										high = id_ast->multirange_dimensions[2*dim-2] + id_ast->multirange_dimensions[2*dim-1] - 1;
										low  = id_ast->multirange_dimensions[2*dim-2];
										if (id_ast->multirange_swapped[dim-1]) {
											left = low;
											right = high;
										} else {
											right = low;
											left = high;
										}
									} else if ((dim > dims+1) || (dim < 0))
										input_error("Dimension %d out of range in `%s', as it only has dimensions 1..%d!\n", dim, buf->str.c_str(), dims+1);
								}
							} else {
								input_error("Unknown memory depth AST type in `%s'!\n", buf->str.c_str());
							}
						}
					}
					width = high - low + 1;
				} else {
					width = width_hint;
				}
				delete buf;
				if (str == "\\$high")
					result = high;
				else if (str == "\\$low")
					result = low;
				else if (str == "\\$left")
					result = left;
				else if (str == "\\$right")
					result = right;
				else if (str == "\\$size")
					result = width;
				else { // str == "\\$bits"
					result = width * mem_depth;
				}
				newNode = mkconst_int(result, true);
				goto apply_newNode;
			}

			if (str == "\\$ln" || str == "\\$log10" || str == "\\$exp" || str == "\\$sqrt" || str == "\\$pow" ||
					str == "\\$floor" || str == "\\$ceil" || str == "\\$sin" || str == "\\$cos" || str == "\\$tan" ||
					str == "\\$asin" || str == "\\$acos" || str == "\\$atan" || str == "\\$atan2" || str == "\\$hypot" ||
					str == "\\$sinh" || str == "\\$cosh" || str == "\\$tanh" || str == "\\$asinh" || str == "\\$acosh" || str == "\\$atanh" ||
					str == "\\$rtoi" || str == "\\$itor")
			{
				bool func_with_two_arguments = str == "\\$pow" || str == "\\$atan2" || str == "\\$hypot";
				double x = 0, y = 0;

				if (func_with_two_arguments) {
					if (children.size() != 2)
						input_error("System function %s got %d arguments, expected 2.\n",
								RTLIL::unescape_id(str).c_str(), int(children.size()));
				} else {
					if (children.size() != 1)
						input_error("System function %s got %d arguments, expected 1.\n",
								RTLIL::unescape_id(str).c_str(), int(children.size()));
				}

				if (children.size() >= 1) {
					while (children[0]->simplify(true, stage, width_hint, sign_hint)) { }
					if (!children[0]->isConst())
						input_error("Failed to evaluate system function `%s' with non-constant argument.\n",
								RTLIL::unescape_id(str).c_str());
					int child_width_hint = width_hint;
					bool child_sign_hint = sign_hint;
					children[0]->detectSignWidth(child_width_hint, child_sign_hint);
					x = children[0]->asReal(child_sign_hint);
				}

				if (children.size() >= 2) {
					while (children[1]->simplify(true, stage, width_hint, sign_hint)) { }
					if (!children[1]->isConst())
						input_error("Failed to evaluate system function `%s' with non-constant argument.\n",
								RTLIL::unescape_id(str).c_str());
					int child_width_hint = width_hint;
					bool child_sign_hint = sign_hint;
					children[1]->detectSignWidth(child_width_hint, child_sign_hint);
					y = children[1]->asReal(child_sign_hint);
				}

				if (str == "\\$rtoi") {
					newNode = AstNode::mkconst_int(x, true);
				} else {
					newNode = new AstNode(AST_REALVALUE);
					if (str == "\\$ln")         newNode->realvalue = ::log(x);
					else if (str == "\\$log10") newNode->realvalue = ::log10(x);
					else if (str == "\\$exp")   newNode->realvalue = ::exp(x);
					else if (str == "\\$sqrt")  newNode->realvalue = ::sqrt(x);
					else if (str == "\\$pow")   newNode->realvalue = ::pow(x, y);
					else if (str == "\\$floor") newNode->realvalue = ::floor(x);
					else if (str == "\\$ceil")  newNode->realvalue = ::ceil(x);
					else if (str == "\\$sin")   newNode->realvalue = ::sin(x);
					else if (str == "\\$cos")   newNode->realvalue = ::cos(x);
					else if (str == "\\$tan")   newNode->realvalue = ::tan(x);
					else if (str == "\\$asin")  newNode->realvalue = ::asin(x);
					else if (str == "\\$acos")  newNode->realvalue = ::acos(x);
					else if (str == "\\$atan")  newNode->realvalue = ::atan(x);
					else if (str == "\\$atan2") newNode->realvalue = ::atan2(x, y);
					else if (str == "\\$hypot") newNode->realvalue = ::hypot(x, y);
					else if (str == "\\$sinh")  newNode->realvalue = ::sinh(x);
					else if (str == "\\$cosh")  newNode->realvalue = ::cosh(x);
					else if (str == "\\$tanh")  newNode->realvalue = ::tanh(x);
					else if (str == "\\$asinh") newNode->realvalue = ::asinh(x);
					else if (str == "\\$acosh") newNode->realvalue = ::acosh(x);
					else if (str == "\\$atanh") newNode->realvalue = ::atanh(x);
					else if (str == "\\$itor")  newNode->realvalue = x;
					else log_abort();
				}
				goto apply_newNode;
			}

			if (str == "\\$sformatf") {
				Fmt fmt = processFormat(stage, /*sformat_like=*/true);
				newNode = AstNode::mkconst_str(fmt.render());
				goto apply_newNode;
			}

			if (str == "\\$countbits") {
				if (children.size() < 2)
					input_error("System function %s got %d arguments, expected at least 2.\n",
							RTLIL::unescape_id(str).c_str(), int(children.size()));

				std::vector<RTLIL::State> control_bits;

				// Determine which bits to count
				for (size_t i = 1; i < children.size(); i++) {
					AstNode *node = children[i];
					while (node->simplify(true, stage, -1, false)) { }
					if (node->type != AST_CONSTANT)
						input_error("Failed to evaluate system function `%s' with non-constant control bit argument.\n", str.c_str());
					if (node->bits.size() != 1)
						input_error("Failed to evaluate system function `%s' with control bit width != 1.\n", str.c_str());
					control_bits.push_back(node->bits[0]);
				}

				// Detect width of exp (first argument of $countbits)
				int  exp_width = -1;
				bool exp_sign  = false;
				AstNode *exp = children[0];
				exp->detectSignWidth(exp_width, exp_sign, NULL);

				newNode = mkconst_int(0, false);

				for (int i = 0; i < exp_width; i++) {
					// Generate nodes for:  exp << i >> ($size(exp) - 1)
					//                          ^^   ^^
					AstNode *lsh_node = new AstNode(AST_SHIFT_LEFT, exp->clone(), mkconst_int(i, false));
					AstNode *rsh_node = new AstNode(AST_SHIFT_RIGHT, lsh_node, mkconst_int(exp_width - 1, false));

					AstNode *or_node = nullptr;

					for (RTLIL::State control_bit : control_bits) {
						// Generate node for:  (exp << i >> ($size(exp) - 1)) === control_bit
						//                                                    ^^^
						AstNode *eq_node = new AstNode(AST_EQX, rsh_node->clone(), mkconst_bits({control_bit}, false));

						// Or the result for each checked bit value
						if (or_node)
							or_node = new AstNode(AST_LOGIC_OR, or_node, eq_node);
						else
							or_node = eq_node;
					}

					// We should have at least one element in control_bits,
					// because we checked for the number of arguments above
					log_assert(or_node != nullptr);

					delete rsh_node;

					// Generate node for adding with result of previous bit
					newNode = new AstNode(AST_ADD, newNode, or_node);
				}

				goto apply_newNode;
			}

			if (str == "\\$countones" || str == "\\$isunknown" || str == "\\$onehot" || str == "\\$onehot0") {
				if (children.size() != 1)
					input_error("System function %s got %d arguments, expected 1.\n",
							RTLIL::unescape_id(str).c_str(), int(children.size()));

				AstNode *countbits = clone();
				countbits->str = "\\$countbits";

				if (str == "\\$countones") {
					countbits->children.push_back(mkconst_bits({RTLIL::State::S1}, false));
					newNode = countbits;
				} else if (str == "\\$isunknown") {
					countbits->children.push_back(mkconst_bits({RTLIL::Sx}, false));
					countbits->children.push_back(mkconst_bits({RTLIL::Sz}, false));
					newNode = new AstNode(AST_GT, countbits, mkconst_int(0, false));
				} else if (str == "\\$onehot") {
					countbits->children.push_back(mkconst_bits({RTLIL::State::S1}, false));
					newNode = new AstNode(AST_EQ, countbits, mkconst_int(1, false));
				} else if (str == "\\$onehot0") {
					countbits->children.push_back(mkconst_bits({RTLIL::State::S1}, false));
					newNode = new AstNode(AST_LE, countbits, mkconst_int(1, false));
				} else {
					log_abort();
				}

				goto apply_newNode;
			}

			if (current_scope.count(str) != 0 && current_scope[str]->type == AST_DPI_FUNCTION)
			{
				AstNode *dpi_decl = current_scope[str];

				std::string rtype, fname;
				std::vector<std::string> argtypes;
				std::vector<AstNode*> args;

				rtype = RTLIL::unescape_id(dpi_decl->children.at(0)->str);
				fname = RTLIL::unescape_id(dpi_decl->children.at(1)->str);

				for (int i = 2; i < GetSize(dpi_decl->children); i++)
				{
					if (i-2 >= GetSize(children))
						input_error("Insufficient number of arguments in DPI function call.\n");

					argtypes.push_back(RTLIL::unescape_id(dpi_decl->children.at(i)->str));
					args.push_back(children.at(i-2)->clone());
					while (args.back()->simplify(true, stage, -1, false)) { }

					if (args.back()->type != AST_CONSTANT && args.back()->type != AST_REALVALUE)
						input_error("Failed to evaluate DPI function with non-constant argument.\n");
				}

				newNode = dpi_call(rtype, fname, argtypes, args);

				for (auto arg : args)
					delete arg;

				goto apply_newNode;
			}

			if (current_scope.count(str) == 0)
				str = try_pop_module_prefix();
			if (current_scope.count(str) == 0 || current_scope[str]->type != AST_FUNCTION)
				input_error("Can't resolve function name `%s'.\n", str.c_str());
		}

		if (type == AST_TCALL)
		{
			if (str == "$finish" || str == "$stop")
			{
				if (!current_always || current_always->type != AST_INITIAL)
					input_error("System task `%s' outside initial block is unsupported.\n", str.c_str());

				input_error("System task `%s' executed.\n", str.c_str());
			}

			if (str == "\\$readmemh" || str == "\\$readmemb")
			{
				if (GetSize(children) < 2 || GetSize(children) > 4)
					input_error("System function %s got %d arguments, expected 2-4.\n",
							RTLIL::unescape_id(str).c_str(), int(children.size()));

				AstNode *node_filename = children[0]->clone();
				while (node_filename->simplify(true, stage, width_hint, sign_hint)) { }
				if (node_filename->type != AST_CONSTANT)
					input_error("Failed to evaluate system function `%s' with non-constant 1st argument.\n", str.c_str());

				AstNode *node_memory = children[1]->clone();
				while (node_memory->simplify(true, stage, width_hint, sign_hint)) { }
				if (node_memory->type != AST_IDENTIFIER || node_memory->id2ast == nullptr || node_memory->id2ast->type != AST_MEMORY)
					input_error("Failed to evaluate system function `%s' with non-memory 2nd argument.\n", str.c_str());

				int start_addr = -1, finish_addr = -1;

				if (GetSize(children) > 2) {
					AstNode *node_addr = children[2]->clone();
					while (node_addr->simplify(true, stage, width_hint, sign_hint)) { }
					if (node_addr->type != AST_CONSTANT)
						input_error("Failed to evaluate system function `%s' with non-constant 3rd argument.\n", str.c_str());
					start_addr = int(node_addr->asInt(false));
				}

				if (GetSize(children) > 3) {
					AstNode *node_addr = children[3]->clone();
					while (node_addr->simplify(true, stage, width_hint, sign_hint)) { }
					if (node_addr->type != AST_CONSTANT)
						input_error("Failed to evaluate system function `%s' with non-constant 4th argument.\n", str.c_str());
					finish_addr = int(node_addr->asInt(false));
				}

				bool unconditional_init = false;
				if (current_always->type == AST_INITIAL) {
					pool<AstNode*> queue;
					log_assert(current_always->children[0]->type == AST_BLOCK);
					queue.insert(current_always->children[0]);
					while (!unconditional_init && !queue.empty()) {
						pool<AstNode*> next_queue;
						for (auto n : queue)
						for (auto c : n->children) {
							if (c == this)
								unconditional_init = true;
							next_queue.insert(c);
						}
						next_queue.swap(queue);
					}
				}

				newNode = readmem(str == "\\$readmemh", node_filename->bitsAsConst().decode_string(), node_memory->id2ast, start_addr, finish_addr, unconditional_init);
				delete node_filename;
				delete node_memory;
				goto apply_newNode;
			}

			if (current_scope.count(str) == 0)
				str = try_pop_module_prefix();
			if (current_scope.count(str) == 0 || current_scope[str]->type != AST_TASK)
				input_error("Can't resolve task name `%s'.\n", str.c_str());
		}


		std::stringstream sstr;
		sstr << str << "$func$" << RTLIL::encode_filename(filename) << ":" << location.first_line << "$" << (autoidx++) << '.';
		std::string prefix = sstr.str();

		AstNode *decl = current_scope[str];
		if (unevaluated_tern_branch && decl->is_recursive_function())
			goto replace_fcall_later;
		decl = decl->clone();
		decl->replace_result_wire_name_in_function(str, "$result"); // enables recursion
		decl->expand_genblock(prefix);

		if (decl->type == AST_FUNCTION && !decl->attributes.count(ID::via_celltype))
		{
			bool require_const_eval = decl->has_const_only_constructs();
			bool all_args_const = true;
			for (auto child : children) {
				while (child->simplify(true, 1, -1, false)) { }
				if (child->type != AST_CONSTANT && child->type != AST_REALVALUE)
					all_args_const = false;
			}

			if (all_args_const) {
				AstNode *func_workspace = decl->clone();
				func_workspace->set_in_param_flag(true);
				func_workspace->str = prefix_id(prefix, "$result");
				newNode = func_workspace->eval_const_function(this, in_param || require_const_eval);
				delete func_workspace;
				if (newNode) {
					delete decl;
					goto apply_newNode;
				}
			}

			if (in_param)
				input_error("Non-constant function call in constant expression.\n");
			if (require_const_eval)
				input_error("Function %s can only be called with constant arguments.\n", str.c_str());
		}

		size_t arg_count = 0;
		dict<std::string, AstNode*> wire_cache;
		vector<AstNode*> new_stmts;
		vector<AstNode*> output_assignments;

		if (current_block == NULL)
		{
			log_assert(type == AST_FCALL);

			AstNode *wire = NULL;
			std::string res_name = prefix_id(prefix, "$result");
			for (auto child : decl->children)
				if (child->type == AST_WIRE && child->str == res_name)
					wire = child->clone();
			log_assert(wire != NULL);

			wire->port_id = 0;
			wire->is_input = false;
			wire->is_output = false;

			current_scope[wire->str] = wire;
			current_ast_mod->children.push_back(wire);
			while (wire->simplify(true, 1, -1, false)) { }

			AstNode *lvalue = new AstNode(AST_IDENTIFIER);
			lvalue->str = wire->str;

			AstNode *always = new AstNode(AST_ALWAYS, new AstNode(AST_BLOCK,
					new AstNode(AST_ASSIGN_EQ, lvalue, clone())));
			always->children[0]->children[0]->was_checked = true;

			current_ast_mod->children.push_back(always);

			goto replace_fcall_with_id;
		}

		if (decl->attributes.count(ID::via_celltype))
		{
			std::string celltype = decl->attributes.at(ID::via_celltype)->asAttrConst().decode_string();
			std::string outport = str;

			if (celltype.find(' ') != std::string::npos) {
				int pos = celltype.find(' ');
				outport = RTLIL::escape_id(celltype.substr(pos+1));
				celltype = RTLIL::escape_id(celltype.substr(0, pos));
			} else
				celltype = RTLIL::escape_id(celltype);

			AstNode *cell = new AstNode(AST_CELL, new AstNode(AST_CELLTYPE));
			cell->str = prefix.substr(0, GetSize(prefix)-1);
			cell->children[0]->str = celltype;

			for (auto attr : decl->attributes)
				if (attr.first.str().rfind("\\via_celltype_defparam_", 0) == 0)
				{
					AstNode *cell_arg = new AstNode(AST_PARASET, attr.second->clone());
					cell_arg->str = RTLIL::escape_id(attr.first.substr(strlen("\\via_celltype_defparam_")));
					cell->children.push_back(cell_arg);
				}

			for (auto child : decl->children)
				if (child->type == AST_WIRE && (child->is_input || child->is_output || (type == AST_FCALL && child->str == str)))
				{
					AstNode *wire = child->clone();
					wire->port_id = 0;
					wire->is_input = false;
					wire->is_output = false;
					current_ast_mod->children.push_back(wire);
					while (wire->simplify(true, 1, -1, false)) { }

					AstNode *wire_id = new AstNode(AST_IDENTIFIER);
					wire_id->str = wire->str;

					if ((child->is_input || child->is_output) && arg_count < children.size())
					{
						AstNode *arg = children[arg_count++]->clone();
						AstNode *assign = child->is_input ?
								new AstNode(AST_ASSIGN_EQ, wire_id->clone(), arg) :
								new AstNode(AST_ASSIGN_EQ, arg, wire_id->clone());
						assign->children[0]->was_checked = true;

						for (auto it = current_block->children.begin(); it != current_block->children.end(); it++) {
							if (*it != current_block_child)
								continue;
							current_block->children.insert(it, assign);
							break;
						}
					}

					AstNode *cell_arg = new AstNode(AST_ARGUMENT, wire_id);
					cell_arg->str = child->str == str ? outport : child->str;
					cell->children.push_back(cell_arg);
				}

			current_ast_mod->children.push_back(cell);
			goto replace_fcall_with_id;
		}

		for (auto child : decl->children)
			if (child->type == AST_WIRE || child->type == AST_MEMORY || child->type == AST_PARAMETER || child->type == AST_LOCALPARAM || child->type == AST_ENUM_ITEM)
			{
				AstNode *wire = nullptr;

				if (wire_cache.count(child->str))
				{
					wire = wire_cache.at(child->str);
					bool contains_value = wire->type == AST_LOCALPARAM;
					if (wire->children.size() == contains_value) {
						for (auto c : child->children)
							wire->children.push_back(c->clone());
					} else if (!child->children.empty()) {
						while (child->simplify(true, stage, -1, false)) { }
						if (GetSize(child->children) == GetSize(wire->children) - contains_value) {
							for (int i = 0; i < GetSize(child->children); i++)
								if (*child->children.at(i) != *wire->children.at(i + contains_value))
									goto tcall_incompatible_wires;
						} else {
					tcall_incompatible_wires:
							input_error("Incompatible re-declaration of wire %s.\n", child->str.c_str());
						}
					}
				}
				else
				{
					wire = child->clone();
					wire->port_id = 0;
					wire->is_input = false;
					wire->is_output = false;
					wire->is_reg = true;
					wire->set_attribute(ID::nosync, AstNode::mkconst_int(1, false));
					if (child->type == AST_ENUM_ITEM)
						wire->set_attribute(ID::enum_base_type, child->attributes[ID::enum_base_type]);

					wire_cache[child->str] = wire;

					current_scope[wire->str] = wire;
					current_ast_mod->children.push_back(wire);
				}

				while (wire->simplify(true, 1, -1, false)) { }

				if ((child->is_input || child->is_output) && arg_count < children.size())
				{
					AstNode *arg = children[arg_count++]->clone();
					// convert purely constant arguments into localparams
					if (child->is_input && child->type == AST_WIRE && arg->type == AST_CONSTANT && node_contains_assignment_to(decl, child)) {
						wire->type = AST_LOCALPARAM;
						if (wire->attributes.count(ID::nosync))
							delete wire->attributes.at(ID::nosync);
						wire->attributes.erase(ID::nosync);
						wire->children.insert(wire->children.begin(), arg->clone());
						// args without a range implicitly have width 1
						if (wire->children.back()->type != AST_RANGE) {
							// check if this wire is redeclared with an explicit size
							bool uses_explicit_size = false;
							for (const AstNode *other_child : decl->children)
								if (other_child->type == AST_WIRE && child->str == other_child->str
										&& !other_child->children.empty()
										&& other_child->children.back()->type == AST_RANGE) {
									uses_explicit_size = true;
									break;
								}
							if (!uses_explicit_size) {
								AstNode* range = new AstNode();
								range->type = AST_RANGE;
								wire->children.push_back(range);
								range->children.push_back(mkconst_int(0, true));
								range->children.push_back(mkconst_int(0, true));
							}
						}
						wire->fixup_hierarchy_flags();
						// updates the sizing
						while (wire->simplify(true, 1, -1, false)) { }
						delete arg;
						continue;
					}
					AstNode *wire_id = new AstNode(AST_IDENTIFIER);
					wire_id->str = wire->str;
					AstNode *assign = child->is_input ?
							new AstNode(AST_ASSIGN_EQ, wire_id, arg) :
							new AstNode(AST_ASSIGN_EQ, arg, wire_id);
					assign->children[0]->was_checked = true;
					if (child->is_input)
						new_stmts.push_back(assign);
					else
						output_assignments.push_back(assign);
				}
			}

		for (auto child : decl->children)
			if (child->type != AST_WIRE && child->type != AST_MEMORY && child->type != AST_PARAMETER && child->type != AST_LOCALPARAM)
				new_stmts.push_back(child->clone());

		new_stmts.insert(new_stmts.end(), output_assignments.begin(), output_assignments.end());

		for (auto it = current_block->children.begin(); ; it++) {
			log_assert(it != current_block->children.end());
			if (*it == current_block_child) {
				current_block->children.insert(it, new_stmts.begin(), new_stmts.end());
				break;
			}
		}

	replace_fcall_with_id:
		delete decl;
		if (type == AST_FCALL) {
			delete_children();
			type = AST_IDENTIFIER;
			str = prefix_id(prefix, "$result");
		}
		if (type == AST_TCALL)
			str = "";
		did_something = true;
	}

replace_fcall_later:;

	// perform const folding when activated
	if (const_fold)
	{
		bool string_op;
		std::vector<RTLIL::State> tmp_bits;
		RTLIL::Const (*const_func)(const RTLIL::Const&, const RTLIL::Const&, bool, bool, int);
		RTLIL::Const dummy_arg;

		switch (type)
		{
		case AST_IDENTIFIER:
			if (current_scope.count(str) > 0 && (current_scope[str]->type == AST_PARAMETER || current_scope[str]->type == AST_LOCALPARAM || current_scope[str]->type == AST_ENUM_ITEM)) {
				if (current_scope[str]->children[0]->type == AST_CONSTANT) {
					if (children.size() != 0 && children[0]->type == AST_RANGE && children[0]->range_valid) {
						std::vector<RTLIL::State> data;
						bool param_upto = current_scope[str]->range_valid && current_scope[str]->range_swapped;
						int param_offset = current_scope[str]->range_valid ? current_scope[str]->range_right : 0;
						int param_width = current_scope[str]->range_valid ? current_scope[str]->range_left - current_scope[str]->range_right + 1 :
								GetSize(current_scope[str]->children[0]->bits);
						int tmp_range_left = children[0]->range_left, tmp_range_right = children[0]->range_right;
						if (param_upto) {
							tmp_range_left = (param_width + 2*param_offset) - children[0]->range_right - 1;
							tmp_range_right = (param_width + 2*param_offset) - children[0]->range_left - 1;
						}
						AST::AstNode *member_node = get_struct_member(this);
						int chunk_offset = member_node ? member_node->range_right : 0;
						log_assert(!(chunk_offset && param_upto));
						for (int i = tmp_range_right; i <= tmp_range_left; i++) {
							int index = i - param_offset;
							if (0 <= index && index < param_width)
								data.push_back(current_scope[str]->children[0]->bits[chunk_offset + index]);
							else
								data.push_back(RTLIL::State::Sx);
						}
						newNode = mkconst_bits(data, false);
					} else
					if (children.size() == 0)
						newNode = current_scope[str]->children[0]->clone();
				} else
				if (current_scope[str]->children[0]->isConst())
					newNode = current_scope[str]->children[0]->clone();
			}
			break;
		case AST_BIT_NOT:
			if (children[0]->type == AST_CONSTANT) {
				RTLIL::Const y = RTLIL::const_not(children[0]->bitsAsConst(width_hint, sign_hint), dummy_arg, sign_hint, false, width_hint);
				newNode = mkconst_bits(y.bits, sign_hint);
			}
			break;
		case AST_TO_SIGNED:
		case AST_TO_UNSIGNED:
			if (children[0]->type == AST_CONSTANT) {
				RTLIL::Const y = children[0]->bitsAsConst(width_hint, sign_hint);
				newNode = mkconst_bits(y.bits, type == AST_TO_SIGNED);
			}
			break;
		if (0) { case AST_BIT_AND:  const_func = RTLIL::const_and;  }
		if (0) { case AST_BIT_OR:   const_func = RTLIL::const_or;   }
		if (0) { case AST_BIT_XOR:  const_func = RTLIL::const_xor;  }
		if (0) { case AST_BIT_XNOR: const_func = RTLIL::const_xnor; }
			if (children[0]->type == AST_CONSTANT && children[1]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(children[0]->bitsAsConst(width_hint, sign_hint),
						children[1]->bitsAsConst(width_hint, sign_hint), sign_hint, sign_hint, width_hint);
				newNode = mkconst_bits(y.bits, sign_hint);
			}
			break;
		if (0) { case AST_REDUCE_AND:  const_func = RTLIL::const_reduce_and;  }
		if (0) { case AST_REDUCE_OR:   const_func = RTLIL::const_reduce_or;   }
		if (0) { case AST_REDUCE_XOR:  const_func = RTLIL::const_reduce_xor;  }
		if (0) { case AST_REDUCE_XNOR: const_func = RTLIL::const_reduce_xnor; }
		if (0) { case AST_REDUCE_BOOL: const_func = RTLIL::const_reduce_bool; }
			if (children[0]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(RTLIL::Const(children[0]->bits), dummy_arg, false, false, -1);
				newNode = mkconst_bits(y.bits, false);
			}
			break;
		case AST_LOGIC_NOT:
			if (children[0]->type == AST_CONSTANT) {
				RTLIL::Const y = RTLIL::const_logic_not(RTLIL::Const(children[0]->bits), dummy_arg, children[0]->is_signed, false, -1);
				newNode = mkconst_bits(y.bits, false);
			} else
			if (children[0]->isConst()) {
				newNode = mkconst_int(children[0]->asReal(sign_hint) == 0, false, 1);
			}
			break;
		if (0) { case AST_LOGIC_AND: const_func = RTLIL::const_logic_and; }
		if (0) { case AST_LOGIC_OR:  const_func = RTLIL::const_logic_or;  }
			if (children[0]->type == AST_CONSTANT && children[1]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(RTLIL::Const(children[0]->bits), RTLIL::Const(children[1]->bits),
						children[0]->is_signed, children[1]->is_signed, -1);
				newNode = mkconst_bits(y.bits, false);
			} else
			if (children[0]->isConst() && children[1]->isConst()) {
				if (type == AST_LOGIC_AND)
					newNode = mkconst_int((children[0]->asReal(sign_hint) != 0) && (children[1]->asReal(sign_hint) != 0), false, 1);
				else
					newNode = mkconst_int((children[0]->asReal(sign_hint) != 0) || (children[1]->asReal(sign_hint) != 0), false, 1);
			}
			break;
		if (0) { case AST_SHIFT_LEFT:   const_func = RTLIL::const_shl;  }
		if (0) { case AST_SHIFT_RIGHT:  const_func = RTLIL::const_shr;  }
		if (0) { case AST_SHIFT_SLEFT:  const_func = RTLIL::const_sshl; }
		if (0) { case AST_SHIFT_SRIGHT: const_func = RTLIL::const_sshr; }
		if (0) { case AST_POW:          const_func = RTLIL::const_pow; }
			if (children[0]->type == AST_CONSTANT && children[1]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(children[0]->bitsAsConst(width_hint, sign_hint),
						RTLIL::Const(children[1]->bits), sign_hint, type == AST_POW ? children[1]->is_signed : false, width_hint);
				newNode = mkconst_bits(y.bits, sign_hint);
			} else
			if (type == AST_POW && children[0]->isConst() && children[1]->isConst()) {
				newNode = new AstNode(AST_REALVALUE);
				newNode->realvalue = pow(children[0]->asReal(sign_hint), children[1]->asReal(sign_hint));
			}
			break;
		if (0) { case AST_LT:  const_func = RTLIL::const_lt; }
		if (0) { case AST_LE:  const_func = RTLIL::const_le; }
		if (0) { case AST_EQ:  const_func = RTLIL::const_eq; }
		if (0) { case AST_NE:  const_func = RTLIL::const_ne; }
		if (0) { case AST_EQX: const_func = RTLIL::const_eqx; }
		if (0) { case AST_NEX: const_func = RTLIL::const_nex; }
		if (0) { case AST_GE:  const_func = RTLIL::const_ge; }
		if (0) { case AST_GT:  const_func = RTLIL::const_gt; }
			if (children[0]->type == AST_CONSTANT && children[1]->type == AST_CONSTANT) {
				int cmp_width = max(children[0]->bits.size(), children[1]->bits.size());
				bool cmp_signed = children[0]->is_signed && children[1]->is_signed;
				RTLIL::Const y = const_func(children[0]->bitsAsConst(cmp_width, cmp_signed),
						children[1]->bitsAsConst(cmp_width, cmp_signed), cmp_signed, cmp_signed, 1);
				newNode = mkconst_bits(y.bits, false);
			} else
			if (children[0]->isConst() && children[1]->isConst()) {
				bool cmp_signed = (children[0]->type == AST_REALVALUE || children[0]->is_signed) && (children[1]->type == AST_REALVALUE || children[1]->is_signed);
				switch (type) {
				case AST_LT:  newNode = mkconst_int(children[0]->asReal(cmp_signed) <  children[1]->asReal(cmp_signed), false, 1); break;
				case AST_LE:  newNode = mkconst_int(children[0]->asReal(cmp_signed) <= children[1]->asReal(cmp_signed), false, 1); break;
				case AST_EQ:  newNode = mkconst_int(children[0]->asReal(cmp_signed) == children[1]->asReal(cmp_signed), false, 1); break;
				case AST_NE:  newNode = mkconst_int(children[0]->asReal(cmp_signed) != children[1]->asReal(cmp_signed), false, 1); break;
				case AST_EQX: newNode = mkconst_int(children[0]->asReal(cmp_signed) == children[1]->asReal(cmp_signed), false, 1); break;
				case AST_NEX: newNode = mkconst_int(children[0]->asReal(cmp_signed) != children[1]->asReal(cmp_signed), false, 1); break;
				case AST_GE:  newNode = mkconst_int(children[0]->asReal(cmp_signed) >= children[1]->asReal(cmp_signed), false, 1); break;
				case AST_GT:  newNode = mkconst_int(children[0]->asReal(cmp_signed) >  children[1]->asReal(cmp_signed), false, 1); break;
				default: log_abort();
				}
			}
			break;
		if (0) { case AST_ADD: const_func = RTLIL::const_add; }
		if (0) { case AST_SUB: const_func = RTLIL::const_sub; }
		if (0) { case AST_MUL: const_func = RTLIL::const_mul; }
		if (0) { case AST_DIV: const_func = RTLIL::const_div; }
		if (0) { case AST_MOD: const_func = RTLIL::const_mod; }
			if (children[0]->type == AST_CONSTANT && children[1]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(children[0]->bitsAsConst(width_hint, sign_hint),
						children[1]->bitsAsConst(width_hint, sign_hint), sign_hint, sign_hint, width_hint);
				newNode = mkconst_bits(y.bits, sign_hint);
			} else
			if (children[0]->isConst() && children[1]->isConst()) {
				newNode = new AstNode(AST_REALVALUE);
				switch (type) {
				case AST_ADD: newNode->realvalue = children[0]->asReal(sign_hint) + children[1]->asReal(sign_hint); break;
				case AST_SUB: newNode->realvalue = children[0]->asReal(sign_hint) - children[1]->asReal(sign_hint); break;
				case AST_MUL: newNode->realvalue = children[0]->asReal(sign_hint) * children[1]->asReal(sign_hint); break;
				case AST_DIV: newNode->realvalue = children[0]->asReal(sign_hint) / children[1]->asReal(sign_hint); break;
				case AST_MOD: newNode->realvalue = fmod(children[0]->asReal(sign_hint), children[1]->asReal(sign_hint)); break;
				default: log_abort();
				}
			}
			break;
		if (0) { case AST_SELFSZ: const_func = RTLIL::const_pos; }
		if (0) { case AST_POS: const_func = RTLIL::const_pos; }
		if (0) { case AST_NEG: const_func = RTLIL::const_neg; }
			if (children[0]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(children[0]->bitsAsConst(width_hint, sign_hint), dummy_arg, sign_hint, false, width_hint);
				newNode = mkconst_bits(y.bits, sign_hint);
			} else
			if (children[0]->isConst()) {
				newNode = new AstNode(AST_REALVALUE);
				if (type == AST_NEG)
					newNode->realvalue = -children[0]->asReal(sign_hint);
				else
					newNode->realvalue = +children[0]->asReal(sign_hint);
			}
			break;
		case AST_TERNARY:
			if (children[0]->isConst())
			{
				auto pair = get_tern_choice();
				AstNode *choice = pair.first;
				AstNode *not_choice = pair.second;

				if (choice != NULL) {
					if (choice->type == AST_CONSTANT) {
						int other_width_hint = width_hint;
						bool other_sign_hint = sign_hint, other_real = false;
						not_choice->detectSignWidth(other_width_hint, other_sign_hint, &other_real);
						if (other_real) {
							newNode = new AstNode(AST_REALVALUE);
							choice->detectSignWidth(width_hint, sign_hint);
							newNode->realvalue = choice->asReal(sign_hint);
						} else {
							RTLIL::Const y = choice->bitsAsConst(width_hint, sign_hint);
							if (choice->is_string && y.bits.size() % 8 == 0 && sign_hint == false)
								newNode = mkconst_str(y.bits);
							else
								newNode = mkconst_bits(y.bits, sign_hint);
						}
					} else
					if (choice->isConst()) {
						newNode = choice->clone();
					}
				} else if (children[1]->type == AST_CONSTANT && children[2]->type == AST_CONSTANT) {
					RTLIL::Const a = children[1]->bitsAsConst(width_hint, sign_hint);
					RTLIL::Const b = children[2]->bitsAsConst(width_hint, sign_hint);
					log_assert(a.bits.size() == b.bits.size());
					for (size_t i = 0; i < a.bits.size(); i++)
						if (a.bits[i] != b.bits[i])
							a.bits[i] = RTLIL::State::Sx;
					newNode = mkconst_bits(a.bits, sign_hint);
				} else if (children[1]->isConst() && children[2]->isConst()) {
					newNode = new AstNode(AST_REALVALUE);
					if (children[1]->asReal(sign_hint) == children[2]->asReal(sign_hint))
						newNode->realvalue = children[1]->asReal(sign_hint);
					else
						// IEEE Std 1800-2012 Sec. 11.4.11 states that the entry in Table 7-1 for
						// the data type in question should be returned if the ?: is ambiguous. The
						// value in Table 7-1 for the 'real' type is 0.0.
						newNode->realvalue = 0.0;
				}
			}
			break;
		case AST_CAST_SIZE:
			if (children.at(0)->type == AST_CONSTANT && children.at(1)->type == AST_CONSTANT) {
				int width = children[0]->bitsAsConst().as_int();
				RTLIL::Const val;
				if (children[1]->is_unsized)
					val = children[1]->bitsAsUnsizedConst(width);
				else
					val = children[1]->bitsAsConst(width);
				newNode = mkconst_bits(val.bits, children[1]->is_signed);
			}
			break;
		case AST_CONCAT:
			string_op = !children.empty();
			for (auto it = children.begin(); it != children.end(); it++) {
				if ((*it)->type != AST_CONSTANT)
					goto not_const;
				if (!(*it)->is_string)
					string_op = false;
				tmp_bits.insert(tmp_bits.end(), (*it)->bits.begin(), (*it)->bits.end());
			}
			newNode = string_op ? mkconst_str(tmp_bits) : mkconst_bits(tmp_bits, false);
			break;
		case AST_REPLICATE:
			if (children.at(0)->type != AST_CONSTANT || children.at(1)->type != AST_CONSTANT)
				goto not_const;
			for (int i = 0; i < children[0]->bitsAsConst().as_int(); i++)
				tmp_bits.insert(tmp_bits.end(), children.at(1)->bits.begin(), children.at(1)->bits.end());
			newNode = children.at(1)->is_string ? mkconst_str(tmp_bits) : mkconst_bits(tmp_bits, false);
			break;
		default:
		not_const:
			break;
		}
	}

	// if any of the above set 'newNode' -> use 'newNode' as template to update 'this'
	if (newNode) {
apply_newNode:
		// fprintf(stderr, "----\n");
		// dumpAst(stderr, "- ");
		// newNode->dumpAst(stderr, "+ ");
		log_assert(newNode != NULL);
		newNode->filename = filename;
		newNode->location = location;
		newNode->cloneInto(this);
		fixup_hierarchy_flags();
		delete newNode;
		did_something = true;
	}

	if (!did_something)
		basic_prep = true;

	recursion_counter--;
	return did_something;
}

void AstNode::replace_result_wire_name_in_function(const std::string &from, const std::string &to)
{
	for (AstNode *child : children)
		child->replace_result_wire_name_in_function(from, to);
	if (str == from && type != AST_FCALL && type != AST_TCALL)
		str = to;
}

// replace a readmem[bh] TCALL ast node with a block of memory assignments
AstNode *AstNode::readmem(bool is_readmemh, std::string mem_filename, AstNode *memory, int start_addr, int finish_addr, bool unconditional_init)
{
	int mem_width, mem_size, addr_bits;
	memory->meminfo(mem_width, mem_size, addr_bits);

	AstNode *block = new AstNode(AST_BLOCK);

	AstNode *meminit = nullptr;
	int next_meminit_cursor=0;
	vector<State> meminit_bits;
	vector<State> en_bits;
	int meminit_size=0;

	for (int i = 0; i < mem_width; i++)
		en_bits.push_back(State::S1);

	std::ifstream f;
	f.open(mem_filename.c_str());
	if (f.fail()) {
#ifdef _WIN32
		char slash = '\\';
#else
		char slash = '/';
#endif
		std::string path = filename.substr(0, filename.find_last_of(slash)+1);
		f.open(path + mem_filename.c_str());
		yosys_input_files.insert(path + mem_filename);
	} else {
		yosys_input_files.insert(mem_filename);
	}
	if (f.fail() || GetSize(mem_filename) == 0)
		input_error("Can not open file `%s` for %s.\n", mem_filename.c_str(), str.c_str());

	log_assert(GetSize(memory->children) == 2 && memory->children[1]->type == AST_RANGE && memory->children[1]->range_valid);
	int range_left =  memory->children[1]->range_left, range_right =  memory->children[1]->range_right;
	int range_min = min(range_left, range_right), range_max = max(range_left, range_right);

	if (start_addr < 0)
		start_addr = range_min;

	if (finish_addr < 0)
		finish_addr = range_max + 1;

	bool in_comment = false;
	int increment = start_addr <= finish_addr ? +1 : -1;
	int cursor = start_addr;

	while (!f.eof())
	{
		std::string line, token;
		std::getline(f, line);

		for (int i = 0; i < GetSize(line); i++) {
			if (in_comment && line.compare(i, 2, "*/") == 0) {
				line[i] = ' ';
				line[i+1] = ' ';
				in_comment = false;
				continue;
			}
			if (!in_comment && line.compare(i, 2, "/*") == 0)
				in_comment = true;
			if (in_comment)
				line[i] = ' ';
		}

		while (1)
		{
			token = next_token(line, " \t\r\n");
			if (token.empty() || token.compare(0, 2, "//") == 0)
				break;

			if (token[0] == '@') {
				token = token.substr(1);
				const char *nptr = token.c_str();
				char *endptr;
				cursor = strtol(nptr, &endptr, 16);
				if (!*nptr || *endptr)
					input_error("Can not parse address `%s` for %s.\n", nptr, str.c_str());
				continue;
			}

			AstNode *value = VERILOG_FRONTEND::const2ast(stringf("%d'%c", mem_width, is_readmemh ? 'h' : 'b') + token);

			if (unconditional_init)
			{
				if (meminit == nullptr || cursor != next_meminit_cursor)
				{
					if (meminit != nullptr) {
						meminit->children[1] = AstNode::mkconst_bits(meminit_bits, false);
						meminit->children[3] = AstNode::mkconst_int(meminit_size, false);
					}

					meminit = new AstNode(AST_MEMINIT);
					meminit->children.push_back(AstNode::mkconst_int(cursor, false));
					meminit->children.push_back(nullptr);
					meminit->children.push_back(AstNode::mkconst_bits(en_bits, false));
					meminit->children.push_back(nullptr);
					meminit->str = memory->str;
					meminit->id2ast = memory;
					meminit_bits.clear();
					meminit_size = 0;

					current_ast_mod->children.push_back(meminit);
					next_meminit_cursor = cursor;
				}

				meminit_size++;
				next_meminit_cursor++;
				meminit_bits.insert(meminit_bits.end(), value->bits.begin(), value->bits.end());
				delete value;
			}
			else
			{
				block->children.push_back(new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER, new AstNode(AST_RANGE, AstNode::mkconst_int(cursor, false))), value));
				block->children.back()->children[0]->str = memory->str;
				block->children.back()->children[0]->id2ast = memory;
				block->children.back()->children[0]->was_checked = true;
			}

			cursor += increment;
			if ((cursor == finish_addr+increment) || (increment > 0 && cursor > range_max) || (increment < 0 && cursor < range_min))
				break;
		}

		if ((cursor == finish_addr+increment) || (increment > 0 && cursor > range_max) || (increment < 0 && cursor < range_min))
			break;
	}

	if (meminit != nullptr) {
		meminit->children[1] = AstNode::mkconst_bits(meminit_bits, false);
		meminit->children[3] = AstNode::mkconst_int(meminit_size, false);
	}

	return block;
}

// annotate the names of all wires and other named objects in a named generate
// or procedural block; nested blocks are themselves annotated such that the
// prefix is carried forward, but resolution of their children is deferred
void AstNode::expand_genblock(const std::string &prefix)
{
	if (type == AST_IDENTIFIER || type == AST_FCALL || type == AST_TCALL || type == AST_WIRETYPE || type == AST_PREFIX) {
		log_assert(!str.empty());

		// search starting in the innermost scope and then stepping outward
		for (size_t ppos = prefix.size() - 1; ppos; --ppos) {
			if (prefix.at(ppos) != '.') continue;

			std::string new_prefix = prefix.substr(0, ppos + 1);
			auto attempt_resolve = [&new_prefix](const std::string &ident) -> std::string {
				std::string new_name = prefix_id(new_prefix, ident);
				if (current_scope.count(new_name))
					return new_name;
				return {};
			};

			// attempt to resolve the full identifier
			std::string resolved = attempt_resolve(str);
			if (!resolved.empty()) {
				str = resolved;
				break;
			}

			// attempt to resolve hierarchical prefixes within the identifier,
			// as the prefix could refer to a local scope which exists but
			// hasn't yet been elaborated
			for (size_t spos = str.size() - 1; spos; --spos) {
				if (str.at(spos) != '.') continue;
				resolved = attempt_resolve(str.substr(0, spos));
				if (!resolved.empty()) {
					str = resolved + str.substr(spos);
					ppos = 1; // break outer loop
					break;
				}
			}

		}
	}

	auto prefix_node = [&prefix](AstNode* child) {
		if (child->str.empty()) return;
		std::string new_name = prefix_id(prefix, child->str);
		if (child->type == AST_FUNCTION)
			child->replace_result_wire_name_in_function(child->str, new_name);
		else
			child->str = new_name;
		current_scope[new_name] = child;
	};

	for (size_t i = 0; i < children.size(); i++) {
		AstNode *child = children[i];

		switch (child->type) {
		case AST_WIRE:
		case AST_MEMORY:
		case AST_STRUCT:
		case AST_UNION:
		case AST_PARAMETER:
		case AST_LOCALPARAM:
		case AST_FUNCTION:
		case AST_TASK:
		case AST_CELL:
		case AST_TYPEDEF:
		case AST_ENUM_ITEM:
		case AST_GENVAR:
			prefix_node(child);
			break;

		case AST_BLOCK:
		case AST_GENBLOCK:
			if (!child->str.empty())
				prefix_node(child);
			break;

		case AST_ENUM:
			current_scope[child->str] = child;
			for (auto enode : child->children){
				log_assert(enode->type == AST_ENUM_ITEM);
				prefix_node(enode);
			}
			break;

		default:
			break;
		}
	}

	for (size_t i = 0; i < children.size(); i++) {
		AstNode *child = children[i];
		// AST_PREFIX member names should not be prefixed; we recurse into them
		// as normal to ensure indices and ranges are properly resolved, and
		// then restore the previous string
		if (type == AST_PREFIX && i == 1) {
			std::string backup_scope_name = child->str;
			child->expand_genblock(prefix);
			child->str = backup_scope_name;
			continue;
		}
		// functions/tasks may reference wires, constants, etc. in this scope
		if (child->type == AST_FUNCTION || child->type == AST_TASK)
			continue;
		// named blocks pick up the current prefix and will expanded later
		if ((child->type == AST_GENBLOCK || child->type == AST_BLOCK) && !child->str.empty())
			continue;

		child->expand_genblock(prefix);
	}
}

// add implicit AST_GENBLOCK names according to IEEE 1364-2005 Section 12.4.3 or
// IEEE 1800-2017 Section 27.6
void AstNode::label_genblks(std::set<std::string>& existing, int &counter)
{
	switch (type) {
	case AST_GENIF:
	case AST_GENFOR:
	case AST_GENCASE:
		// seeing a proper generate control flow construct increments the
		// counter once
		++counter;
		for (AstNode *child : children)
			child->label_genblks(existing, counter);
		break;

	case AST_GENBLOCK: {
		// if this block is unlabeled, generate its corresponding unique name
		for (int padding = 0; str.empty(); ++padding) {
			std::string candidate = "\\genblk";
			for (int i = 0; i < padding; ++i)
				candidate += '0';
			candidate += std::to_string(counter);
			if (!existing.count(candidate))
				str = candidate;
		}
		// within a genblk, the counter starts fresh
		std::set<std::string> existing_local = existing;
		int counter_local = 0;
		for (AstNode *child : children)
			child->label_genblks(existing_local, counter_local);
		break;
	}

	default:
		// track names which could conflict with implicit genblk names
		if (str.rfind("\\genblk", 0) == 0)
			existing.insert(str);
		for (AstNode *child : children)
			child->label_genblks(existing, counter);
		break;
	}
}

// helper function for mem2reg_as_needed_pass1
static void mark_memories_assign_lhs_complex(dict<AstNode*, pool<std::string>> &mem2reg_places,
		dict<AstNode*, uint32_t> &mem2reg_candidates, AstNode *that)
{
	for (auto &child : that->children)
		mark_memories_assign_lhs_complex(mem2reg_places, mem2reg_candidates, child);

	if (that->type == AST_IDENTIFIER && that->id2ast && that->id2ast->type == AST_MEMORY) {
		AstNode *mem = that->id2ast;
		if (!(mem2reg_candidates[mem] & AstNode::MEM2REG_FL_CMPLX_LHS))
			mem2reg_places[mem].insert(stringf("%s:%d", RTLIL::encode_filename(that->filename).c_str(), that->location.first_line));
		mem2reg_candidates[mem] |= AstNode::MEM2REG_FL_CMPLX_LHS;
	}
}

// find memories that should be replaced by registers
void AstNode::mem2reg_as_needed_pass1(dict<AstNode*, pool<std::string>> &mem2reg_places,
		dict<AstNode*, uint32_t> &mem2reg_candidates, dict<AstNode*, uint32_t> &proc_flags, uint32_t &flags)
{
	uint32_t children_flags = 0;
	int lhs_children_counter = 0;

	if (type == AST_TYPEDEF)
		return; // don't touch content of typedefs

	if (type == AST_ASSIGN || type == AST_ASSIGN_LE || type == AST_ASSIGN_EQ)
	{
		// mark all memories that are used in a complex expression on the left side of an assignment
		for (auto &lhs_child : children[0]->children)
			mark_memories_assign_lhs_complex(mem2reg_places, mem2reg_candidates, lhs_child);

		if (children[0]->type == AST_IDENTIFIER && children[0]->id2ast && children[0]->id2ast->type == AST_MEMORY)
		{
			AstNode *mem = children[0]->id2ast;

			// activate mem2reg if this is assigned in an async proc
			if (flags & AstNode::MEM2REG_FL_ASYNC) {
				if (!(mem2reg_candidates[mem] & AstNode::MEM2REG_FL_SET_ASYNC))
					mem2reg_places[mem].insert(stringf("%s:%d", RTLIL::encode_filename(filename).c_str(), location.first_line));
				mem2reg_candidates[mem] |= AstNode::MEM2REG_FL_SET_ASYNC;
			}

			// remember if this is assigned blocking (=)
			if (type == AST_ASSIGN_EQ) {
				if (!(proc_flags[mem] & AstNode::MEM2REG_FL_EQ1))
					mem2reg_places[mem].insert(stringf("%s:%d", RTLIL::encode_filename(filename).c_str(), location.first_line));
				proc_flags[mem] |= AstNode::MEM2REG_FL_EQ1;
			}

			// for proper (non-init) writes: remember if this is a constant index or not
			if ((flags & MEM2REG_FL_INIT) == 0) {
				if (children[0]->children.size() && children[0]->children[0]->type == AST_RANGE && children[0]->children[0]->children.size()) {
					if (children[0]->children[0]->children[0]->type == AST_CONSTANT)
						mem2reg_candidates[mem] |= AstNode::MEM2REG_FL_CONST_LHS;
					else
						mem2reg_candidates[mem] |= AstNode::MEM2REG_FL_VAR_LHS;
				}
			}

			// remember where this is
			if (flags & MEM2REG_FL_INIT) {
				if (!(mem2reg_candidates[mem] & AstNode::MEM2REG_FL_SET_INIT))
					mem2reg_places[mem].insert(stringf("%s:%d", RTLIL::encode_filename(filename).c_str(), location.first_line));
				mem2reg_candidates[mem] |= AstNode::MEM2REG_FL_SET_INIT;
			} else {
				if (!(mem2reg_candidates[mem] & AstNode::MEM2REG_FL_SET_ELSE))
					mem2reg_places[mem].insert(stringf("%s:%d", RTLIL::encode_filename(filename).c_str(), location.first_line));
				mem2reg_candidates[mem] |= AstNode::MEM2REG_FL_SET_ELSE;
			}
		}

		lhs_children_counter = 1;
	}

	if (type == AST_IDENTIFIER && id2ast && id2ast->type == AST_MEMORY)
	{
		AstNode *mem = id2ast;

		// flag if used after blocking assignment (in same proc)
		if ((proc_flags[mem] & AstNode::MEM2REG_FL_EQ1) && !(mem2reg_candidates[mem] & AstNode::MEM2REG_FL_EQ2)) {
			mem2reg_places[mem].insert(stringf("%s:%d", RTLIL::encode_filename(filename).c_str(), location.first_line));
			mem2reg_candidates[mem] |= AstNode::MEM2REG_FL_EQ2;
		}
	}

	// also activate if requested, either by using mem2reg attribute or by declaring array as 'wire' instead of 'reg' or 'logic'
	if (type == AST_MEMORY && (get_bool_attribute(ID::mem2reg) || (flags & AstNode::MEM2REG_FL_ALL) || !(is_reg || is_logic)))
		mem2reg_candidates[this] |= AstNode::MEM2REG_FL_FORCED;

	if ((type == AST_MODULE || type == AST_INTERFACE) && get_bool_attribute(ID::mem2reg))
		children_flags |= AstNode::MEM2REG_FL_ALL;

	dict<AstNode*, uint32_t> *proc_flags_p = NULL;

	if (type == AST_ALWAYS) {
		int count_edge_events = 0;
		for (auto child : children)
			if (child->type == AST_POSEDGE || child->type == AST_NEGEDGE)
				count_edge_events++;
		if (count_edge_events != 1)
			children_flags |= AstNode::MEM2REG_FL_ASYNC;
		proc_flags_p = new dict<AstNode*, uint32_t>;
	}
	else if (type == AST_INITIAL) {
		children_flags |= AstNode::MEM2REG_FL_INIT;
		proc_flags_p = new dict<AstNode*, uint32_t>;
	}

	uint32_t backup_flags = flags;
	flags |= children_flags;
	log_assert((flags & ~0x000000ff) == 0);

	for (auto child : children)
	{
		if (lhs_children_counter > 0) {
			lhs_children_counter--;
			if (child->children.size() && child->children[0]->type == AST_RANGE && child->children[0]->children.size()) {
				for (auto c : child->children[0]->children) {
					if (proc_flags_p)
						c->mem2reg_as_needed_pass1(mem2reg_places, mem2reg_candidates, *proc_flags_p, flags);
					else
						c->mem2reg_as_needed_pass1(mem2reg_places, mem2reg_candidates, proc_flags, flags);
				}
			}
		} else
		if (proc_flags_p)
			child->mem2reg_as_needed_pass1(mem2reg_places, mem2reg_candidates, *proc_flags_p, flags);
		else
			child->mem2reg_as_needed_pass1(mem2reg_places, mem2reg_candidates, proc_flags, flags);
	}

	flags &= ~children_flags | backup_flags;

	if (proc_flags_p) {
#ifndef NDEBUG
		for (auto it : *proc_flags_p)
			log_assert((it.second & ~0xff000000) == 0);
#endif
		delete proc_flags_p;
	}
}

bool AstNode::mem2reg_check(pool<AstNode*> &mem2reg_set)
{
	if (type != AST_IDENTIFIER || !id2ast || !mem2reg_set.count(id2ast))
		return false;

	if (children.empty() || children[0]->type != AST_RANGE || GetSize(children[0]->children) != 1)
		input_error("Invalid array access.\n");

	return true;
}

void AstNode::mem2reg_remove(pool<AstNode*> &mem2reg_set, vector<AstNode*> &delnodes)
{
	log_assert(mem2reg_set.count(this) == 0);

	if (mem2reg_set.count(id2ast))
		id2ast = nullptr;

	for (size_t i = 0; i < children.size(); i++) {
		if (mem2reg_set.count(children[i]) > 0) {
			delnodes.push_back(children[i]);
			children.erase(children.begin() + (i--));
		} else {
			children[i]->mem2reg_remove(mem2reg_set, delnodes);
		}
	}
}

// actually replace memories with registers
bool AstNode::mem2reg_as_needed_pass2(pool<AstNode*> &mem2reg_set, AstNode *mod, AstNode *block, AstNode *&async_block)
{
	bool did_something = false;

	if (type == AST_BLOCK)
		block = this;

	if (type == AST_FUNCTION || type == AST_TASK)
		return false;

	if (type == AST_TYPEDEF)
		return false;

	if (type == AST_MEMINIT && id2ast && mem2reg_set.count(id2ast))
	{
		log_assert(children[0]->type == AST_CONSTANT);
		log_assert(children[1]->type == AST_CONSTANT);
		log_assert(children[2]->type == AST_CONSTANT);
		log_assert(children[3]->type == AST_CONSTANT);

		int cursor = children[0]->asInt(false);
		Const data = children[1]->bitsAsConst();
		Const en = children[2]->bitsAsConst();
		int length = children[3]->asInt(false);

		if (length != 0)
		{
			AstNode *block = new AstNode(AST_INITIAL, new AstNode(AST_BLOCK));
			mod->children.push_back(block);
			block = block->children[0];

			int wordsz = GetSize(data) / length;

			for (int i = 0; i < length; i++) {
				int pos = 0;
				while (pos < wordsz) {
					if (en[pos] != State::S1) {
						pos++;
					} else {
						int epos = pos + 1;
						while (epos < wordsz && en[epos] == State::S1)
							epos++;
						int clen = epos - pos;
						AstNode *range = new AstNode(AST_RANGE, AstNode::mkconst_int(cursor+i, false));
						if (pos != 0 || epos != wordsz) {
							int left;
							int right;
							AstNode *mrange = id2ast->children[0];
							if (mrange->range_left < mrange->range_right) {
								right = mrange->range_right - pos;
								left = mrange->range_right - epos + 1;
							} else {
								right = mrange->range_right + pos;
								left = mrange->range_right + epos - 1;
							}
							range = new AstNode(AST_MULTIRANGE, range, new AstNode(AST_RANGE, AstNode::mkconst_int(left, true), AstNode::mkconst_int(right, true)));
						}
						AstNode *target = new AstNode(AST_IDENTIFIER, range);
						target->str = str;
						target->id2ast = id2ast;
						target->was_checked = true;
						block->children.push_back(new AstNode(AST_ASSIGN_EQ, target, mkconst_bits(data.extract(i*wordsz + pos, clen).bits, false)));
						pos = epos;
					}
				}
			}
		}

		AstNode *newNode = new AstNode(AST_NONE);
		newNode->cloneInto(this);
		delete newNode;

		did_something = true;
	}

	if (type == AST_ASSIGN && block == NULL && children[0]->mem2reg_check(mem2reg_set))
	{
		if (async_block == NULL) {
			async_block = new AstNode(AST_ALWAYS, new AstNode(AST_BLOCK));
			mod->children.push_back(async_block);
		}

		AstNode *newNode = clone();
		newNode->type = AST_ASSIGN_EQ;
		newNode->children[0]->was_checked = true;
		async_block->children[0]->children.push_back(newNode);

		newNode = new AstNode(AST_NONE);
		newNode->cloneInto(this);
		delete newNode;

		did_something = true;
	}

	if ((type == AST_ASSIGN_LE || type == AST_ASSIGN_EQ) && children[0]->mem2reg_check(mem2reg_set) &&
			children[0]->children[0]->children[0]->type != AST_CONSTANT)
	{
		std::stringstream sstr;
		sstr << "$mem2reg_wr$" << children[0]->str << "$" << RTLIL::encode_filename(filename) << ":" << location.first_line << "$" << (autoidx++);
		std::string id_addr = sstr.str() + "_ADDR", id_data = sstr.str() + "_DATA";

		int mem_width, mem_size, addr_bits;
		bool mem_signed = children[0]->id2ast->is_signed;
		children[0]->id2ast->meminfo(mem_width, mem_size, addr_bits);

		AstNode *wire_addr = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(addr_bits-1, true), mkconst_int(0, true)));
		wire_addr->str = id_addr;
		wire_addr->is_reg = true;
		wire_addr->was_checked = true;
		wire_addr->set_attribute(ID::nosync, AstNode::mkconst_int(1, false));
		mod->children.push_back(wire_addr);
		while (wire_addr->simplify(true, 1, -1, false)) { }

		AstNode *wire_data = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(mem_width-1, true), mkconst_int(0, true)));
		wire_data->str = id_data;
		wire_data->is_reg = true;
		wire_data->was_checked = true;
		wire_data->is_signed = mem_signed;
		wire_data->set_attribute(ID::nosync, AstNode::mkconst_int(1, false));
		mod->children.push_back(wire_data);
		while (wire_data->simplify(true, 1, -1, false)) { }

		log_assert(block != NULL);
		size_t assign_idx = 0;
		while (assign_idx < block->children.size() && block->children[assign_idx] != this)
			assign_idx++;
		log_assert(assign_idx < block->children.size());

		AstNode *assign_addr = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), children[0]->children[0]->children[0]->clone());
		assign_addr->children[0]->str = id_addr;
		assign_addr->children[0]->was_checked = true;
		block->children.insert(block->children.begin()+assign_idx+1, assign_addr);

		AstNode *case_node = new AstNode(AST_CASE, new AstNode(AST_IDENTIFIER));
		case_node->children[0]->str = id_addr;
		for (int i = 0; i < mem_size; i++) {
			if (children[0]->children[0]->children[0]->type == AST_CONSTANT && int(children[0]->children[0]->children[0]->integer) != i)
				continue;
			AstNode *cond_node = new AstNode(AST_COND, AstNode::mkconst_int(i, false, addr_bits), new AstNode(AST_BLOCK));
			AstNode *assign_reg = new AstNode(type, new AstNode(AST_IDENTIFIER), new AstNode(AST_IDENTIFIER));
			if (children[0]->children.size() == 2)
				assign_reg->children[0]->children.push_back(children[0]->children[1]->clone());
			assign_reg->children[0]->str = stringf("%s[%d]", children[0]->str.c_str(), i);
			assign_reg->children[1]->str = id_data;
			cond_node->children[1]->children.push_back(assign_reg);
			case_node->children.push_back(cond_node);
		}

		// fixup on the full hierarchy below case_node
		case_node->fixup_hierarchy_flags(true);

		block->children.insert(block->children.begin()+assign_idx+2, case_node);

		children[0]->delete_children();
		children[0]->range_valid = false;
		children[0]->id2ast = NULL;
		children[0]->str = id_data;
		type = AST_ASSIGN_EQ;
		children[0]->was_checked = true;

		fixup_hierarchy_flags();
		did_something = true;
	}

	if (mem2reg_check(mem2reg_set))
	{
		AstNode *bit_part_sel = NULL;
		if (children.size() == 2)
			bit_part_sel = children[1]->clone();

		if (children[0]->children[0]->type == AST_CONSTANT)
		{
			int id = children[0]->children[0]->integer;
			int left = id2ast->children[1]->children[0]->integer;
			int right = id2ast->children[1]->children[1]->integer;
			bool valid_const_access =
				(left <= id && id <= right) ||
				(right <= id && id <= left);
			if (valid_const_access)
			{
				str = stringf("%s[%d]", str.c_str(), id);
				delete_children();
				range_valid = false;
				id2ast = NULL;
			}
			else
			{
				int width;
				if (bit_part_sel)
				{
					bit_part_sel->dumpAst(nullptr, "? ");
					if (bit_part_sel->children.size() == 1)
						width = 0;
					else
						width = bit_part_sel->children[0]->integer -
							bit_part_sel->children[1]->integer;
					delete bit_part_sel;
					bit_part_sel = nullptr;
				}
				else
				{
					width = id2ast->children[0]->children[0]->integer -
						id2ast->children[0]->children[1]->integer;
				}
				width = abs(width) + 1;

				delete_children();

				std::vector<RTLIL::State> x_bits;
				for (int i = 0; i < width; i++)
					x_bits.push_back(RTLIL::State::Sx);
				AstNode *constant = AstNode::mkconst_bits(x_bits, false);
				constant->cloneInto(this);
				delete constant;
			}
		}
		else
		{
			std::stringstream sstr;
			sstr << "$mem2reg_rd$" << str << "$" << RTLIL::encode_filename(filename) << ":" << location.first_line << "$" << (autoidx++);
			std::string id_addr = sstr.str() + "_ADDR", id_data = sstr.str() + "_DATA";

			int mem_width, mem_size, addr_bits;
			bool mem_signed = id2ast->is_signed;
			id2ast->meminfo(mem_width, mem_size, addr_bits);

			AstNode *wire_addr = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(addr_bits-1, true), mkconst_int(0, true)));
			wire_addr->str = id_addr;
			wire_addr->is_reg = true;
			wire_addr->was_checked = true;
			if (block)
				wire_addr->set_attribute(ID::nosync, AstNode::mkconst_int(1, false));
			mod->children.push_back(wire_addr);
			while (wire_addr->simplify(true, 1, -1, false)) { }

			AstNode *wire_data = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(mem_width-1, true), mkconst_int(0, true)));
			wire_data->str = id_data;
			wire_data->is_reg = true;
			wire_data->was_checked = true;
			wire_data->is_signed = mem_signed;
			if (block)
				wire_data->set_attribute(ID::nosync, AstNode::mkconst_int(1, false));
			mod->children.push_back(wire_data);
			while (wire_data->simplify(true, 1, -1, false)) { }

			AstNode *assign_addr = new AstNode(block ? AST_ASSIGN_EQ : AST_ASSIGN, new AstNode(AST_IDENTIFIER), children[0]->children[0]->clone());
			assign_addr->children[0]->str = id_addr;
			assign_addr->children[0]->was_checked = true;

			AstNode *case_node = new AstNode(AST_CASE, new AstNode(AST_IDENTIFIER));
			case_node->children[0]->str = id_addr;

			for (int i = 0; i < mem_size; i++) {
				if (children[0]->children[0]->type == AST_CONSTANT && int(children[0]->children[0]->integer) != i)
					continue;
				AstNode *cond_node = new AstNode(AST_COND, AstNode::mkconst_int(i, false, addr_bits), new AstNode(AST_BLOCK));
				AstNode *assign_reg = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), new AstNode(AST_IDENTIFIER));
				assign_reg->children[0]->str = id_data;
				assign_reg->children[0]->was_checked = true;
				assign_reg->children[1]->str = stringf("%s[%d]", str.c_str(), i);
				cond_node->children[1]->children.push_back(assign_reg);
				case_node->children.push_back(cond_node);
			}

			std::vector<RTLIL::State> x_bits;
			for (int i = 0; i < mem_width; i++)
				x_bits.push_back(RTLIL::State::Sx);

			AstNode *cond_node = new AstNode(AST_COND, new AstNode(AST_DEFAULT), new AstNode(AST_BLOCK));
			AstNode *assign_reg = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), AstNode::mkconst_bits(x_bits, false));
			assign_reg->children[0]->str = id_data;
			assign_reg->children[0]->was_checked = true;
			cond_node->children[1]->children.push_back(assign_reg);
			case_node->children.push_back(cond_node);

			// fixup on the full hierarchy below case_node
			case_node->fixup_hierarchy_flags(true);

			if (block)
			{
				size_t assign_idx = 0;
				while (assign_idx < block->children.size() && !block->children[assign_idx]->contains(this))
					assign_idx++;
				log_assert(assign_idx < block->children.size());
				block->children.insert(block->children.begin()+assign_idx, case_node);
				block->children.insert(block->children.begin()+assign_idx, assign_addr);
			}
			else
			{
				AstNode *proc = new AstNode(AST_ALWAYS, new AstNode(AST_BLOCK, case_node));
				mod->children.push_back(proc);
				mod->children.push_back(assign_addr);
				mod->fixup_hierarchy_flags();
			}

			delete_children();
			range_valid = false;
			id2ast = NULL;
			str = id_data;
		}

		if (bit_part_sel) {
			children.push_back(bit_part_sel);
			fixup_hierarchy_flags();
		}

		did_something = true;
	}

	log_assert(id2ast == NULL || mem2reg_set.count(id2ast) == 0);

	auto children_list = children;
	for (size_t i = 0; i < children_list.size(); i++)
		if (children_list[i]->mem2reg_as_needed_pass2(mem2reg_set, mod, block, async_block))
			did_something = true;

	return did_something;
}

// calculate memory dimensions
void AstNode::meminfo(int &mem_width, int &mem_size, int &addr_bits)
{
	log_assert(type == AST_MEMORY);

	mem_width = children[0]->range_left - children[0]->range_right + 1;
	mem_size = children[1]->range_left - children[1]->range_right;

	if (mem_size < 0)
		mem_size *= -1;
	mem_size += min(children[1]->range_left, children[1]->range_right) + 1;

	addr_bits = 1;
	while ((1 << addr_bits) < mem_size)
		addr_bits++;
}

bool AstNode::detect_latch(const std::string &var)
{
	switch (type)
	{
	case AST_ALWAYS:
		for (auto &c : children)
		{
			switch (c->type)
			{
			case AST_POSEDGE:
			case AST_NEGEDGE:
				return false;
			case AST_EDGE:
				break;
			case AST_BLOCK:
				if (!c->detect_latch(var))
					return false;
				break;
			default:
				log_abort();
			}
		}
		return true;
	case AST_BLOCK:
		for (auto &c : children)
			if (!c->detect_latch(var))
				return false;
		return true;
	case AST_CASE:
		{
			bool r = true;
			for (auto &c : children) {
				if (c->type == AST_COND) {
					if (c->children.at(1)->detect_latch(var))
						return true;
					r = false;
				}
				if (c->type == AST_DEFAULT) {
					if (c->children.at(0)->detect_latch(var))
						return true;
					r = false;
				}
			}
			return r;
		}
	case AST_ASSIGN_EQ:
	case AST_ASSIGN_LE:
		if (children.at(0)->type == AST_IDENTIFIER &&
				children.at(0)->children.empty() && children.at(0)->str == var)
			return false;
		return true;
	default:
		return true;
	}
}

bool AstNode::has_const_only_constructs()
{
	if (type == AST_WHILE || type == AST_REPEAT)
		return true;
	for (auto child : children)
		if (child->has_const_only_constructs())
			return true;
	return false;
}

bool AstNode::is_simple_const_expr()
{
	if (type == AST_IDENTIFIER)
		return false;
	for (auto child : children)
		if (!child->is_simple_const_expr())
			return false;
	return true;
}

// helper function for AstNode::eval_const_function()
bool AstNode::replace_variables(std::map<std::string, AstNode::varinfo_t> &variables, AstNode *fcall, bool must_succeed)
{
	if (type == AST_IDENTIFIER && variables.count(str)) {
		int offset = variables.at(str).offset, width = variables.at(str).val.bits.size();
		if (!children.empty()) {
			if (children.size() != 1 || children.at(0)->type != AST_RANGE) {
				if (!must_succeed)
					return false;
				input_error("Memory access in constant function is not supported\n%s: ...called from here.\n",
						fcall->loc_string().c_str());
			}
			if (!children.at(0)->replace_variables(variables, fcall, must_succeed))
				return false;
			while (simplify(true, 1, -1, false)) { }
			if (!children.at(0)->range_valid) {
				if (!must_succeed)
					return false;
				input_error("Non-constant range\n%s: ... called from here.\n",
						fcall->loc_string().c_str());
			}
			offset = min(children.at(0)->range_left, children.at(0)->range_right);
			width = min(std::abs(children.at(0)->range_left - children.at(0)->range_right) + 1, width);
		}
		offset -= variables.at(str).offset;
		if (variables.at(str).range_swapped)
			offset = -offset;
		std::vector<RTLIL::State> &var_bits = variables.at(str).val.bits;
		std::vector<RTLIL::State> new_bits(var_bits.begin() + offset, var_bits.begin() + offset + width);
		AstNode *newNode = mkconst_bits(new_bits, variables.at(str).is_signed);
		newNode->cloneInto(this);
		delete newNode;
		return true;
	}

	for (auto &child : children)
		if (!child->replace_variables(variables, fcall, must_succeed))
			return false;
	return true;
}

// attempt to statically evaluate a functions with all-const arguments
AstNode *AstNode::eval_const_function(AstNode *fcall, bool must_succeed)
{
	std::map<std::string, AstNode*> backup_scope = current_scope;
	std::map<std::string, AstNode::varinfo_t> variables;
	std::vector<AstNode*> to_delete;
	AstNode *block = new AstNode(AST_BLOCK);
	AstNode *result = nullptr;

	size_t argidx = 0;
	for (auto child : children)
	{
		block->children.push_back(child->clone());
	}
	block->set_in_param_flag(true);

	while (!block->children.empty())
	{
		AstNode *stmt = block->children.front();

#if 0
		log("-----------------------------------\n");
		for (auto &it : variables)
			log("%20s %40s\n", it.first.c_str(), log_signal(it.second.val));
		stmt->dumpAst(NULL, "stmt> ");
#endif

		if (stmt->type == AST_WIRE)
		{
			while (stmt->simplify(true, 1, -1, false)) { }
			if (!stmt->range_valid) {
				if (!must_succeed)
					goto finished;
				stmt->input_error("Can't determine size of variable %s\n%s: ... called from here.\n",
						stmt->str.c_str(), fcall->loc_string().c_str());
			}
			AstNode::varinfo_t &variable = variables[stmt->str];
			int width = abs(stmt->range_left - stmt->range_right) + 1;
			// if this variable has already been declared as an input, check the
			// sizes match if it already had an explicit size
			if (variable.arg && variable.explicitly_sized && variable.val.size() != width) {
				input_error("Incompatible re-declaration of constant function wire %s.\n", stmt->str.c_str());
			}
			variable.val = RTLIL::Const(RTLIL::State::Sx, width);
			variable.offset = stmt->range_swapped ? stmt->range_left : stmt->range_right;
			variable.range_swapped = stmt->range_swapped;
			variable.is_signed = stmt->is_signed;
			variable.explicitly_sized = stmt->children.size() &&
				stmt->children.back()->type == AST_RANGE;
			// identify the argument corresponding to this wire, if applicable
			if (stmt->is_input && argidx < fcall->children.size()) {
				variable.arg = fcall->children.at(argidx++);
			}
			// load the constant arg's value into this variable
			if (variable.arg) {
				if (variable.arg->type == AST_CONSTANT) {
					variable.val = variable.arg->bitsAsConst(width);
				} else {
					log_assert(variable.arg->type == AST_REALVALUE);
					variable.val = variable.arg->realAsConst(width);
				}
			}
			current_scope[stmt->str] = stmt;

			block->children.erase(block->children.begin());
			to_delete.push_back(stmt);
			continue;
		}

		log_assert(variables.count(str) != 0);

		if (stmt->type == AST_LOCALPARAM)
		{
			while (stmt->simplify(true, 1, -1, false)) { }

			current_scope[stmt->str] = stmt;

			block->children.erase(block->children.begin());
			to_delete.push_back(stmt);
			continue;
		}

		if (stmt->type == AST_ASSIGN_EQ)
		{
			if (stmt->children.at(0)->type == AST_IDENTIFIER && stmt->children.at(0)->children.size() != 0 &&
					stmt->children.at(0)->children.at(0)->type == AST_RANGE)
				if (!stmt->children.at(0)->children.at(0)->replace_variables(variables, fcall, must_succeed))
					goto finished;
			if (!stmt->children.at(1)->replace_variables(variables, fcall, must_succeed))
				goto finished;
			while (stmt->simplify(true, 1, -1, false)) { }

			if (stmt->type != AST_ASSIGN_EQ)
				continue;

			if (stmt->children.at(1)->type != AST_CONSTANT) {
				if (!must_succeed)
					goto finished;
				stmt->input_error("Non-constant expression in constant function\n%s: ... called from here. X\n",
						fcall->loc_string().c_str());
			}

			if (stmt->children.at(0)->type != AST_IDENTIFIER) {
				if (!must_succeed)
					goto finished;
				stmt->input_error("Unsupported composite left hand side in constant function\n%s: ... called from here.\n",
						fcall->loc_string().c_str());
			}

			if (!variables.count(stmt->children.at(0)->str)) {
				if (!must_succeed)
					goto finished;
				stmt->input_error("Assignment to non-local variable in constant function\n%s: ... called from here.\n",
						fcall->loc_string().c_str());
			}

			if (stmt->children.at(0)->children.empty()) {
				variables[stmt->children.at(0)->str].val = stmt->children.at(1)->bitsAsConst(variables[stmt->children.at(0)->str].val.bits.size());
			} else {
				AstNode *range = stmt->children.at(0)->children.at(0);
				if (!range->range_valid) {
					if (!must_succeed)
						goto finished;
					range->input_error("Non-constant range\n%s: ... called from here.\n", fcall->loc_string().c_str());
				}
				int offset = min(range->range_left, range->range_right);
				int width = std::abs(range->range_left - range->range_right) + 1;
				varinfo_t &v = variables[stmt->children.at(0)->str];
				RTLIL::Const r = stmt->children.at(1)->bitsAsConst(v.val.bits.size());
				for (int i = 0; i < width; i++) {
					int index = i + offset - v.offset;
					if (v.range_swapped)
						index = -index;
					v.val.bits.at(index) = r.bits.at(i);
				}
			}

			delete block->children.front();
			block->children.erase(block->children.begin());
			continue;
		}

		if (stmt->type == AST_FOR)
		{
			block->children.insert(block->children.begin(), stmt->children.at(0));
			stmt->children.at(3)->children.push_back(stmt->children.at(2));
			stmt->children.erase(stmt->children.begin() + 2);
			stmt->children.erase(stmt->children.begin());
			stmt->type = AST_WHILE;
			continue;
		}

		if (stmt->type == AST_WHILE)
		{
			AstNode *cond = stmt->children.at(0)->clone();
			if (!cond->replace_variables(variables, fcall, must_succeed))
				goto finished;
			cond->set_in_param_flag(true);
			while (cond->simplify(true, 1, -1, false)) { }

			if (cond->type != AST_CONSTANT) {
				if (!must_succeed)
					goto finished;
				stmt->input_error("Non-constant expression in constant function\n%s: ... called from here.\n",
						fcall->loc_string().c_str());
			}

			if (cond->asBool()) {
				block->children.insert(block->children.begin(), stmt->children.at(1)->clone());
			} else {
				delete block->children.front();
				block->children.erase(block->children.begin());
			}

			delete cond;
			continue;
		}

		if (stmt->type == AST_REPEAT)
		{
			AstNode *num = stmt->children.at(0)->clone();
			if (!num->replace_variables(variables, fcall, must_succeed))
				goto finished;
			num->set_in_param_flag(true);
			while (num->simplify(true, 1, -1, false)) { }

			if (num->type != AST_CONSTANT) {
				if (!must_succeed)
					goto finished;
				stmt->input_error("Non-constant expression in constant function\n%s: ... called from here.\n",
						fcall->loc_string().c_str());
			}

			block->children.erase(block->children.begin());
			for (int i = 0; i < num->bitsAsConst().as_int(); i++)
				block->children.insert(block->children.begin(), stmt->children.at(1)->clone());

			delete stmt;
			delete num;
			continue;
		}

		if (stmt->type == AST_CASE)
		{
			AstNode *expr = stmt->children.at(0)->clone();
			if (!expr->replace_variables(variables, fcall, must_succeed))
				goto finished;
			expr->set_in_param_flag(true);
			while (expr->simplify(true, 1, -1, false)) { }

			AstNode *sel_case = NULL;
			for (size_t i = 1; i < stmt->children.size(); i++)
			{
				bool found_match = false;
				log_assert(stmt->children.at(i)->type == AST_COND || stmt->children.at(i)->type == AST_CONDX || stmt->children.at(i)->type == AST_CONDZ);

				if (stmt->children.at(i)->children.front()->type == AST_DEFAULT) {
					sel_case = stmt->children.at(i)->children.back();
					continue;
				}

				for (size_t j = 0; j+1 < stmt->children.at(i)->children.size() && !found_match; j++)
				{
					AstNode *cond = stmt->children.at(i)->children.at(j)->clone();
					if (!cond->replace_variables(variables, fcall, must_succeed))
						goto finished;

					cond = new AstNode(AST_EQ, expr->clone(), cond);
					cond->set_in_param_flag(true);
					while (cond->simplify(true, 1, -1, false)) { }

					if (cond->type != AST_CONSTANT) {
						if (!must_succeed)
							goto finished;
						stmt->input_error("Non-constant expression in constant function\n%s: ... called from here.\n",
								fcall->loc_string().c_str());
					}

					found_match = cond->asBool();
					delete cond;
				}

				if (found_match) {
					sel_case = stmt->children.at(i)->children.back();
					break;
				}
			}

			block->children.erase(block->children.begin());
			if (sel_case)
				block->children.insert(block->children.begin(), sel_case->clone());
			delete stmt;
			delete expr;
			continue;
		}

		if (stmt->type == AST_BLOCK)
		{
			if (!stmt->str.empty())
				stmt->expand_genblock(stmt->str + ".");

			block->children.erase(block->children.begin());
			block->children.insert(block->children.begin(), stmt->children.begin(), stmt->children.end());
			stmt->children.clear();
			block->fixup_hierarchy_flags();
			delete stmt;
			continue;
		}

		if (!must_succeed)
			goto finished;
		stmt->input_error("Unsupported language construct in constant function\n%s: ... called from here.\n",
				fcall->loc_string().c_str());
		log_abort();
	}

	result = AstNode::mkconst_bits(variables.at(str).val.bits, variables.at(str).is_signed);

finished:
	delete block;
	current_scope = backup_scope;

	for (auto it : to_delete) {
		delete it;
	}
	to_delete.clear();

	return result;
}

void AstNode::allocateDefaultEnumValues()
{
	log_assert(type==AST_ENUM);
	log_assert(children.size() > 0);
	if (children.front()->attributes.count(ID::enum_base_type))
		return; // already elaborated
	int last_enum_int = -1;
	for (auto node : children) {
		log_assert(node->type==AST_ENUM_ITEM);
		node->set_attribute(ID::enum_base_type, mkconst_str(str));
		for (size_t i = 0; i < node->children.size(); i++) {
			switch (node->children[i]->type) {
			case AST_NONE:
				// replace with auto-incremented constant
				delete node->children[i];
				node->children[i] = AstNode::mkconst_int(++last_enum_int, true);
				break;
			case AST_CONSTANT:
				// explicit constant (or folded expression)
				// TODO: can't extend 'x or 'z item
				last_enum_int = node->children[i]->integer;
				break;
			default:
				// ignore ranges
				break;
			}
			// TODO: range check
		}
	}
}

bool AstNode::is_recursive_function() const
{
	std::set<const AstNode *> visited;
	std::function<bool(const AstNode *node)> visit = [&](const AstNode *node) {
		if (visited.count(node))
			return node == this;
		visited.insert(node);
		if (node->type == AST_FCALL) {
			auto it = current_scope.find(node->str);
			if (it != current_scope.end() && visit(it->second))
				return true;
		}
		for (const AstNode *child : node->children) {
			if (visit(child))
				return true;
		}
		return false;
	};

	log_assert(type == AST_FUNCTION);
	return visit(this);
}

std::pair<AstNode*, AstNode*> AstNode::get_tern_choice()
{
	if (!children[0]->isConst())
		return {};

	bool found_sure_true = false;
	bool found_maybe_true = false;

	if (children[0]->type == AST_CONSTANT)
		for (auto &bit : children[0]->bits) {
			if (bit == RTLIL::State::S1)
				found_sure_true = true;
			if (bit > RTLIL::State::S1)
				found_maybe_true = true;
		}
	else
		found_sure_true = children[0]->asReal(true) != 0;

	AstNode *choice = nullptr, *not_choice = nullptr;
	if (found_sure_true)
		choice = children[1], not_choice = children[2];
	else if (!found_maybe_true)
		choice = children[2], not_choice = children[1];

	return {choice, not_choice};
}

std::string AstNode::try_pop_module_prefix() const
{
	AstNode *current_scope_ast = (current_ast_mod == nullptr) ? current_ast : current_ast_mod;
	size_t pos = str.find('.', 1);
	if (str[0] == '\\' && pos != std::string::npos) {
		std::string new_str = "\\" + str.substr(pos + 1);
		if (current_scope.count(new_str)) {
			std::string prefix = str.substr(0, pos);
			auto it = current_scope_ast->attributes.find(ID::hdlname);
			if ((it != current_scope_ast->attributes.end() && it->second->str == prefix)
					|| prefix == current_scope_ast->str)
				return new_str;
		}
	}
	return str;
}

YOSYS_NAMESPACE_END
