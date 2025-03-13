/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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

#ifndef SCOPEINFO_H
#define SCOPEINFO_H

#include <vector>
#include <algorithm>

#include "kernel/yosys.h"
#include "kernel/celltypes.h"

YOSYS_NAMESPACE_BEGIN

template<typename T>
class IdTree
{
public:
	struct Cursor;

protected:
	IdTree *parent = nullptr;
	IdString scope_name;
	int depth = 0;

	pool<IdString> names;
	dict<IdString, T> entries;
public: // XXX
	dict<IdString, std::unique_ptr<IdTree>> subtrees;

	template<typename P, typename T_ref>
	static Cursor do_insert(IdTree *tree, P begin, P end, T_ref &&value)
	{
		log_assert(begin != end && "path must be non-empty");
		while (true) {
			IdString name = *begin;
			++begin;
			log_assert(!name.empty());
			tree->names.insert(name);
			if (begin == end) {
				tree->entries.emplace(name, std::forward<T_ref>(value));
				return Cursor(tree, name);
			}
			auto &unique = tree->subtrees[name];
			if (!unique) {
				unique.reset(new IdTree);
				unique->scope_name = name;
				unique->parent = tree;
				unique->depth = tree->depth + 1;
			}
			tree = unique.get();
		}
	}

public:
	IdTree() = default;
	IdTree(const IdTree &) = delete;
	IdTree(IdTree &&) = delete;

	// A cursor remains valid as long as the (sub-)IdTree it points at is alive
	struct Cursor
	{
		friend class IdTree;
	protected:
	public:
		IdTree *target;
		IdString scope_name;

		Cursor() : target(nullptr) {}
		Cursor(IdTree *target, IdString scope_name) : target(target), scope_name(scope_name) {
			if (scope_name.empty())
				log_assert(target->parent == nullptr);
		}

		Cursor do_first_child() {
			IdTree *tree = nullptr;
			if (scope_name.empty()) {
				tree = target;
			} else {
				auto found = target->subtrees.find(scope_name);
				if (found != target->subtrees.end()) {
					tree = found->second.get();
				} else {
					return Cursor();
				}
			}
			if (tree->names.empty()) {
				return Cursor();
			}
			return Cursor(tree, *tree->names.begin());
		}

		Cursor do_next_sibling() {
			if (scope_name.empty())
				return Cursor();
			auto found = target->names.find(scope_name);
			if (found == target->names.end())
				return Cursor();
			++found;
			if (found == target->names.end())
				return Cursor();
			return Cursor(target, *found);
		}

		Cursor do_parent() {
			if (scope_name.empty())
				return Cursor();
			if (target->parent != nullptr)
				return Cursor(target->parent, target->scope_name);
			return Cursor(target, IdString());
		}

		Cursor do_next_preorder() {
			Cursor current = *this;
			Cursor next = current.do_first_child();
			if (next.valid())
				return next;
			while (current.valid()) {
				if (next.valid())
					return next;
				next = current.do_next_sibling();
				if (next.valid())
					return next;
				current = current.do_parent();
			}
			return current;
		}

		Cursor do_child(IdString name) {
			IdTree *tree = nullptr;
			if (scope_name.empty()) {
				tree = target;
			} else {
				auto found = target->subtrees.find(scope_name);
				if (found != target->subtrees.end()) {
					tree = found->second.get();
				} else {
					return Cursor();
				}
			}
			auto found = tree->names.find(name);
			if (found == tree->names.end()) {
				return Cursor();
			}
			return Cursor(tree, *found);
		}

	public:
		bool operator==(const Cursor &other) const {
			return target == other.target && scope_name == other.scope_name;
		}
		bool operator!=(const Cursor &other) const {
			return !(*this == other);
		}

		[[nodiscard]] Hasher hash_into(Hasher h) const
		{
			h.eat(scope_name);
			h.eat(target);
			return h;
		}

		bool valid() const {
			return target != nullptr;
		}

		int depth() const {
			log_assert(valid());
			return target->depth + !scope_name.empty();
		}

		bool is_root() const {
			return target != nullptr && scope_name.empty();
		}

		bool has_entry() const {
			log_assert(valid());
			return !scope_name.empty() && target->entries.count(scope_name);
		}

		T &entry() {
			log_assert(!scope_name.empty());
			return target->entries.at(scope_name);
		}

		void assign_path_to(std::vector<IdString> &out_path) {
			log_assert(valid());
			out_path.clear();
			if (scope_name.empty())
				return;
			out_path.push_back(scope_name);
			IdTree *current = target;
			while (current->parent) {
				out_path.push_back(current->scope_name);
				current = current->parent;
			}
			std::reverse(out_path.begin(), out_path.end());
		}

		std::vector<IdString> path() {
			std::vector<IdString> result;
			assign_path_to(result);
			return result;
		}

		std::string path_str() {
			std::string result;
			for (const auto &item : path()) {
				if (!result.empty())
					result.push_back(' ');
				result += RTLIL::unescape_id(item);
			}
			return result;
		}

		Cursor first_child() {
			log_assert(valid());
			return do_first_child();
		}

		Cursor next_preorder() {
			log_assert(valid());
			return do_next_preorder();
		}

		Cursor parent() {
			log_assert(valid());
			return do_parent();
		}

		Cursor child(IdString name) {
			log_assert(valid());
			return do_child(name);
		}

		Cursor common_ancestor(Cursor other) {
			Cursor current = *this;

			while (current != other) {
				if (!current.valid() || !other.valid())
					return Cursor();
				int delta = current.depth() - other.depth();
				if (delta >= 0)
					current = current.do_parent();
				if (delta <= 0)
					other = other.do_parent();
			}
			return current;
		}
	};

	template<typename P>
	Cursor insert(P begin, P end, const T &value) {
		return do_insert(this, begin, end, value);
	}

	template<typename P>
	Cursor insert(P begin, P end, T &&value) {
		return do_insert(this, begin, end, std::move(value));
	}

	template<typename P>
	Cursor insert(const P &path, const T &value) {
		return do_insert(this, path.begin(), path.end(), value);
	}

	template<typename P>
	Cursor insert(const P &path, T &&value) {
		return do_insert(this, path.begin(), path.end(), std::move(value));
	}

	Cursor cursor() {
		return parent ? Cursor(this->parent, this->scope_name) : Cursor(this, IdString());
	}

	template<typename P>
	Cursor cursor(P begin, P end) {
		Cursor current = cursor();
		for (; begin != end; ++begin) {
			current = current.do_child(*begin);
			if (!current.valid())
				break;
		}
		return current;
	}

	template<typename P>
	Cursor cursor(const P &path) {
		return cursor(path.begin(), path.end());
	}
};


struct ModuleItem {
	enum class Type {
		Wire,
		Cell,
	};
	Type type;
	void *ptr;

	ModuleItem(Wire *wire) : type(Type::Wire), ptr(wire) {}
	ModuleItem(Cell *cell) : type(Type::Cell), ptr(cell) {}

	bool is_wire() const { return type == Type::Wire; }
	bool is_cell() const { return type == Type::Cell; }

	Wire *wire() const { return type == Type::Wire ? static_cast<Wire *>(ptr) : nullptr; }
	Cell *cell() const { return type == Type::Cell ? static_cast<Cell *>(ptr) : nullptr; }

	bool operator==(const ModuleItem &other) const { return ptr == other.ptr && type == other.type; }
	[[nodiscard]] Hasher hash_into(Hasher h) const { h.eat(ptr); return h; }
};

static inline void log_dump_val_worker(typename IdTree<ModuleItem>::Cursor cursor ) { log("%p %s", cursor.target, log_id(cursor.scope_name)); }

template<typename T>
static inline void log_dump_val_worker(const typename std::unique_ptr<T> &cursor ) { log("unique %p", cursor.get()); }

template<typename O>
std::vector<IdString> parse_hdlname(const O* object)
{
	std::vector<IdString> path;
	for (auto const &item : object->get_hdlname_attribute())
		path.push_back("\\" + item);
	if (path.empty() && object->name.isPublic())
		path.push_back(object->name);
	if (!path.empty() && !(object->name.isPublic() || object->name.begins_with("$paramod") || object->name.begins_with("$abstract"))) {
		path.pop_back();
		path.push_back(object->name);
	}
	return path;
}

template<typename O>
std::pair<std::vector<IdString>, IdString> parse_scopename(const O* object)
{
	std::vector<IdString> path;
	IdString trailing = object->name;
	if (object->name.isPublic() || object->name.begins_with("$paramod") || object->name.begins_with("$abstract")) {
		for (auto const &item : object->get_hdlname_attribute())
			path.push_back("\\" + item);
		if (!path.empty()) {
			trailing = path.back();
			path.pop_back();
		}
	} else if (object->has_attribute(ID::hdlname)) {
		for (auto const &item : object->get_hdlname_attribute())
			path.push_back("\\" + item);
		if (!path.empty()) {
			path.pop_back();
		}
	} else {
		for (auto const &item : split_tokens(object->get_string_attribute(ID(scopename)), " "))
			path.push_back("\\" + item);
	}
	return {path, trailing};
}

struct ModuleHdlnameIndex {
	typedef IdTree<ModuleItem>::Cursor Cursor;

	RTLIL::Module *module;
	IdTree<ModuleItem> tree;
	dict<ModuleItem, Cursor> lookup;

	ModuleHdlnameIndex(RTLIL::Module *module) : module(module) {}

private:
	template<typename I, typename Filter>
	void index_items(I begin, I end, Filter filter);

public:
	// Index all wires and cells of the module
	void index();

	// Index all wires of the module
	void index_wires();

	// Index all cells of the module
	void index_cells();

	// Index only the $scopeinfo cells of the module.
	// This is sufficient when using `containing_scope`.
	void index_scopeinfo_cells();


	// Return the cursor for the containing scope of some RTLIL object (Wire/Cell/...)
	template<typename O>
	std::pair<Cursor, IdString> containing_scope(O *object) {
		auto pair = parse_scopename(object);
		return {tree.cursor(pair.first), pair.second};
	}

	// Return a vector of source locations starting from the indexed module to
	// the scope represented by the cursor. The vector alternates module and
	// module item source locations, using empty strings for missing src
	// attributes.
	std::vector<std::string> scope_sources(Cursor cursor);

	// Return a vector of source locations starting from the indexed module to
	// the passed RTLIL object (Wire/Cell/...). The vector alternates module
	// and module item source locations, using empty strings for missing src
	// attributes.
	template<typename O>
	std::vector<std::string> sources(O *object) {
		auto pair = parse_scopename(object);
		std::vector<std::string> result = scope_sources(tree.cursor(pair.first));
		result.push_back(object->get_src_attribute());
		return result;
	}
};

enum class ScopeinfoAttrs {
	Module,
	Cell,
};

// Check whether the flattened module or flattened cell corresponding to a $scopeinfo cell had a specific attribute.
bool scopeinfo_has_attribute(const RTLIL::Cell *scopeinfo, ScopeinfoAttrs attrs, const RTLIL::IdString &id);

// Get a specific attribute from the flattened module or flattened cell corresponding to a $scopeinfo cell.
RTLIL::Const scopeinfo_get_attribute(const RTLIL::Cell *scopeinfo, ScopeinfoAttrs attrs, const RTLIL::IdString &id);

// Get all attribute from the flattened module or flattened cell corresponding to a $scopeinfo cell.
dict<RTLIL::IdString, RTLIL::Const> scopeinfo_attributes(const RTLIL::Cell *scopeinfo, ScopeinfoAttrs attrs);

YOSYS_NAMESPACE_END

#endif
