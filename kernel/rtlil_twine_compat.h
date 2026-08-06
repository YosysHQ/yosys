#ifndef RTLIL_TWINE_COMPAT_H
#define RTLIL_TWINE_COMPAT_H

namespace RTLIL {

template<typename Derived> struct NameMasqBase;
template<typename Owner> struct ObjNameMasq;
struct CellTypeMasq;
struct ModuleNameMasq;
struct PooledName;

using WireNameMasq = ObjNameMasq<Wire>;
using CellNameMasq = ObjNameMasq<Cell>;
using MemoryNameMasq = ObjNameMasq<Memory>;
using ProcessNameMasq = ObjNameMasq<Process>;

namespace masq_detail {

inline std::string render_escaped(const TwinePool *pool, IdString id) {
	if (id == IdString::Null)
		return std::string();
	return pool ? pool->str(id) : ID::str(id);
}

inline std::string render_unescaped(const TwinePool *pool, IdString id) {
	if (id == IdString::Null)
		return std::string();
	return pool ? pool->unescaped_str(id) : ID::unescaped_str(id);
}

}

template<typename Derived>
struct NameMasqBase {
	operator IdString() const { return self().ref(); }
	operator std::string() const { return self().escaped(); }
	bool isPublic() const { return self().ref().isPublic(); }
	bool empty() const { return self().ref() == IdString::Null; }
	std::string str() const { return self().escaped(); }
	bool begins_with(const char *s) const {
		const TwinePool *pool = self().pool();
		return pool ? pool->begins_with(self().ref(), s) : str().starts_with(s);
	}
	bool ends_with(const char *s) const { return str().ends_with(s); }
	template<typename... Ts> bool in(Ts &&...args) const {
		return self().ref().in(std::forward<Ts>(args)...);
	}
	std::string substr(size_t pos = 0, size_t len = std::string::npos) const {
		return self().escaped().substr(pos, len);
	}
	size_t size() const {
		const TwinePool *pool = self().pool();
		return pool ? pool->str_size(self().ref()) : self().escaped().size();
	}
	bool contains(const char *p) const { return self().escaped().find(p) != std::string::npos; }
	char operator[](int n) const { return self().escaped()[n]; }
	bool lt_by_name(const Derived &rhs) const {
		const TwinePool *pool = self().pool();
		if (pool == nullptr)
			return self().escaped() < rhs.escaped();
		return pool->compare_by_name(self().ref(), rhs.ref()) < 0;
	}
	friend bool operator==(const Derived &lhs, const Derived &rhs) { return lhs.ref() == rhs.ref(); }
	friend bool operator==(const Derived &lhs, IdString rhs) { return lhs.ref() == rhs; }
	friend bool operator==(const Derived &lhs, NullIdString) { return lhs.ref() == IdString::Null; }
	friend bool operator==(const Derived &lhs, const std::string &rhs) { return lhs.escaped() == rhs; }
	friend bool operator<(const Derived &lhs, const Derived &rhs) { return lhs.ref() < rhs.ref(); }
	[[nodiscard]] Hasher hash_into(Hasher h) const { return self().ref().hash_into(h); }
private:
	const Derived &self() const { return *static_cast<const Derived *>(this); }
};

template<typename T>
concept IsNameMasq = std::is_base_of_v<NameMasqBase<std::decay_t<T>>, std::decay_t<T>>;

// Two masq can be compared for equality by comparing .ref()
template<IsNameMasq A, IsNameMasq B>
requires (!std::is_same_v<A, B>)
inline bool operator==(const A &lhs, const B &rhs) { return lhs.ref() == rhs.ref(); }

// A pair can be created from two masqs
// otherwise, you'd try to construct masqs in the arguments of std::make_pair
// which would error out as the constructor is deleted
template<IsNameMasq A, typename B>
auto make_pair(A &&a, B &&b) { return std::make_pair(a.ref(), std::forward<B>(b)); }
template<typename A, IsNameMasq B>
auto make_pair(A &&a, B &&b) { return std::make_pair(std::forward<A>(a), b.ref()); }
template<IsNameMasq A, IsNameMasq B>
auto make_pair(A &&a, B &&b) { return std::make_pair(a.ref(), b.ref()); }

template<typename Owner>
struct ObjNameMasq : NameMasqBase<ObjNameMasq<Owner>> {
	ObjNameMasq() = default;
	ObjNameMasq(const ObjNameMasq &) = delete;
	ObjNameMasq(ObjNameMasq &&) = delete;
	IdString ref() const;
	const TwinePool *pool() const;
	std::string escaped() const;
	std::string unescape() const;
	ObjNameMasq &operator=(IdString id);
	ObjNameMasq &operator=(const ObjNameMasq &other) { return *this = other.ref(); }
	ObjNameMasq &operator=(ObjNameMasq &&other) { return *this = other.ref(); }
private:
	const Owner *owner() const;
	Owner *owner();
};

struct CellTypeMasq : NameMasqBase<CellTypeMasq> {
	CellTypeMasq() = default;
	CellTypeMasq(const CellTypeMasq &) = delete;
	CellTypeMasq(CellTypeMasq &&) = delete;
	IdString ref() const;
	const TwinePool *pool() const;
	std::string escaped() const;
	std::string unescape() const;
	CellTypeMasq &operator=(IdString id);
	CellTypeMasq &operator=(const CellTypeMasq &other) { return *this = other.ref(); }
	CellTypeMasq &operator=(CellTypeMasq &&other) { return *this = other.ref(); }
private:
	const Cell *owner() const;
	Cell *owner();
};

struct ModuleNameMasq : NameMasqBase<ModuleNameMasq> {
	ModuleNameMasq() = default;
	ModuleNameMasq(const ModuleNameMasq &) = delete;
	ModuleNameMasq(ModuleNameMasq &&) = delete;
	IdString ref() const;
	const TwinePool *pool() const;
	std::string escaped() const;
	std::string unescape() const;
	ModuleNameMasq &operator=(IdString id);
	ModuleNameMasq &operator=(const ModuleNameMasq &other) { return *this = other.ref(); }
	ModuleNameMasq &operator=(ModuleNameMasq &&other) { return *this = other.ref(); }
private:
	const Module *owner() const;
	Module *owner();
};

struct PooledName : NameMasqBase<PooledName> {
	PooledName() = default;
	explicit PooledName(IdString id) : id_(id) {}
	PooledName(const TwinePool *pool, IdString id) : pool_(pool), id_(id) {}
	PooledName(const Design *design, IdString id);
	PooledName(const Module *module, IdString id);
	template<typename D> PooledName(const NameMasqBase<D> &masq)
		: pool_(static_cast<const D &>(masq).pool()),
		  id_(static_cast<const D &>(masq).ref()) {}
	IdString ref() const { return id_; }
	const TwinePool *pool() const { return pool_; }
	std::string escaped() const;
	std::string unescape() const;
private:
	const TwinePool *pool_ = nullptr;
	IdString id_ = IdString::Null;
};

}

#endif
