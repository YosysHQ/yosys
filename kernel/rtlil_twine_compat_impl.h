#ifndef RTLIL_TWINE_COMPAT_IMPL_H
#define RTLIL_TWINE_COMPAT_IMPL_H

#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Winvalid-offsetof"
#endif

namespace RTLIL {

template<typename Owner>
inline const Owner *ObjNameMasq<Owner>::owner() const {
	return reinterpret_cast<const Owner *>(
		reinterpret_cast<const char *>(this) - offsetof(Owner, name));
}

template<typename Owner>
inline Owner *ObjNameMasq<Owner>::owner() {
	return reinterpret_cast<Owner *>(
		reinterpret_cast<char *>(this) - offsetof(Owner, name));
}

template<typename Owner>
inline IdString ObjNameMasq<Owner>::ref() const {
	return owner()->name_;
}

template<typename Owner>
inline const TwinePool *ObjNameMasq<Owner>::pool() const {
	const Owner *o = owner();
	return o->module && o->module->design ? &o->module->design->twines : nullptr;
}

template<typename Owner>
inline std::string ObjNameMasq<Owner>::escaped() const {
	return masq_detail::render_escaped(pool(), ref());
}

template<typename Owner>
inline std::string ObjNameMasq<Owner>::unescape() const {
	return masq_detail::render_unescaped(pool(), ref());
}

template<typename Owner>
inline ObjNameMasq<Owner> &ObjNameMasq<Owner>::operator=(IdString id) {
	owner()->name_ = id;
	return *this;
}

inline const Cell *CellTypeMasq::owner() const {
	return reinterpret_cast<const Cell *>(
		reinterpret_cast<const char *>(this) - offsetof(Cell, type));
}

inline Cell *CellTypeMasq::owner() {
	return reinterpret_cast<Cell *>(
		reinterpret_cast<char *>(this) - offsetof(Cell, type));
}

inline IdString CellTypeMasq::ref() const {
	return owner()->type_impl;
}

inline const TwinePool *CellTypeMasq::pool() const {
	const Cell *c = owner();
	return c->module && c->module->design ? &c->module->design->twines : nullptr;
}

inline std::string CellTypeMasq::escaped() const {
	return masq_detail::render_escaped(pool(), ref());
}

inline std::string CellTypeMasq::unescape() const {
	return masq_detail::render_unescaped(pool(), ref());
}

inline CellTypeMasq &CellTypeMasq::operator=(IdString id) {
	owner()->type_impl = id;
	return *this;
}

inline const Module *ModuleNameMasq::owner() const {
	return reinterpret_cast<const Module *>(
		reinterpret_cast<const char *>(this) - offsetof(Module, name));
}

inline Module *ModuleNameMasq::owner() {
	return reinterpret_cast<Module *>(
		reinterpret_cast<char *>(this) - offsetof(Module, name));
}

inline IdString ModuleNameMasq::ref() const {
	return owner()->name_;
}

inline const TwinePool *ModuleNameMasq::pool() const {
	const Module *m = owner();
	return m->design ? &m->design->twines : nullptr;
}

inline std::string ModuleNameMasq::escaped() const {
	return masq_detail::render_escaped(pool(), ref());
}

inline std::string ModuleNameMasq::unescape() const {
	return masq_detail::render_unescaped(pool(), ref());
}

inline ModuleNameMasq &ModuleNameMasq::operator=(IdString id) {
	owner()->name_ = id;
	return *this;
}

inline PooledName::PooledName(const Design *design, IdString id)
	: pool_(design ? &design->twines : nullptr), id_(id) { }

inline PooledName::PooledName(const Module *module, IdString id)
	: PooledName(module ? module->design : nullptr, id) { }

inline std::string PooledName::escaped() const {
	return masq_detail::render_escaped(pool_, id_);
}

inline std::string PooledName::unescape() const {
	return masq_detail::render_unescaped(pool_, id_);
}

}

#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif

template<typename Derived>
inline void log_dump_val_worker(const RTLIL::NameMasqBase<Derived> &name) {
	log("%s", static_cast<const Derived &>(name).unescape());
}

#endif
