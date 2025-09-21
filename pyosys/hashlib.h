// -------------------------------------------------------
// Written by Mohamed Gaber in 2025 <me@donn.website>
// Based on kernel/hashlib.h by Claire Xenia Wolf <claire@yosyshq.com>
// -------------------------------------------------------
// This header is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.
//
// In jurisdictions that recognize copyright laws, the author or authors
// of this software dedicate any and all copyright interest in the
// software to the public domain. We make this dedication for the benefit
// of the public at large and to the detriment of our heirs and
// successors. We intend this dedication to be an overt act of
// relinquishment in perpetuity of all present and future rights to this
// software under copyright law.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.
//
// For more information, please refer to <https://unlicense.org/>
// -------------------------------------------------------
//
// pybind11 bridging headers for hashlib template
//
// These are various binding functions that expose hashlib templates as opaque
// types (https://pybind11.readthedocs.io/en/latest/advanced/cast/stl.html#making-opaque-types).
//
// Opaque types cross language barries by reference, not value. This allows
// things like mutating containers that are class properties.
//
// All methods should be vaguely in the same order as the python reference
// https://docs.python.org/3/library/stdtypes.html
//
#include <optional> // optional maps cleanest to methods that accept None in Python

#include <pybind11/pybind11.h> // base
#include <pybind11/stl.h> // std::optional
#include <pybind11/operators.h> // easier operator binding

#include "kernel/hashlib.h"

namespace pybind11 {

template<typename T>
struct is_pointer { static const bool value = false; };
template<typename T>
struct is_pointer<T*> { static const bool value = true; };

bool is_mapping(object obj) {
	object mapping = module_::import("collections.abc").attr("Mapping");
	return isinstance(obj, mapping);
}


// also used for std::set because the semantics are close enough
template <typename C, typename T>
void bind_pool(module &m, const char *name_cstr) {
	std::string {name_cstr};

	class_<C>(m, name_cstr)
		.def(init<>())
		.def("__len__", [](const C &s){ return (size_t)s.size(); })
		.def("__contains__", [](const C &s, const T &v){ return s.count(v); })
		.def("__delitem__", [](C &s, const T &v) {
			auto n = s.erase(v);
			if (n == 0) throw key_error(str(cast(v)));
		})
		// TODO: disjoint, subset, union, intersection, difference, symdif
		.def("copy", [](const C &s) {
			return new C(s);
		})
		.def("update", [](C &s, iterable iterable) {
			for (auto item: iterable) {
				s.insert(item.cast<T>());
			}
		})
		.def("add", [](C &s, const T &v){ s.insert(v); })
		.def("remove", [](C &s, const T &v){
			auto n = s.erase(v);
			if (n == 0) throw key_error(str(cast(v)));
		})
		.def("discard", [](C &s, const T &v){ s.erase(v); })
		.def("clear", [](C &s){ s.clear(); })
		.def("pop", [](C &s){
			if (s.size() == 0) {
				throw key_error("empty pool");
			}
			auto result = *s.begin();
			s.erase(result);
			return result;
		})
		.def("__bool__", [](const C &s) { return s.size() != 0; })
		.def("__iter__", [](const C &s){
			return make_iterator(s.begin(), s.end());
		}, keep_alive<0,1>())
		.def("__repr__", [name_cstr](const C &s){
			return std::string("<") + name_cstr + " size=" + std::to_string(s.size()) + ">";
		});
}

template <typename C, typename K, typename V>
void update_dict(C *target, iterable &iterable_or_mapping) {
	if (is_mapping(iterable_or_mapping)) {
		for (const auto &key: iterable_or_mapping) {
			(*target)[cast<K>(key)] = cast<V>(iterable_or_mapping[key]);
		}
	} else {
		for (const auto &pair: iterable_or_mapping) {
			if (len(pair) != 2) {
				throw value_error(str("iterable element %s has more than two elements").format(str(pair)));
			}
			(*target)[cast<K>(pair[cast(0)])] = cast<V>(pair[cast(1)]);
		}
	}
}

template <typename C, typename K, typename V>
void bind_dict(module &m, const char *name_cstr) {
	std::string {name_cstr};

	class_<C>(m, name_cstr)
		.def(init<>())
		.def("__len__", [](const C &s){ return (size_t)s.size(); })
		.def("__getitem__", [](const C &s, const K &k) { return s.at(k); })
		.def("__setitem__", [](C &s, const K &k, const V &v) { s[k] = v; })
		.def("__delitem__", [](C &s, const K &k) {
			auto n = s.erase(k);
			if (n == 0) throw key_error("remove: key not found");
		})
		.def("__contains__", [](const C &s, const K &k) { return s.count(k) != 0; })
		.def("__iter__", [](const C &s){
			return make_key_iterator(s.begin(), s.end());
		}, keep_alive<0,1>())
		.def("clear", [](C &s){ s.clear(); })
		.def("copy", [](const C &s) {
			return new C(s);
		})
		.def("get", [](const C &s, const K& k, std::optional<const V> &default_) {
			if (default_.has_value()) {
				return s.at(k, *default_);
			} else {
				return s.at(k);
			}
		}, arg("key"), arg("default") = std::nullopt)
		.def("items", [](const C &s){
			return make_iterator(s.begin(), s.end());
		}, keep_alive<0,1>())
		.def("keys", [](const C &s){
			return make_key_iterator(s.begin(), s.end());
		}, keep_alive<0,1>())
		.def("pop", [](const C &s, const K& k, std::optional<const V> &default_) {
			if (default_.has_value()) {
				return s.at(k, *default_);
			} else {
				return s.at(k);
			}
		}, arg("key"), arg("default") = std::nullopt)
		.def("popitem", [name_cstr](args _) { throw std::runtime_error(std::string(name_cstr) + " is not an ordered dictionary"); })
		.def("setdefault", [name_cstr](C &s, const K& k, std::optional<const V> &default_) {
			auto it = s.find(k);
			if (it != s.end()) {
				return it->second;
			}
			if (default_.has_value()) {
				s[k] = *default_;
				return *default_;
			}
			 // if pointer, nullptr can be our default
			if constexpr (is_pointer<V>::value) {
				s[k] = nullptr;
				return (V)nullptr;
			}
			// TODO: std::optional? do we care?
			throw type_error(std::string("the value type of ") + name_cstr + " is not nullable");
		}, arg("key"), arg("default") = std::nullopt)
		.def("update", [](C &s, iterable iterable_or_mapping) {
			update_dict<C, K, V>(&s, iterable_or_mapping);
		}, arg("iterable_or_mapping"))
		.def("values", [](const C &s){
			return make_value_iterator(s.begin(), s.end());
		}, keep_alive<0,1>())
		.def("__or__", [](const C &s, iterable iterable_or_mapping) {
			auto result = new C(s);
			update_dict<C, K, V>(result, iterable_or_mapping);
			return result;
		})
		.def("__ior__", [](C &s, iterable iterable_or_mapping) {
			update_dict<C, K, V>(&s, iterable_or_mapping);
			return s;
		})
		.def("__bool__", [](const C &s) { return s.size() != 0; })
		.def("__repr__", [name_cstr](const C &s){
			return std::string("<") + name_cstr + " size=" + std::to_string(s.size()) + ">";
		});
}

// idict is a special bijection and doesn't map cleanly to dict
//
// it's cleanest, despite the inconsistency with __getitem__, to just think of
// the hashable as key and the integer as value
template <typename C, typename K>
void bind_idict(module &m, const char *name_cstr) {
	std::string {name_cstr};

	auto cls = class_<C>(m, name_cstr)
		.def(init<>())
		.def("__len__", [](const C &s){ return (size_t)s.size(); })
		.def("__getitem__", [](const C &s, int v) { return s[v]; })
		.def("__call__", [](C &s, const K &k) { return s(k); })
		.def("__contains__", [](const C &s, const K &k) {
			return s.count(k) != 0;
		})
		.def("__iter__", [](const C &s){
			return make_iterator(s.begin(), s.end());
		}, keep_alive<0,1>())
		.def("clear", [](C &s) {
			s.clear();
		})
		.def("copy", [](const C &s) {
			return new C(s);
		})
		.def("get", [](const C &s, const K& k, std::optional<int> &default_) {
			if (default_.has_value()) {
				return s.at(k, *default_);
			} else {
				return s.at(k);
			}
		}, arg("key"), arg("default") = std::nullopt)
		.def("keys", [](const C &s){
			return make_iterator(s.begin(), s.end());
		})
		.def("values", [](args _){
			throw type_error("idicts do not support iteration on the integers");
		})
		.def("items", [](args _){
			throw type_error("idicts do not support pairwise iteration");
		})
		.def("update", [](C &s, iterable iterable) {
			for (auto &e: iterable) {
				s(cast<K>(e));
			}
		})
		.def("__or__", [](const C &s, iterable iterable) {
			auto result = new C(s);
			for (auto &e: iterable) {
				(*result)(cast<K>(e));
			}
			return result;
		})
		.def("__ior__", [](C &s, iterable iterable) {
			for (auto &e: iterable) {
				s(cast<K>(e));
			}
			return s;
		})
		.def("__bool__", [](const C &s) { return s.size() != 0; })
		.def("__repr__", [name_cstr](const C &s){
			return std::string("<") + name_cstr + " size=" + std::to_string(s.size()) + ">";
		});

	for (const char *mutator: {"__setitem__", "__delitem__", "pop", "popitem", "setdefault"}) {
		cls.def(mutator, [](args _) {
			throw type_error("idicts do not support arbitrary element mutation");
		});
	}
}
}; // namespace pybind11
