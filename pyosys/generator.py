#!/usr/bin/env python3
#  yosys -- Yosys Open SYnthesis Suite
#
#  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
#
#  Permission to use, copy, modify, and/or distribute this software for any
#  purpose with or without fee is hereby granted, provided that the above
#  copyright notice and this permission notice appear in all copies.
#
#  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
#  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
#  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
#  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
#  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
#  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
#  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#
#  Written by Mohamed Gaber <me@donn.website>
#
#  Inspired by py_wrap_generator.py by Benedikt Tutzer
"""
This generates:
- Wrapper calls for opaque container types
- Full wrappers for select classes and all enums, global functions and global
  variables

Jump to "MARK: Inclusion and Exclusion" to control the above.

Please run ruff on this file in particular to make sure it parses with Python
<= 3.12. There is so much f-string use here that the outer quote thing
is a common problem. ``ruff check pyosys/generator.py`` suffices.
"""
import os
import io
import shutil
import argparse
from pathlib import Path
from sysconfig import get_paths
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, Iterable, Tuple, Union, Optional, List

import pybind11
from cxxheaderparser.simple import parse_file, ClassScope, NamespaceScope, EnumDecl
from cxxheaderparser.options import ParserOptions
from cxxheaderparser.preprocessor import make_gcc_preprocessor
from cxxheaderparser.types import (
    PQName,
    Type,
    Pointer,
    Reference,
    MoveReference,
    AnonymousName,
    Method,
    Function,
    Field,
    Variable,
    Array,
    FundamentalSpecifier,
    FunctionType,
)

__file_dir__ = Path(__file__).absolute().parent
__yosys_root__ = __file_dir__.parent


@dataclass
class PyosysClass:
    """
    Metadata about classes or structs intended to be wrapped using Pyosys.

    :param name: The base name of the class (without extra qualifiers)
    :param ref_only: Whether this class can be copied to Python, or only
        referenced.
    :param string_expr:
        A C++ expression that will be used for the ``__str__`` method in Python.

        The object will be available as a const reference with the identifier
        `s`.
    :param hash_expr:
        A C++ expression that will be fed to ``run_hash`` to declare a
        ``__hash__`` method for Python.

        The object will be vailable as a const reference with the identifier
        `s`.
    :param denylist: If specified, one or more methods can be excluded from
        wrapping.
    """

    name: str
    ref_only: bool = False

    # in the format s.(method or property) (or just s)
    string_expr: Optional[str] = None
    hash_expr: Optional[str] = None

    denylist: FrozenSet[str] = frozenset({})


@dataclass
class PyosysHeader:
    """
    :param name: The name of the header, i.e., its relative path to the Yosys root
    :param classes: A list of ``PyosysClass`` classes to be wrapped
    :param enums: A list of enums to be wrapped
    """

    name: str
    classes: List[PyosysClass] = field(default_factory=lambda: [])

    def __post_init__(self):
        self.classes_by_name = {}
        if classes := self.classes:
            for cls in classes:
                self.classes_by_name[cls.name] = cls


# MARK: Inclusion and Exclusion
global_denylist = frozenset(
    {
        # deprecated
        "builtin_ff_cell_types",
        "logv_file_error",
        # no implementation
        "set_verific_logging",
        # can't bridge to python cleanly
        ## std::regex
        "log_warn_regexes",
        "log_nowarn_regexes",
        "log_werror_regexes",
        ## function pointers
        "log_error_atexit",
        "log_verific_callback",
    }
)
pyosys_headers = [
    # Headers for incomplete types
    PyosysHeader("kernel/binding.h"),
    PyosysHeader("libs/sha1/sha1.h"),
    # Headers for globals
    PyosysHeader("kernel/log.h"),
    PyosysHeader("kernel/yosys.h"),
    PyosysHeader("kernel/cost.h"),
    # Headers with classes
    PyosysHeader(
        "kernel/celltypes.h",
        [PyosysClass("CellType", hash_expr="s.type"), PyosysClass("CellTypes")],
    ),
    PyosysHeader("kernel/consteval.h", [PyosysClass("ConstEval")]),
    PyosysHeader(
        "kernel/register.h",
        [
            # PyosysClass("Pass") # Virtual methods, manually bridged
        ],
    ),
    PyosysHeader(
        "kernel/rtlil.h",
        [
            PyosysClass(
                "IdString",
                string_expr="s.str()",
                hash_expr="s.str()",
                denylist=frozenset(
                    # shouldn't be messed with from python in general
                    {
                        "global_id_storage_",
                        "global_id_index_",
                        "global_refcount_storage_",
                        "global_free_idx_list_",
                        "last_created_idx_ptr_",
                        "last_created_idx_",
                        "builtin_ff_cell_types",
                    }
                ),
            ),
            PyosysClass(
                "Const",
                string_expr="s.as_string()",
                denylist=frozenset({"bits", "bitvectorize"}),
            ),
            PyosysClass("AttrObject", denylist=frozenset({"get_blackbox_attribute"})),
            PyosysClass("NamedObject"),
            PyosysClass("Selection"),
            # PyosysClass("Monitor"), # Virtual methods, manually bridged
            PyosysClass("CaseRule"),
            PyosysClass("SwitchRule"),
            PyosysClass("SyncRule"),
            PyosysClass(
                "Process",
                ref_only=True,
                string_expr="s.name.c_str()",
                hash_expr="s.name",
            ),
            PyosysClass("SigChunk"),
            PyosysClass("SigBit", hash_expr="s"),
            PyosysClass("SigSpec", hash_expr="s", denylist={"chunks"}),
            PyosysClass(
                "Cell",
                ref_only=True,
                string_expr="s.name.c_str()",
                hash_expr="s",
            ),
            PyosysClass(
                "Wire",
                ref_only=True,
                string_expr="s.name.c_str()",
                hash_expr="s",
            ),
            PyosysClass(
                "Memory",
                ref_only=True,
                string_expr="s.name.c_str()",
                hash_expr="s",
            ),
            PyosysClass(
                "Module",
                ref_only=True,
                string_expr="s.name.c_str()",
                hash_expr="s",
                denylist=frozenset({"Pow"}),  # has no implementation
            ),
            PyosysClass(
                "Design",
                string_expr="std::to_string(s.hashidx_)",
                hash_expr="s",
                denylist=frozenset({"selected_whole_modules"}),  # deprecated
            ),
        ],
    ),
]


@dataclass(frozen=True)  # hashable
class PyosysType:
    """
    Bit of a hacky object all-around: this is more or less used to encapsulate
    container types so they can be later made opaque using pybind.
    """

    base: str
    specialization: Tuple["PyosysType", ...]
    const: bool = False

    @classmethod
    def from_type(Self, type_obj, drop_const=False) -> "PyosysType":
        const = hasattr(type_obj, "const") and type_obj.const and not drop_const
        if isinstance(type_obj, Pointer):
            ptr_to = Self.from_type(type_obj.ptr_to)
            return Self("ptr", (ptr_to,), const)
        elif isinstance(type_obj, Reference):
            ref_to = Self.from_type(type_obj.ref_to)
            return Self("ref", (ref_to,), const)
        elif isinstance(type_obj, FunctionType):
            ret_type = Self.from_type(type_obj.return_type)
            param_types = (Self.from_type(p.type) for p in type_obj.parameters)
            return Self("fn", (ret_type, *param_types), False)
        assert isinstance(
            type_obj, Type
        ), f"unexpected c++ type object of type {type(type_obj)}"
        last_segment = type_obj.typename.segments[-1]
        base = last_segment.name
        specialization = tuple()
        if (
            hasattr(last_segment, "specialization")
            and last_segment.specialization is not None
        ):
            for template_arg in last_segment.specialization.args:
                specialization = (*specialization, Self.from_type(template_arg.arg))
        return Self(base, specialization, const)

    def generate_identifier(self):
        title = self.base.title()
        if len(self.specialization) == 0:
            return title

        if title == "Dict":
            key, value = self.specialization
            return f"{key.generate_identifier()}To{value.generate_identifier()}{title}"
        elif title == "Fn":
            identifier = self.specialization[0].generate_identifier()
            if identifier == "Void":
                identifier = ""
            else:
                identifier += "From"
            identifier += "And".join(
                p.generate_identifier() for p in self.specialization[1:]
            )
            return identifier

        return (
            "".join(spec.generate_identifier() for spec in self.specialization) + title
        )

    def generate_cpp_name(self):
        const_prefix = "const " * self.const
        if len(self.specialization) == 0:
            return const_prefix + self.base
        elif self.base == "ptr":
            return const_prefix + f"{self.specialization[0].generate_cpp_name()} *"
        elif self.base == "ref":
            return const_prefix + f"{self.specialization[0].generate_cpp_name()} &"
        elif self.base == "fn":
            param_cpp_names = (s.generate_cpp_name() for s in self.specialization[1:])
            return f"{self.specialization[0].generate_cpp_name()}({','.join(param_cpp_names)})"
        else:
            return (
                const_prefix
                + f"{self.base}<{', '.join(spec.generate_cpp_name() for spec in self.specialization)}>"
            )


class PyosysWrapperGenerator(object):
    def __init__(
        self,
        from_headers: Iterable[PyosysHeader],
        wrapper_stream: io.TextIOWrapper,
        header_stream: io.TextIOWrapper,
    ):
        self.headers = from_headers
        self.f = wrapper_stream
        self.f_inc = header_stream
        self.found_containers: Dict[PyosysType, Any] = {}
        self.class_registry: Dict[str, Tuple[ClassScope, PyosysClass]] = {}

    # entry point
    def generate(self):
        tpl = __file_dir__ / "wrappers_tpl.cc"
        preprocessor_opts = self.make_preprocessor_options()
        with open(tpl, encoding="utf8") as f:
            do_line_directive = True
            for i, line in enumerate(f):
                if do_line_directive:
                    self.f.write(f'#line {i + 1} "{tpl}"\n')
                    do_line_directive = False
                if "<!-- generated includes -->" in line:
                    for header in self.headers:
                        self.f.write(f'#include "{header.name}"\n')
                    do_line_directive = True
                elif "<!-- generated pymod-level code -->" in line:
                    for header in self.headers:
                        header_path = __yosys_root__ / header.name
                        parsed = parse_file(header_path, options=preprocessor_opts)
                        global_namespace = parsed.namespace
                        self.process_namespace(header, global_namespace)
                else:
                    self.f.write(line)

        for container, _ in self.found_containers.items():
            identifier = container.generate_identifier()
            print(
                f"using {identifier} = {container.generate_cpp_name()};",
                file=self.f_inc,
            )
            print(f"PYBIND11_MAKE_OPAQUE({identifier})", file=self.f_inc)

        print(
            f"static void bind_autogenerated_opaque_containers(py::module &m) {{",
            file=self.f_inc,
        )
        for container, _ in self.found_containers.items():
            identifier = container.generate_identifier()
            cxx = container.generate_cpp_name()
            tpl_args = [cxx]
            for spec in container.specialization:
                tpl_args.append(spec.generate_cpp_name())
            print(
                f'\tpy::hashlib::bind_{container.base}<{", ".join(tpl_args)}>(m, "{container.generate_identifier()}");',
                file=self.f_inc,
            )
            print(
                f"\tpy::implicitly_convertible<py::iterable, {identifier}>();",
                file=self.f_inc,
            )
        print(f"}}", file=self.f_inc)

    # helpers
    def make_preprocessor_options(self):
        py_include = get_paths()["include"]
        preprocessor_bin = shutil.which("clang++") or "g++"
        cxx_std = os.getenv("CXX_STD", "c++17")
        return ParserOptions(
            preprocessor=make_gcc_preprocessor(
                defines=["_YOSYS_", "YOSYS_ENABLE_PYTHON"],
                gcc_args=[preprocessor_bin, "-fsyntax-only", f"-std={cxx_std}"],
                include_paths=[str(__yosys_root__), py_include, pybind11.get_include()],
            ),
        )

    @staticmethod
    def find_containers(
        containers: Iterable[str], type_info: Any
    ) -> Dict[PyosysType, Any]:
        if isinstance(type_info, Pointer):
            return PyosysWrapperGenerator.find_containers(containers, type_info.ptr_to)
        if isinstance(type_info, MoveReference):
            return PyosysWrapperGenerator.find_containers(
                containers, type_info.moveref_to
            )
        if isinstance(type_info, Reference):
            return PyosysWrapperGenerator.find_containers(containers, type_info.ref_to)
        if not isinstance(type_info, Type):
            return {}
        segments = type_info.typename.segments
        containers_found = {}
        for segment in segments:
            if isinstance(segment, FundamentalSpecifier):
                continue
            if segment.name in containers:
                containers_found.update(
                    {PyosysType.from_type(type_info, drop_const=True): type_info}
                )
            if segment.specialization is not None:
                for arg in segment.specialization.args:
                    sub_containers = PyosysWrapperGenerator.find_containers(
                        containers, arg.arg
                    )
                    containers_found.update(sub_containers)
        return containers_found

    @staticmethod
    def find_anonymous_union(cls: ClassScope):
        if cls.class_decl.typename.classkey != "union":
            return None
        for s in cls.class_decl.typename.segments:
            if isinstance(s, AnonymousName):
                return s
        return None  # named union

    @staticmethod
    def get_parameter_types(function: Function) -> str:
        return ", ".join(p.type.format() for p in function.parameters)

    def register_containers(self, target: Union[Function, Field, Variable]) -> bool:
        supported = ("dict", "idict", "pool", "set", "vector")
        found = False
        if isinstance(target, Function):
            return_type_containers = self.find_containers(supported, target.return_type)
            found = found or len(return_type_containers)
            self.found_containers.update(return_type_containers)

            for parameter in target.parameters:
                parameter_containers = self.find_containers(supported, parameter.type)
                found = found or len(parameter_containers)
                self.found_containers.update(parameter_containers)
        else:
            variable_containers = self.find_containers(supported, target.type)
            found = found or len(variable_containers)
            self.found_containers.update(variable_containers)
        return found

    # processors
    def get_overload_cast(
        self, function: Function, class_basename: Optional[str]
    ) -> str:
        is_method = isinstance(function, Method)
        function_return_type = function.return_type.format()
        if class_basename == "Const" and function_return_type in {
            "iterator",
            "const_iterator",
        }:
            # HACK: qualify Const's iterators
            function_return_type = f"{class_basename}::{function_return_type}"

        pointer_kind = (
            f"{class_basename}::*" if (is_method and not function.static) else "*"
        )

        retval = f"static_cast <"
        retval += function_return_type
        retval += f"({pointer_kind})"
        retval += f"({self.get_parameter_types(function)})"
        if is_method and function.const:
            retval += " const"
        retval += ">"
        retval += "(&"
        if is_method:
            retval += f"{class_basename}::"
        retval += function.name.segments[-1].format()
        retval += ")"
        return retval

    def get_definition_args(
        self,
        function: Function,
        class_basename: Optional[str],
        python_name_override: Optional[str] = None,
    ) -> List[str]:
        function_basename = function.name.segments[-1].format()

        python_function_basename = python_name_override or keyword_aliases.get(
            function_basename, function_basename
        )

        def_args = [f'"{python_function_basename}"']
        def_args.append(self.get_overload_cast(function, class_basename))
        for i, parameter in enumerate(function.parameters):
            name = parameter.name or f"arg{i}"
            parameter_arg = f'py::arg("{name}")'
            if parameter.default is not None:
                parameter_arg += f" = {parameter.default.format()}"
            def_args.append(parameter_arg)

        return def_args

    def process_method(self, metadata: PyosysClass, function: Method):
        if (
            function.deleted
            or function.template
            or function.vararg
            or function.access != "public"
            or function.pure_virtual
            or function.destructor
        ):
            return

        if any(isinstance(p.type, MoveReference) for p in function.parameters):
            # skip move constructors
            return

        if len(function.name.segments) > 1:
            # can't handle, skip
            return

        if function.constructor:
            if (
                not metadata.ref_only
            ):  # ref-only classes should not be constructed from python
                print(
                    f"\t\t\t.def(py::init<{self.get_parameter_types(function)}>())",
                    file=self.f,
                )
            return

        python_name_override = None
        if function.operator is not None:
            if function.operator == "==":
                python_name_override = "__eq__"
            elif function.operator == "!=":
                python_name_override = "__ne__"
            elif function.operator == "<":
                python_name_override = "__lt__"
            else:
                return

        self.register_containers(function)

        definition_fn = "def"
        if function.static:
            definition_fn = "def_static"

        definition_args = self.get_definition_args(
            function, metadata.name, python_name_override
        )

        print(
            f"\t\t\t.{definition_fn}({', '.join(definition_args)})",
            file=self.f,
        )

    def process_function(self, function: Function):
        if function.deleted or function.template or function.vararg or function.static:
            return

        if function.operator is not None:
            # Python doesn't do global operators
            return

        if function.name.segments[-1].format() in global_denylist:
            return

        self.register_containers(function)

        print(
            f"\t\t\tm.def({', '.join(self.get_definition_args(function, None))});",
            file=self.f,
        )

    def process_field(self, metadata: PyosysClass, field: Field):
        if field.access != "public":
            return

        if field.name is None:
            # anonymous structs and unions
            # unions handled in calling function
            # ASSUMPTION: No anonymous structs in the yosys codebase
            # 			  (they're not in the C++ standard anyway)
            return

        unique_ptrs = self.find_containers(("unique_ptr",), field.type)
        if len(unique_ptrs):
            # TODO: figure out how to bridge unique pointers maybe does anyone
            # care
            return

        has_containers = self.register_containers(field)

        definition_fn = f"def_{'readonly' if field.type.const else 'readwrite'}"
        if field.static:
            definition_fn += "_static"

        field_python_basename = keyword_aliases.get(field.name, field.name)

        def_args = [
            f'"{field_python_basename}"',
            f"&{metadata.name}::{field.name}",
        ]
        def_args.append("py::return_value_policy::copy")
        print(
            f"\t\t\t.{definition_fn}({', '.join(def_args)})",
            file=self.f,
        )

    def process_variable(self, variable: Variable):
        if isinstance(variable.type, Array):
            return

        variable_basename = variable.name.segments[-1].format()
        if variable_basename in global_denylist:
            return

        self.register_containers(variable)

        definition_fn = (
            f"def_{'readonly' if variable.type.const else 'readwrite'}_static"
        )

        variable_python_basename = keyword_aliases.get(
            variable_basename, variable_basename
        )
        variable_name = variable.name.format()

        print(
            f'\t\t\tglobal_variables.{definition_fn}("{variable_python_basename}", &{variable_name});',
            file=self.f,
        )

    def process_class_members(
        self,
        metadata: PyosysClass,
        base_metadata: PyosysClass,
        cls: ClassScope,
        basename: str,
    ):
        for method in cls.methods:
            if method.name.segments[-1].name in base_metadata.denylist:
                continue
            self.process_method(metadata, method)

        visited_anonymous_unions = set()
        for field_ in cls.fields:
            if field_.name in base_metadata.denylist:
                continue
            self.process_field(metadata, field_)

            # Handle anonymous unions
            for subclass in cls.classes:
                if subclass.class_decl.access != "public":
                    continue
                if au := self.find_anonymous_union(subclass):
                    if au.id in visited_anonymous_unions:
                        continue
                    visited_anonymous_unions.add(au.id)
                    for subfield in subclass.fields:
                        self.process_field(metadata, subfield)

        for base in cls.class_decl.bases:
            if base.access != "public":
                continue
            name = base.typename.segments[-1].format()
            if processed := self.class_registry.get(name):
                base_scope, base_metadata = processed
                self.process_class_members(
                    metadata, base_metadata, base_scope, basename
                )

    def process_class(
        self,
        metadata: PyosysClass,
        cls: ClassScope,
        namespace_components: Tuple[str, ...],
    ):
        pqname: PQName = cls.class_decl.typename
        full_path = list(namespace_components) + [
            segment.format() for segment in pqname.segments
        ]
        basename = full_path.pop()
        self.class_registry[basename] = (cls, metadata)

        declaration_namespace = "::".join(full_path)
        tpl_args = [basename]
        if metadata.ref_only:
            tpl_args.append(f"std::unique_ptr<{basename}, py::nodelete>")
        print(
            f'\t\t{{using namespace {declaration_namespace}; py::class_<{", ".join(tpl_args)}>(m, "{basename}")',
            file=self.f,
        )

        self.process_class_members(metadata, metadata, cls, basename)

        if expr := metadata.string_expr:
            print(
                f'\t\t.def("__str__", [](const {basename} &s) {{ return {expr}; }})',
                file=self.f,
            )
            print(
                f'\t\t.def("__repr__", [](const {basename} &s) {{ std::stringstream ss; ss << "<{basename} " << {expr} << ">"; return ss.str(); }})',
                file=self.f,
            )

        if expr := metadata.hash_expr:
            print(
                f'\t\t.def("__hash__", [](const {basename} &s) {{ return run_hash({expr}); }})',
                file=self.f,
            )

        print(f"\t\t;}}", file=self.f)

    def process_enum(
        self,
        enum: EnumDecl,
        namespace_components: Tuple[str, ...],
    ):
        pqname: PQName = enum.typename
        full_path = list(namespace_components) + [
            segment.format() for segment in pqname.segments
        ]
        basename = full_path.pop()

        declaration_namespace = "::".join(full_path)
        print(
            f'\t\t{{using namespace {declaration_namespace}; py::native_enum<{basename}>(m, "{basename}", "enum.Enum")',
            file=self.f,
        )
        enum_class = enum.typename.classkey == "enum class"
        for value in enum.values:
            enum_class_qualifier = f"{basename}::" * enum_class
            print(
                f'\t\t\t.value("{value.name}", {enum_class_qualifier}{value.name})',
                file=self.f,
            )
        print(f"\t\t\t.finalize();}}", file=self.f)

    def process_namespace(
        self,
        header: PyosysHeader,
        ns: NamespaceScope,
        namespace_components: Tuple[str, ...] = (),
    ):
        for name, subns in ns.namespaces.items():
            self.process_namespace(header, subns, (*namespace_components, name))
        if len(namespace_components) and (len(ns.functions) + len(ns.variables)):
            # TODO: Not essential but maybe move namespace usage into
            # process_function for consistency?
            print(
                f"\t\t{{ using namespace {'::'.join(namespace_components)};",
                file=self.f,
            )
            for function in ns.functions:
                self.process_function(function)
            for variable in ns.variables:
                self.process_variable(variable)
            print(f"\t\t}}", file=self.f)
        for enum in ns.enums:
            self.process_enum(enum, namespace_components)
        for cls in ns.classes:
            pqname = cls.class_decl.typename
            declared_name_str = pqname.segments[-1].format()
            if cls_metadata := header.classes_by_name.get(declared_name_str):
                self.process_class(cls_metadata, cls, namespace_components)


keyword_aliases = {
    "False": "False_",
    "None": "None_",
    "True": "True_",
    "and": "and_",
    "as": "as_",
    "assert": "assert_",
    "break": "break_",
    "class": "class_",
    "continue": "continue_",
    "def": "def_",
    "del": "del_",
    "elif": "elif_",
    "else": "else_",
    "except": "except_",
    "for": "for_",
    "from": "from_",
    "global": "global_",
    "if": "if_",
    "import": "import_",
    "in": "in_",
    "is": "is_",
    "lambda": "lambda_",
    "nonlocal": "nonlocal_",
    "not": "not_",
    "or": "or_",
    "pass": "pass_",
    "raise": "raise_",
    "return": "return_",
    "try": "try_",
    "while": "while_",
    "with": "with_",
    "yield": "yield_",
}


def print_includes():
    for header in pyosys_headers:
        print(header.name)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--debug", default=0, type=int)
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument("--print-includes", action="store_true")
    group.add_argument("output", nargs="?")
    ns = ap.parse_args()
    if ns.print_includes:
        print_includes()
        exit(0)

    out_path = Path(ns.output)
    out_inc = out_path.parent / (out_path.stem + ".inc.cc")
    with open(out_path, "w", encoding="utf8") as f, open(
        out_inc, "w", encoding="utf8"
    ) as inc_f:
        generator = PyosysWrapperGenerator(
            from_headers=pyosys_headers, wrapper_stream=f, header_stream=inc_f
        )
        generator.generate()
