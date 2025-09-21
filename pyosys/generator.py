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
#  Author: Benedikt Tutzer
#  Modified for pybind11 by: Mohamed Gaber

import argparse
import copy
from enum import Enum
from io import StringIO
from pathlib import Path
from functools import wraps
from typing import ClassVar, Optional

__file_dir__ = Path(__file__).absolute().parent


def autostring(fn):
	@wraps(fn)
	def wrapper(*args, **kwargs):
		if "stream" not in kwargs:
			stream = StringIO()
			fn(*args, stream=stream, **kwargs)
			return stream.getvalue()
		else:
			fn(*args, **kwargs)

	return wrapper


# Map c++ operator Syntax to Python functions
wrappable_operators = {
	"<": "__lt__",
	"==": "__eq__",
	"!=": "__ne__",
	"+": "__add__",
	"-": "__sub__",
	"*": "__mul__",
	"/": "__div__",
	"()": "__call__",
}

# Restrict certain strings from being function names in Python
keyword_aliases = {
	"in": "in_",
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

# These can be used without any explicit conversion
autocast_types = {
	"void": "void",
	"bool": "bool",
	"int": "int",
	"double": "double",
	"size_t": "size_t",
	"std::string": "std::string",
	"string": "string",
	"char_p": "char_p",
	"std::source_location": "std::source_location",
	"source_location": "source_location",
	"State": "RTLIL::State",
	# trampoline types
	"Pass": "RTLIL::Pass",
	"Monitor": "RTLIL::Monitor",
}

def strip_std_prefix(str_in):
	# removesuffix is python 3.9+
	std_namespace = "std::"
	if str_in.startswith(std_namespace):
		return str_in[len(std_namespace):]
	return str_in


# Ways to link between Python- and C++ Objects
class link_types(Enum):
	global_list = 1  # Identical to pointer, kept for historical reasons
	ref_copy = 2  # Copy
	pointer = 3  # The Python Object contains a pointer to its C++
	# counterpart
	derive = 4  # Identical to ref_copy, kept for historical reasons


class attr_types(Enum):
	star = "*"
	amp = "&"
	ampamp = "&&"
	default = ""


# For source-files
class Source:
	name = ""
	classes = []

	def __init__(self, name, classes):
		self.name = name
		self.classes = classes


# Splits a list by the given delimiter, without splitting strings inside
# pointy-brackets (< and >)
def split_list(str_def, delim):
	str_def = str_def.strip()
	if len(str_def) == 0:
		return []
	if str_def.count(delim) == 0:
		return [str_def]
	if str_def.count("<") == 0:
		return str_def.split(delim)
	if str_def.find("<") < str_def.find(" "):
		closing = find_closing(
			str_def[str_def.find("<") + 1 :], "<", ">"
		) + str_def.find("<")
		comma = str_def[closing:].find(delim)
		if comma == -1:
			return [str_def]
		comma = closing + comma
	else:
		comma = str_def.find(delim)
	rest = split_list(str_def[comma + 1 :], delim)
	ret = [str_def[:comma]]
	if rest != None and len(rest) != 0:
		ret.extend(rest)
	return ret


# Represents a Type
class WType:
	name = ""
	cont = None
	attr_type = attr_types.default

	def __init__(self, name="", cont=None, attr_type=attr_types.default):
		self.name = name
		self.cont = cont
		self.attr_type = attr_type

	# Python type-string
	def gen_text(self):
		text = self.name
		if self.name in enum_names:
			text = enum_by_name(self.name).namespace + "::" + self.name
		if self.cont != None:
			return self.cont.gen_identifier()
		return text

	# C++ type-string
	def gen_text_cpp(self):
		postfix = ""
		if self.attr_type == attr_types.star:
			postfix = " *"
		elif self.attr_type == attr_types.amp:
			postfix = " &"
		elif self.attr_type == attr_types.ampamp:
			postfix = " &&"
		if self.name in classnames:
			return class_by_name(self.name).namespace + "::" + self.name + postfix
		if self.name in enum_names:
			return enum_by_name(self.name).namespace + "::" + self.name + postfix
		if self.name in autocast_types:
			return autocast_types[self.name] + postfix
		text = self.name
		if self.cont != None:
			text += "<"
			for a in self.cont.args:
				text += a.gen_text_cpp() + ", "
			text = text[:-2]
			text += ">"
		return text

	@staticmethod
	def from_string(str_def, containing_file, line_number):
		str_def = str_def.strip()
		if len(str_def) == 0:
			return None
		str_def = str_def.replace(
			"RTLIL::SigSig", "std::pair<SigSpec, SigSpec>"
		).replace("SigSig", "std::pair<SigSpec, SigSpec>")
		t = WType()
		t.name = ""
		t.cont = None
		t.attr_type = attr_types.default
		if str_def.find("<") != -1:  # and str_def.find("<") < str_def.find(" "):
			str_def = str_def.replace("const ", "")

			candidate = WContainer.from_string(str_def, containing_file, line_number)
			if candidate == None:
				return None
			t.name = str_def[: str_def.find("<")]

			if t.name.count("*") + t.name.count("&") > 1:
				return None

			if t.name.count("*") == 1 or str_def[0] == "*" or str_def[-1] == "*":
				t.attr_type = attr_types.star
				t.name = t.name.replace("*", "")
			elif t.name.count("&&") == 1:
				t.attr_type = attr_types.ampamp
				t.name = t.name.replace("&&", "")
			elif t.name.count("&") == 1 or str_def[0] == "&" or str_def[-1] == "&":
				t.attr_type = attr_types.amp
				t.name = t.name.replace("&", "")

			t.cont = candidate
			if t.name not in known_containers:
				return None
			return t

		prefix = ""

		if str.startswith(str_def, "const "):
			if "char_p" in str_def:
				prefix = "const "
			str_def = str_def[6:]
		if str.startswith(str_def, "unsigned "):
			prefix = "unsigned " + prefix
			str_def = str_def[9:]
		while str.startswith(str_def, "long "):
			prefix = "long " + prefix
			str_def = str_def[5:]
		while str.startswith(str_def, "short "):
			prefix = "short " + prefix
			str_def = str_def[6:]

		str_def = str_def.split("::")[-1]

		if str_def.count("*") + str_def.count("&") >= 2:
			return None

		if str_def.count("*") == 1:
			t.attr_type = attr_types.star
			str_def = str_def.replace("*", "")
		elif str_def.count("&&") == 1:
			t.attr_type = attr_types.ampamp
			str_def = str_def.replace("&&", "")
		elif str_def.count("&") == 1:
			t.attr_type = attr_types.amp
			str_def = str_def.replace("&", "")

		if (
			len(str_def) > 0
			and str_def.split("::")[-1] not in autocast_types
			and str_def.split("::")[-1] not in classnames
			and str_def.split("::")[-1] not in enum_names
		):
			return None

		if str_def.count(" ") == 0:
			t.name = (prefix + str_def).replace("char_p", "char *")
			t.cont = None
			return t
		return None

	def gen_identifier(self):
		if self.cont:
			return self.cont.gen_identifier()
		return self.name.title()

	def as_wclass(self) -> Optional["WClass"]:
		return class_by_name(self.name)

	def __repr__(self):
		return f"{self.__class__.__qualname__}(**{repr(self.__dict__)})"


# Associate the "Translators" with their c++ type
known_containers = {
	"std::set",
	"std::vector",
	"std::map",
	"std::pair",
	"pool",
	"idict",
	"dict",
	"RTLIL::ObjRange"
}

# Represents a container-type
class WContainer:
	name = ""
	args = []

	def from_string(str_def, containing_file, line_number):
		if str_def == None or len(str_def) < 4:
			return None
		cont = WContainer()
		cont.name = str_def[: str_def.find("<")]
		str_def = str_def[str_def.find("<") + 1 : find_closing(str_def, "<", ">")]
		cont.args = []
		for arg in split_list(str_def, ","):
			candidate = WType.from_string(arg.strip(), containing_file, line_number)
			if candidate == None:
				return None
			if candidate.name == "void":
				return None
			cont.args.append(candidate)
		return cont

	# generate the c++ type string
	def gen_type_cpp(self):
		tpl_args = []
		for arg in self.args:
			postfix = (arg.attr_type == attr_types.star) * " *"
			if arg.name in autocast_types:
				tpl_args.append(autocast_types[arg.name] + postfix)
			elif arg.name in known_containers:
				tpl_args.append(arg.cont.gen_type_cpp())
			else:
				tpl_args.append(arg.as_wclass().fully_qualified_name() + postfix)
		return f'{self.name}<{ ", ".join(tpl_args) }>'

	def gen_identifier(self):
		container = strip_std_prefix(self.name).title()

		if container == "Dict":
			assert len(self.args) == 2
			return f"{self.args[0].gen_identifier()}To{self.args[1].gen_identifier()}{container}"

		args = []
		for arg in self.args:
			arg_name = arg.name.title()
			if arg.cont:
				arg_name = arg.cont.gen_identifier()
			args.append(arg_name)
		args.append(container)
		result = "".join(args)
		if result == "SigspecSigspecPair":
			return "SigSig"
		return result

	@autostring
	def gen_boost_py(self, *, stream):
		bind_fn = "py::bind_" + strip_std_prefix(self.name)
		tpl_args = [self.gen_type_cpp()]
		if bind_fn != "py::bind_vector":
			# using custom bind function, can't use ::value so need more
			# template arguments
			for arg in self.args:
				postfix = (arg.attr_type == attr_types.star) * " *"
				if arg.name in autocast_types:
					tpl_args.append(autocast_types[arg.name] + postfix)
				elif arg.name in known_containers:
					tpl_args.append(arg.cont.gen_type_cpp())
				else:
					tpl_args.append(arg.as_wclass().fully_qualified_name() + postfix)
		if bind_fn == "py::bind_set":
			bind_fn = "py::bind_pool"
		stream.write(f'\t\t{bind_fn}<{",".join(tpl_args)}>(m, "{self.gen_identifier()}");\n')

	def __repr__(self):
		return f"{self.__class__.__qualname__}(**{repr(self.__dict__)})"


class Attribute:
	wtype = None
	varname = None
	is_const = False
	default_value = None
	pos = None
	pos_counter = 0

	def __init__(self, wtype, varname, is_const=False, default_value=None):
		self.wtype = wtype
		self.varname = varname
		self.is_const = is_const
		self.default_value = None
		self.container = None

	@staticmethod
	def from_string(str_def, containing_file, line_number):
		if len(str_def) < 3:
			return None
		orig = str_def
		arg = Attribute(None, None)
		prefix = ""
		arg.wtype = None
		arg.varname = None
		arg.is_const = False
		arg.default_value = None
		arg.container = None
		if str.startswith(str_def, "const "):
			arg.is_const = True
			str_def = str_def[6:]
		if str.startswith(str_def, "unsigned "):
			prefix = "unsigned "
			str_def = str_def[9:]
		while str.startswith(str_def, "long "):
			prefix = "long " + prefix
			str_def = str_def[5:]
		while str.startswith(str_def, "short "):
			prefix = "short " + prefix
			str_def = str_def[6:]

		if str_def.find("<") != -1 and str_def.find("<") < str_def.find(" "):
			closing = (
				find_closing(str_def[str_def.find("<") :], "<", ">")
				+ str_def.find("<")
				+ 1
			)
			arg.wtype = WType.from_string(
				str_def[:closing].strip(), containing_file, line_number
			)
			str_def = str_def[closing + 1 :]
		else:
			if str_def.count(" ") > 0:
				arg.wtype = WType.from_string(
					prefix + str_def[: str_def.find(" ")].strip(),
					containing_file,
					line_number,
				)
				str_def = str_def[str_def.find(" ") + 1 :]
			else:
				arg.wtype = WType.from_string(
					prefix + str_def.strip(), containing_file, line_number
				)
				str_def = ""
				arg.varname = ""

		if arg.wtype == None:
			return None
		if str_def.count("=") == 0:
			arg.varname = str_def.strip()
			if arg.varname.find(" ") > 0:
				return None
		else:
			arg.varname = str_def[: str_def.find("=")].strip()
			if arg.varname.find(" ") > 0:
				return None
			str_def = str_def[str_def.find("=") + 1 :].strip()
			arg.default_value = str_def[arg.varname.find("=") + 1 :].strip()
		if len(arg.varname) == 0:
			arg.varname = None
			return arg
		if arg.varname[0] == "*":
			arg.wtype.attr_type = attr_types.star
			arg.varname = arg.varname[1:]
		elif arg.varname[0] == "&":
			if arg.wtype.attr_type != attr_types.default:
				return None
			if arg.varname[1] == "&":
				arg.wtype.attr_type = attr_types.ampamp
				arg.varname = arg.varname[2:]
			else:
				arg.wtype.attr_type = attr_types.amp
				arg.varname = arg.varname[1:]
		return arg

	# Generates the varname. If the attribute has no name in the header file,
	# a name is generated
	def gen_varname(self):
		if self.varname != None:
			return self.varname
		if self.wtype.name == "void":
			return ""
		if self.pos == None:
			self.pos = Attribute.pos_counter
			Attribute.pos_counter = Attribute.pos_counter + 1
		return "gen_varname_" + str(self.pos)

	# Generates the test for the function headers with c++ types
	def gen_listitem_cpp(self, include_varname=True):
		postfix = self.gen_varname() * include_varname
		prefix = ""
		if self.is_const:
			prefix = "const "
		infix = ""
		if self.wtype.attr_type == attr_types.star:
			infix = "*"
		elif self.wtype.attr_type == attr_types.amp:
			infix = "&"
		elif self.wtype.attr_type == attr_types.ampamp:
			infix = "&&"
		if self.wtype.name in known_containers:
			return (
				prefix
				+ self.wtype.cont.gen_type_cpp()
				+ " "
				+ infix
				+ postfix
			)
		if self.wtype.name in classnames:
			return (
				prefix
				+ class_by_name(self.wtype.name).namespace
				+ "::"
				+ self.wtype.name
				+ " "
				+ infix
				+ postfix
			)
		return prefix + self.wtype.name + " " + infix + postfix

	def gen_listitem_pyarg(self):
		default = ""
		if self.default_value is not None:
			default = f" = {self.default_value}"
		return f'py::arg("{self.varname}"){default}'

	# Generates the listitem withtout the varname, so the signature can be
	# compared
	def gen_listitem_hash(self):
		prefix = ""
		if self.is_const:
			prefix = "const "
		if self.wtype.name in classnames:
			return prefix + self.wtype.name + "* "
		if self.wtype.name in known_containers:
			return self.wtype.cont.gen_identifier()
		return prefix + self.wtype.name


class WClass:
	name = None
	namespace = None
	link_type = None
	base_class = None
	id_ = None
	string_id = None
	hash_id = None
	needs_clone = False
	found_funs = []
	found_vars = []
	found_constrs = []

	def __init__(
		self,
		name,
		link_type,
		*,
		id_=None,
		string_id=None,
		hash_id=None,
		needs_clone=False,
	):
		self.name = name
		self.namespace = None
		self.base_class = None
		self.link_type = link_type
		self.id_ = id_
		self.string_id = string_id
		self.hash_id = hash_id
		self.needs_clone = needs_clone
		self.found_funs = []
		self.found_vars = []
		self.found_constrs = []

	@autostring
	def gen_boost_py(self, *, stream):
		name_qualified = f"{self.namespace}::{self.name}"
		tpl_args = [name_qualified]
		if self.link_type in [link_types.pointer, link_types.global_list]:
			tpl_args.append(f"std::unique_ptr<{name_qualified}, py::nodelete>")
		stream.write(f'\t\tpy::class_<{", ".join(tpl_args)}>(m, "{self.name}")\n')
		for con in self.found_constrs:
			# HACK: skip move constructors
			if "&&" in con.orig_text:
				continue
			con.gen_boost_py(stream=stream)
		for fun in sorted(self.found_funs, key=lambda f: (f.is_operator, f.name)):
			fun.gen_boost_py(stream=stream)
		if self.string_id:
			stream.write(
				f'\t\t\t.def("__str__", [](const {name_qualified} &self){{ return self.{self.string_id}; }})\n'
			)
		if self.hash_id:
			hash_member = f".{self.hash_id}" if self.hash_id != "" else ""
			stream.write(
				f'\t\t\t.def("__hash__", [](const {name_qualified} &self){{ return run_hash(self{hash_member}); }})\n'
			)
		for var in self.found_vars:
			var.gen_boost_py(stream=stream)
		stream.write("\t\t;\n")

	def fully_qualified_name(self) -> str:
		return f"{self.namespace}::{self.name}"

	def __repr__(self):
		return f"{self.__class__.__qualname__}({repr(self.__dict__)})"


# CONFIGURE HEADER-FILES TO BE PARSED AND CLASSES EXPECTED IN THEM HERE

sources = [
	Source(
		"kernel/celltypes",
		[
			WClass("CellType", link_types.ref_copy, hash_id="type", needs_clone=True),
			WClass("CellTypes", link_types.ref_copy, needs_clone=True),
		],
	),
	Source(
		"kernel/consteval", [WClass("ConstEval", link_types.ref_copy, needs_clone=True)]
	),
	Source("kernel/log", []),
	Source(
		"kernel/register",
		[
			# WClass("Pass", link_types.derive, needs_clone=True), # Manual mapping because of virtual method
		],
	),
	Source(
		"kernel/rtlil",
		[
			WClass("IdString", link_types.ref_copy, string_id="str()", hash_id="str()"),
			WClass("Const", link_types.ref_copy, string_id="as_string()"),
			WClass("AttrObject", link_types.ref_copy),
			WClass("NamedObject", link_types.ref_copy),
			WClass("Selection", link_types.ref_copy),
			#WClass("Monitor", link_types.derive), # Moved to tpl for virtual methods
			WClass("CaseRule", link_types.ref_copy, needs_clone=True),
			WClass("SwitchRule", link_types.ref_copy, needs_clone=True),
			WClass("SyncRule", link_types.ref_copy, needs_clone=True),
			WClass(
				"Process", link_types.pointer, string_id="name.c_str()", hash_id="name"
			),
			WClass("SigChunk", link_types.ref_copy),
			WClass("SigBit", link_types.ref_copy, hash_id=""),
			WClass("SigSpec", link_types.ref_copy, hash_id=""),
			WClass(
				"Cell",
				link_types.global_list,
				id_=Attribute(WType("unsigned int"), "hashidx_"),
				string_id="name.c_str()",
				hash_id="",
			),
			WClass(
				"Wire",
				link_types.global_list,
				id_=Attribute(WType("unsigned int"), "hashidx_"),
				string_id="name.c_str()",
				hash_id="",
			),
			WClass(
				"Memory",
				link_types.global_list,
				id_=Attribute(WType("unsigned int"), "hashidx_"),
				string_id="name.c_str()",
				hash_id="",
			),
			WClass(
				"Module",
				link_types.global_list,
				id_=Attribute(WType("unsigned int"), "hashidx_"),
				string_id="name.c_str()",
				hash_id="",
			),
			WClass(
				"Design",
				link_types.ref_copy,
				id_=Attribute(WType("unsigned int"), "hashidx_"),
				string_id="hashidx_",
				hash_id="",
			),
		],
	),
	# Source("kernel/satgen",[
	# 	]
	# 	),
	# Source("libs/ezsat/ezsat",[
	# 	]
	# 	),
	# Source("libs/ezsat/ezminisat",[
	# 	]
	# 	),
	Source(
		"kernel/sigtools", [WClass("SigMap", link_types.ref_copy, needs_clone=True)]
	),
	Source("kernel/yosys", []),
	Source("kernel/cost", []),
]

blacklist_methods = [
	"YOSYS_NAMESPACE::Pass::run_register",
	"YOSYS_NAMESPACE::Module::Pow",
	"YOSYS_NAMESPACE::RTLIL::Design::selected_whole_modules",
	"YOSYS_NAMESPACE::RTLIL::AttrObject::get_blackbox_attribute"
]

enum_names = ["State", "SyncType", "ConstFlags"]

enums = []  # Do not edit
glbls = []

unowned_functions = []

classnames = []
for source in sources:
	for wclass in source.classes:
		classnames.append(wclass.name)


def class_by_name(name):
	for source in sources:
		for wclass in source.classes:
			if wclass.name == name:
				return wclass
	return None


def enum_by_name(name):
	for e in enums:
		if e.name == name:
			return e
	return None


def find_closing(text, open_tok, close_tok):
	if text.find(open_tok) == -1 or text.find(close_tok) <= text.find(open_tok):
		return text.find(close_tok)
	return (
		text.find(close_tok)
		+ find_closing(text[text.find(close_tok) + 1 :], open_tok, close_tok)
		+ 1
	)


def unpretty_string(s):
	s = s.strip()
	while s.find("  ") != -1:
		s = s.replace("  ", " ")
	while s.find("\t") != -1:
		s = s.replace("\t", " ")
	s = s.replace(" (", "(")
	return s


class WEnum:
	name = None
	namespace = None
	values = []

	def from_string(str_def, namespace, line_number):
		str_def = str_def.strip()
		if not str.startswith(str_def, "enum "):
			return None
		if str_def.count(";") != 1:
			return None
		str_def = str_def[5:]
		enum = WEnum()
		split = str_def.split(":")
		if len(split) != 2:
			return None
		enum.name = split[0].strip()
		if enum.name not in enum_names:
			return None
		str_def = split[1]
		if str_def.count("{") != str_def.count("}") != 1:
			return None
		if (
			len(str_def) < str_def.find("}") + 2
			or str_def[str_def.find("}") + 1] != ";"
		):
			return None
		str_def = str_def.split("{")[-1].split("}")[0]
		enum.values = []
		for val in str_def.split(","):
			enum.values.append(val.strip().split("=")[0].strip())
		enum.namespace = namespace
		return enum

	@autostring
	def gen_boost_py(self, *, stream):
		stream.write(
			f'\t\tpy::native_enum<{self.namespace}::{self.name}>(m, "{self.name}", "enum.Enum")\n'
		)
		for value in self.values:
			stream.write(f'\t\t\t.value("{value}", {self.namespace}::{value})\n')
		stream.write("\t\t\t.finalize();\n")

	def __str__(self):
		ret = "Enum " + self.namespace + "::" + self.name + "(\n"
		for val in self.values:
			ret = ret + "\t" + val + "\n"
		return ret + ")"


class WConstructor:
	orig_text = None
	args = []
	containing_file = None
	member_of = None
	duplicate = False
	protected = False

	def __init__(self, containing_file, class_):
		self.orig_text = "Auto generated default constructor"
		self.args = []
		self.containing_file = containing_file
		self.member_of = class_
		self.protected = False

	def from_string(str_def, containing_file, class_, line_number, protected=False):
		if class_ == None:
			return None
		if str_def.count("delete;") > 0:
			return None
		con = WConstructor(containing_file, class_)
		con.orig_text = str_def
		con.args = []
		con.duplicate = False
		con.protected = protected
		if str.startswith(str_def, "inline "):
			str_def = str_def[7:]
		if not str.startswith(str_def, class_.name + "("):
			return None
		str_def = str_def[len(class_.name) + 1 :]
		found = find_closing(str_def, "(", ")")
		if found == -1:
			return None
		str_def = str_def[0:found].strip()
		if len(str_def) == 0:
			return con
		args = split_list(str_def, ",")
		for i, arg in enumerate(args):
			parsed = Attribute.from_string(arg.strip(), containing_file, line_number)
			if parsed == None:
				return None
			# Only allow std::source_location as defaulted last argument, and
			# don't append so it takes default value
			if parsed.wtype.name in ["std::source_location", "source_location"]:
				if parsed.default_value is None or i != len(args) - 1:
					debug(
						"std::source_location not defaulted last arg of "
						+ class_.name
						+ " is unsupported",
						2,
					)
					return None
				continue
			con.args.append(parsed)
		return con

	def gen_decl_hash_py(self):
		text = self.member_of.name + "("
		for arg in self.args:
			text += arg.gen_listitem_hash() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += ");"
		return text

	def overload_params(self):
		return ", ".join([a.gen_listitem_cpp(include_varname=False) for a in self.args])

	@autostring
	def gen_boost_py(self, *, stream):
		if self.duplicate or self.protected:
			return
		stream.write(f"\t\t\t.def(py::init<{self.overload_params()}>())\n")


class WFunction:
	orig_text = None
	is_static = False
	is_inline = False
	is_virtual = False
	is_const = False
	ret_attr_type = attr_types.default
	is_operator = False
	ret_type = None
	name = None
	alias = None
	args = []
	containing_file = None
	member_of = None
	duplicate = False
	namespace = ""

	def from_string(str_def, containing_file, class_, line_number, namespace):
		if str_def.count("delete;") > 0:
			return None
		func = WFunction()
		func.is_static = False
		func.is_inline = False
		func.is_virtual = False
		func.is_const = False
		func.ret_attr_type = attr_types.default
		func.is_operator = False
		func.member_of = None
		func.orig_text = str_def
		func.args = []
		func.containing_file = containing_file
		func.member_of = class_
		func.duplicate = False
		func.namespace = namespace
		str_def = str_def.replace("operator ", "operator")

		# remove attributes from the start
		if str.startswith(str_def, "[[") and "]]" in str_def:
			str_def = str_def[str_def.find("]]") + 2 :]

		if str.startswith(str_def, "static "):
			func.is_static = True
			str_def = str_def[7:]
		else:
			func.is_static = False
		if str.startswith(str_def, "inline "):
			func.is_inline = True
			str_def = str_def[7:]
		else:
			func.is_inline = False
		if str.startswith(str_def, "virtual "):
			func.is_virtual = True
			str_def = str_def[8:]
		else:
			func.is_virtual = False

		if str_def.count(" ") == 0:
			return None

		parts = split_list(str_def.strip(), " ")

		prefix = ""
		i = 0
		for part in parts:
			if part in ["unsigned", "long", "short", "const"]:
				prefix += part + " "
				i += 1
			else:
				break
		parts = parts[i:]

		if len(parts) <= 1:
			return None

		func.ret_type = WType.from_string(
			prefix + parts[0], containing_file, line_number
		)

		if func.ret_type == None:
			return None

		str_def = parts[1]
		for part in parts[2:]:
			str_def = str_def + " " + part

		found = str_def.find("(")
		if found == -1 or (str_def.find(" ") != -1 and found > str_def.find(" ")):
			return None
		func.name = str_def[:found]
		str_def = str_def[found:]
		if func.name.find("operator") != -1 and str.startswith(str_def, "()("):
			func.name += "()"
			str_def = str_def[2:]
		str_def = str_def[1:]
		if func.name.find("operator") != -1:
			func.is_operator = True
		if func.name.find("*") == 0:
			func.name = func.name.replace("*", "")
			func.ret_type.attr_type = attr_types.star
		if func.name.find("&&") == 0:
			func.name = func.name.replace("&&", "")
			func.ret_type.attr_type = attr_types.ampamp
		if func.name.find("&") == 0:
			func.name = func.name.replace("&", "")
			func.ret_type.attr_type = attr_types.amp

		found = find_closing(str_def, "(", ")")
		if found == -1:
			return None

		post_qualifiers = str_def[found + 1 :].lstrip()
		if post_qualifiers.startswith("const"):
			func.is_const = True

		str_def = str_def[0:found]
		if func.name in blacklist_methods:
			return None
		if func.namespace != None and func.namespace != "":
			if (func.namespace + "::" + func.name) in blacklist_methods:
				return None
			if func.member_of != None:
				if (
					func.namespace + "::" + func.member_of.name + "::" + func.name
				) in blacklist_methods:
					return None
		if (
			func.is_operator
			and func.name.replace(" ", "").replace("operator", "").split("::")[-1]
			not in wrappable_operators
		):
			return None

		testname = func.name
		if func.is_operator:
			testname = testname[: testname.find("operator")]
		if (
			testname.count(")") != 0
			or testname.count("(") != 0
			or testname.count("~") != 0
			or testname.count(";") != 0
			or testname.count(">") != 0
			or testname.count("<") != 0
			or testname.count("throw") != 0
		):
			return None

		func.alias = func.name
		if func.name in keyword_aliases:
			func.alias = keyword_aliases[func.name]
		str_def = str_def[:found].strip()
		if len(str_def) == 0:
			return func
		args = split_list(str_def, ",")
		for i, arg in enumerate(args):
			if arg.strip() == "...":
				continue
			parsed = Attribute.from_string(arg.strip(), containing_file, line_number)
			if parsed == None:
				return None
			# Only allow std::source_location as defaulted last argument, and
			# don't append so it takes default value
			if parsed.wtype.name in ["std::source_location", "source_location"]:
				if parsed.default_value is None or i != len(args) - 1:
					debug(
						"std::source_location not defaulted last arg of "
						+ func.name
						+ " is unsupported",
						2,
					)
					return None
				continue
			func.args.append(parsed)
		# handle (void) parameter declarations
		if len(func.args) == 1 and func.args[0].wtype.name == "void":
			func.args = []
		return func

	@property
	def mangled_name(self):
		mangled_typename = (
			lambda code: code.replace("::", "_")
			.replace("<", "_")
			.replace(">", "_")
			.replace(" ", "")
			.replace("*", "")
			.replace(",", "")
		)

		return self.name + "".join(
			f"__{mangled_typename(arg.wtype.gen_text_cpp())}" for arg in self.args
		)

	def gen_alias(self):
		self.alias = self.mangled_name

	def gen_post_qualifiers(self, derived=False):
		if (
			self.member_of != None
			and self.member_of.link_type == link_types.derive
			and self.is_virtual
			and derived
		):
			# we drop the qualifiers when deriving callbacks to be implemented in Python
			return ""
		return " const" if self.is_const else ""

	def gen_decl_hash_py(self):
		text = self.ret_type.gen_text() + " " + self.alias + "("
		for arg in self.args:
			text += arg.gen_listitem_hash() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += ");"
		return text

	def overload_params(self):
		return ", ".join([a.gen_listitem_cpp(False) for a in self.args])

	def py_args(self):
		return ", ".join([a.gen_listitem_pyarg() for a in self.args])

	def wrapper_params(self):
		return ", ".join([a.gen_listitem_cpp() for a in self.args])

	def wrapper_args(self):
		varnames = []
		for a in self.args:
			if a.varname == "format":
				# HACK: handle format strings (by ignoring the format part)
				varnames.extend(['"%s"', "format"])
			else:
				varnames.append(a.varname)
		return ", ".join(varnames)

	@autostring
	def gen_boost_py(self, *, stream):
		if self.duplicate:
			return

		fully_qualify = False
		if self.member_of is not None and (
			(self.member_of.name == "IdString" and self.name == "in")
			or (self.member_of.name == "Design" and self.name == "selection")
		):
			fully_qualify = True

		# HACK: skip methods with inline-related nonsense
		if self.alias in [
			"log_id",
			"log_dump_val_worker",
			"log_dump_args_worker",
			"GetSize",
		]:
			return

		prefix = "\t\tm"
		ns = self.namespace
		if self.member_of:
			prefix = "\t\t\t"
			ns = self.member_of.fully_qualified_name()

		stream.write(f"{prefix}.def")
		if self.member_of and self.is_static:
			stream.write("_static")
		stream.write("(")

		if self.is_operator:
			stream.write(f"py::self {self.name[len('operator'):]} py::self")
		else:
			stream.write(f'"{self.alias}", ')
			# HACK: wrap variadics by only allowing a string
			if "..." in self.orig_text:
				stream.write(
					f"[]({self.wrapper_params()}) {{ {self.namespace}::{self.name}({self.wrapper_args()}); }}"
				)
			else:

				# HACK: Some of these needs special handling, i.e., a FULL
				# overload disambiguation. Not sure why. Something to do with
				# inlines and overloads.
				#
				# In theory, this disambiguation should work for everything but
				# WType doesn't properly retain const return types yet.
				if fully_qualify:
					stream.write(
						f"static_cast < {self.ret_type.gen_text_cpp()} ({ns}::*)({self.overload_params()}) {self.gen_post_qualifiers()} >("
					)
				elif not len(self.args) == 0:
					stream.write(f"py::overload_cast<{self.overload_params()}>(")
				stream.write(f"&{ns}::{self.name}")
				if fully_qualify:
					stream.write(")")
				elif not len(self.args) == 0:
					if self.is_const:
						stream.write(f", py::const_")
					stream.write(")")
		py_args = self.py_args()
		if len(py_args):
			stream.write(", ")
			stream.write(py_args)
		stream.write(")\n" if self.member_of is not None else ");\n")

	def __repr__(self):
		return f"{self.__class__.__qualname__}({repr(self.__dict__)})"


class WMember:
	opaque_containers: ClassVar[dict] = dict()
	orig_text = None
	wtype = attr_types.default
	name = None
	containing_file = None
	member_of = None
	namespace = ""
	is_const = False

	def from_string(str_def, containing_file, class_, line_number, namespace):
		member = WMember()
		member.orig_text = str_def
		member.wtype = None
		member.name = ""
		member.containing_file = containing_file
		member.member_of = class_
		member.namespace = namespace
		member.is_const = False

		if str.startswith(str_def, "const "):
			member.is_const = True
			str_def = str_def[6:]

		if str_def.count(" ") == 0:
			return None

		parts = split_list(str_def.strip(), " ")

		prefix = ""
		i = 0
		for part in parts:
			if part in ["unsigned", "long", "short"]:
				prefix += part + " "
				i += 1
			else:
				break
		parts = parts[i:]

		if len(parts) <= 1:
			return None

		member.wtype = WType.from_string(
			prefix + parts[0], containing_file, line_number
		)

		if member.wtype == None:
			return None

		str_def = parts[1]
		for part in parts[2:]:
			str_def = str_def + " " + part

		if (
			str_def.find("(") != -1
			or str_def.find(")") != -1
			or str_def.find("{") != -1
			or str_def.find("}") != -1
		):
			return None

		found = str_def.find(";")
		if found == -1:
			return None

		found_eq = str_def.find("=")
		if found_eq != -1:
			found = found_eq

		member.name = str_def[:found]
		str_def = str_def[found + 1 :]
		if member.name.find("*") == 0:
			member.name = member.name.replace("*", "")
			member.wtype.attr_type = attr_types.star
		if member.name.find("&&") == 0:
			member.name = member.name.replace("&&", "")
			member.wtype.attr_type = attr_types.ampamp
		if member.name.find("&") == 0:
			member.name = member.name.replace("&", "")
			member.wtype.attr_type = attr_types.amp

		if len(str_def.strip()) != 0:
			return None

		if len(member.name.split(",")) > 1:
			member_list = []
			for name in member.name.split(","):
				name = name.strip()
				member_list.append(WMember())
				member_list[-1].orig_text = member.orig_text
				member_list[-1].wtype = member.wtype
				member_list[-1].name = name
				member_list[-1].containing_file = member.containing_file
				member_list[-1].member_of = member.member_of
				member_list[-1].namespace = member.namespace
				member_list[-1].is_const = member.is_const
			return member_list

		if member.wtype.cont:
			WMember.opaque_containers[member.wtype.gen_identifier()] = member.wtype

		return member

	@autostring
	def gen_boost_py(self, *, stream):
		if False and self.wtype.attr_type == attr_types.default:
			property_type = self.wtype.gen_text_cpp()
			stream.write(f'\t\t\t.def_property("{self.name}",\n')
			stream.write(f'\t\t\t\t[]({self.member_of.fully_qualified_name()} &o) -> {property_type}&  {{ return o.{self.name}; }},\n')
			stream.write(f'\t\t\t\t[]({self.member_of.fully_qualified_name()} &o, {property_type} const &p) {{ o.{self.name} = p; }},\n')
			stream.write(f'\t\t\t\tpy::return_value_policy::reference_internal\n')
			stream.write(f'\t\t\t)\n')
		else:
			meth = "def_readonly" if self.is_const else "def_readwrite"
			stream.write(
				f'\t\t\t.{meth}("{self.name}", &{self.member_of.fully_qualified_name()}::{self.name})\n'
			)

	def __repr__(self):
		return f"{self.__class__.__qualname__}({repr(self.__dict__)})"


class WGlobal:
	orig_text = None
	wtype = attr_types.default
	name = None
	containing_file = None
	namespace = ""
	is_const = False

	def from_string(str_def, containing_file, line_number, namespace):
		glbl = WGlobal()
		glbl.orig_text = str_def
		glbl.wtype = None
		glbl.name = ""
		glbl.containing_file = containing_file
		glbl.namespace = namespace
		glbl.is_const = False

		if not str.startswith(str_def, "extern"):
			return None
		str_def = str_def[7:]

		if str.startswith(str_def, "const "):
			glbl.is_const = True
			str_def = str_def[6:]

		if str_def.count(" ") == 0:
			return None

		parts = split_list(str_def.strip(), " ")

		prefix = ""
		i = 0
		for part in parts:
			if part in ["unsigned", "long", "short"]:
				prefix += part + " "
				i += 1
			else:
				break
		parts = parts[i:]

		if len(parts) <= 1:
			return None

		glbl.wtype = WType.from_string(prefix + parts[0], containing_file, line_number)

		if glbl.wtype == None:
			return None

		str_def = parts[1]
		for part in parts[2:]:
			str_def = str_def + " " + part

		if (
			str_def.find("(") != -1
			or str_def.find(")") != -1
			or str_def.find("{") != -1
			or str_def.find("}") != -1
		):
			return None

		found = str_def.find(";")
		if found == -1:
			return None

		found_eq = str_def.find("=")
		if found_eq != -1:
			found = found_eq

		glbl.name = str_def[:found]
		str_def = str_def[found + 1 :]
		if glbl.name.find("*") == 0:
			glbl.name = glbl.name.replace("*", "")
			glbl.wtype.attr_type = attr_types.star
		if glbl.name.find("&&") == 0:
			glbl.name = glbl.name.replace("&&", "")
			glbl.wtype.attr_type = attr_types.ampamp
		if glbl.name.find("&") == 0:
			glbl.name = glbl.name.replace("&", "")
			glbl.wtype.attr_type = attr_types.amp

		if len(str_def.strip()) != 0:
			return None

		if len(glbl.name.split(",")) > 1:
			glbl_list = []
			for name in glbl.name.split(","):
				name = name.strip()
				glbl_list.append(WGlobal())
				glbl_list[-1].orig_text = glbl.orig_text
				glbl_list[-1].wtype = glbl.wtype
				glbl_list[-1].name = name
				glbl_list[-1].containing_file = glbl.containing_file
				glbl_list[-1].namespace = glbl.namespace
				glbl_list[-1].is_const = glbl.is_const
			return glbl_list

		return glbl

	@autostring
	def gen_boost_py(self, *, stream):
		args = [
			f'"{self.name}"',
		]
		meth = "def_readonly_static"
		if not self.is_const:
			meth = "def_readwrite_static"
		args.append(f"&{self.namespace}::{self.name}")
		stream.write(f'\t\t\t.{meth}({", ".join(args)})\n')


def concat_namespace(tuple_list):
	if len(tuple_list) == 0:
		return ""
	ret = ""
	for namespace in tuple_list:
		ret += "::" + namespace[0]
	return ret[2:]


def calc_ident(text):
	if len(text) == 0 or text[0] != " ":
		return 0
	return calc_ident(text[1:]) + 1


def assure_length(text, length, left=False):
	if len(text) > length:
		return text[:length]
	if left:
		return text + " " * (length - len(text))
	return " " * (length - len(text)) + text


def nesting_delta(s):
	return s.count("{") - s.count("}")


def parse_header(source):
	debug("Parsing " + source.name + ".pyh", 1)
	source_file = open(source.name + ".pyh", "r")

	source_text = []
	in_line = source_file.readline()

	namespaces = []

	while in_line:
		if len(in_line) > 1:
			source_text.append(
				in_line.replace("char *", "char_p ").replace("char* ", "char_p ")
			)
		in_line = source_file.readline()

	i = 0

	namespaces = []
	classes = []
	private_segment = False

	while i < len(source_text):
		line = (
			source_text[i]
			.replace(
				"YOSYS_NAMESPACE_BEGIN",
				"                    namespace YOSYS_NAMESPACE{",
			)
			.replace("YOSYS_NAMESPACE_END", "                    }")
		)
		ugly_line = unpretty_string(line)
		debug(f"READ:>> {line}", 2)

		# for anonymous unions, ignore union enclosure by skipping start line and replacing end line with new line
		if "union {" in line:
			j = i + 1
			while j < len(source_text):
				union_line = source_text[j]
				if "};" in union_line:
					source_text[j] = "\n"
					break
				j += 1
			if j != len(source_text):
				i += 1
				continue

		if str.startswith(
			ugly_line, "namespace "
		):  # and ugly_line.find("std") == -1 and ugly_line.find("__") == -1:
			namespace_name = ugly_line[10:].replace("{", "").strip()
			namespaces.append((namespace_name, ugly_line.count("{")))
			debug("-----NAMESPACE " + concat_namespace(namespaces) + "-----", 3)
			i += 1
			continue

		if len(namespaces) != 0:
			namespaces[-1] = (
				namespaces[-1][0],
				namespaces[-1][1] + nesting_delta(ugly_line),
			)
			if namespaces[-1][1] == 0:
				debug("-----END NAMESPACE " + concat_namespace(namespaces) + "-----", 3)
				namespaces.pop()
				i += 1
				continue

		if (
			str.startswith(ugly_line, "struct ") or str.startswith(ugly_line, "class")
		) and ugly_line.count(";") == 0:
			# Opening a record declaration which isn't a forward declaration
			struct_name = ugly_line.split(" ")[1].split("::")[-1]
			impl_namespaces = ugly_line.split(" ")[1].split("::")[:-1]
			complete_namespace = concat_namespace(namespaces)
			for namespace in impl_namespaces:
				complete_namespace += "::" + namespace
			debug("\tFound " + struct_name + " in " + complete_namespace, 2)

			base_class_name = None
			if len(ugly_line.split(" : ")) > 1:  # class is derived
				deriv_str = ugly_line.split(" : ")[1]
				if len(deriv_str.split("::")) > 1:  # namespace of base class is given
					base_class_name = deriv_str.split("::", 1)[1]
				else:
					base_class_name = deriv_str.split(" ")[0]
				debug("\t  " + struct_name + " is derived from " + base_class_name, 2)
			base_class = class_by_name(base_class_name)

			c = (class_by_name(struct_name), ugly_line.count("{"))  # calc_ident(line))
			debug(f"switch to {struct_name} in namespace {namespaces}", 2)
			if struct_name in classnames:
				c[0].namespace = complete_namespace
				c[0].base_class = base_class
			classes.append(c)
			i += 1
			continue

		if len(classes):
			c = (classes[-1][0], classes[-1][1] + nesting_delta(ugly_line))
			classes[-1] = c
			if c[1] == 0:
				if c[0] == None:
					debug("\tExiting unknown class", 3)
				else:
					debug("\tExiting class " + c[0].name, 3)
				classes.pop()
				private_segment = False
				i += 1
				continue

		class_ = classes[-1] if classes else None

		if class_ != None and (
			line.find("private:") != -1 or line.find("protected:") != -1
		):
			private_segment = True
			i += 1
			continue
		if class_ != None and line.find("public:") != -1:
			private_segment = False
			i += 1
			continue

		candidate = None

		if private_segment and class_ != None and class_[0] != None:
			candidate = WConstructor.from_string(
				ugly_line, source.name, class_[0], i, True
			)
			if candidate != None:
				debug(
					'\t\tFound constructor of class "'
					+ class_[0].name
					+ '" in namespace '
					+ concat_namespace(namespaces),
					2,
				)
				class_[0].found_constrs.append(candidate)
				i += 1
				continue

		if not private_segment and (class_ == None or class_[0] != None):
			if class_ != None:
				candidate = WFunction.from_string(
					ugly_line, source.name, class_[0], i, concat_namespace(namespaces)
				)
			else:
				candidate = WFunction.from_string(
					ugly_line, source.name, None, i, concat_namespace(namespaces)
				)
			if candidate != None and candidate.name.find("::") == -1:
				if class_ == None:
					debug(
						'\tFound unowned function "'
						+ candidate.name
						+ '" in namespace '
						+ concat_namespace(namespaces),
						2,
					)
					unowned_functions.append(candidate)
				else:
					debug(
						'\t\tFound function "'
						+ candidate.name
						+ '" of class "'
						+ class_[0].name
						+ '" in namespace '
						+ concat_namespace(namespaces),
						2,
					)
					class_[0].found_funs.append(candidate)
			else:
				candidate = WEnum.from_string(
					ugly_line, concat_namespace(namespaces), i
				)
				if candidate != None:
					enums.append(candidate)
					debug(
						'\tFound enum "'
						+ candidate.name
						+ '" in namespace '
						+ concat_namespace(namespaces),
						2,
					)
				elif class_ != None and class_[1] == 1:
					candidate = WConstructor.from_string(
						ugly_line, source.name, class_[0], i
					)
					if candidate != None:
						debug(
							'\t\tFound constructor of class "'
							+ class_[0].name
							+ '" in namespace '
							+ concat_namespace(namespaces),
							2,
						)
						class_[0].found_constrs.append(candidate)
					else:
						candidate = WMember.from_string(
							ugly_line,
							source.name,
							class_[0],
							i,
							concat_namespace(namespaces),
						)
						if candidate != None:
							if type(candidate) == list:
								for c in candidate:
									debug(
										'\t\tFound member "'
										+ c.name
										+ '" of class "'
										+ class_[0].name
										+ '" of type "'
										+ c.wtype.name
										+ '"',
										2,
									)
								class_[0].found_vars.extend(candidate)
							else:
								debug(
									'\t\tFound member "'
									+ candidate.name
									+ '" of class "'
									+ class_[0].name
									+ '" of type "'
									+ candidate.wtype.name
									+ '"',
									2,
								)
								class_[0].found_vars.append(candidate)
				if candidate == None and class_ == None:
					candidate = WGlobal.from_string(
						ugly_line, source.name, i, concat_namespace(namespaces)
					)
					if candidate != None:
						if type(candidate) == list:
							for c in candidate:
								glbls.append(c)
								debug(
									'\tFound global "'
									+ c.name
									+ '" in namespace '
									+ concat_namespace(namespaces),
									2,
								)
						else:
							glbls.append(candidate)
							debug(
								'\tFound global "'
								+ candidate.name
								+ '" in namespace '
								+ concat_namespace(namespaces),
								2,
							)

			j = i
			line = unpretty_string(line)
			while (
				candidate == None
				and j + 1 < len(source_text)
				and line.count(";") <= 1
				and line.count("(") >= line.count(")")
			):
				j += 1
				line = line + "\n" + unpretty_string(source_text[j])
				if class_ != None:
					candidate = WFunction.from_string(
						ugly_line,
						source.name,
						class_[0],
						i,
						concat_namespace(namespaces),
					)
				else:
					candidate = WFunction.from_string(
						ugly_line, source.name, None, i, concat_namespace(namespaces)
					)
				if candidate != None and candidate.name.find("::") == -1:
					if class_ == None:
						debug(
							'\tFound unowned function "'
							+ candidate.name
							+ '" in namespace '
							+ concat_namespace(namespaces),
							2,
						)
						unowned_functions.append(candidate)
					else:
						debug(
							'\t\tFound function "'
							+ candidate.name
							+ '" of class "'
							+ class_[0].name
							+ '" in namespace '
							+ concat_namespace(namespaces),
							2,
						)
						class_[0].found_funs.append(candidate)
					continue
				candidate = WEnum.from_string(line, concat_namespace(namespaces), i)
				if candidate != None:
					enums.append(candidate)
					debug(
						'\tFound enum "'
						+ candidate.name
						+ '" in namespace '
						+ concat_namespace(namespaces),
						2,
					)
					continue
				if class_ != None:
					candidate = WConstructor.from_string(
						line, source.name, class_[0], i
					)
					if candidate != None:
						debug(
							'\t\tFound constructor of class "'
							+ class_[0].name
							+ '" in namespace '
							+ concat_namespace(namespaces),
							2,
						)
						class_[0].found_constrs.append(candidate)
						continue
				if class_ == None:
					candidate = WGlobal.from_string(
						line, source.name, i, concat_namespace(namespaces)
					)
					if candidate != None:
						if type(candidate) == list:
							for c in candidate:
								glbls.append(c)
								debug(
									'\tFound global "'
									+ c.name
									+ '" in namespace '
									+ concat_namespace(namespaces),
									2,
								)
						else:
							glbls.append(candidate)
							debug(
								'\tFound global "'
								+ candidate.name
								+ '" in namespace '
								+ concat_namespace(namespaces),
								2,
							)
						continue
		if candidate != None:
			while i < j:
				i += 1
				line = (
					source_text[i]
					.replace(
						"YOSYS_NAMESPACE_BEGIN",
						"                    namespace YOSYS_NAMESPACE{",
					)
					.replace("YOSYS_NAMESPACE_END", "                    }")
				)
				ugly_line = unpretty_string(line)
				if len(namespaces) != 0:
					namespaces[-1] = (
						namespaces[-1][0],
						namespaces[-1][1] + nesting_delta(ugly_line),
					)
					if namespaces[-1][1] == 0:
						debug(
							"-----END NAMESPACE "
							+ concat_namespace(namespaces)
							+ "-----",
							3,
						)
						namespaces.pop()
				if len(classes):
					c = (classes[-1][0], classes[-1][1] + nesting_delta(ugly_line))
					classes[-1] = c
					if c[1] == 0:
						if c[0] == None:
							debug("\tExiting unknown class", 3)
						else:
							debug("\tExiting class " + c[0].name, 3)
						classes.pop()
						private_segment = False
			i += 1
		else:
			i += 1


def debug(message, level):
	if level <= debug.debug_level:
		print(message)


def expand_functions():
	global unowned_functions
	new_funs = []
	for fun in unowned_functions:
		new_funs.append(fun)
	unowned_functions = new_funs
	for source in sources:
		for class_ in source.classes:
			new_funs = []
			for fun in class_.found_funs:
				new_funs.append(fun)
			class_.found_funs = new_funs


def inherit_members():
	for source in sources:
		for class_ in source.classes:
			if class_.base_class:
				base_funs = copy.deepcopy(class_.base_class.found_funs)
				for fun in base_funs:
					fun.member_of = class_
					fun.namespace = class_.namespace
				base_vars = copy.deepcopy(class_.base_class.found_vars)
				for var in base_vars:
					var.member_of = class_
					var.namespace = class_.namespace
				class_.found_funs.extend(base_funs)
				class_.found_vars.extend(base_vars)


def clean_duplicates():
	for source in sources:
		for class_ in source.classes:
			known_decls = {}
			for fun in class_.found_funs:
				if fun.gen_decl_hash_py() in known_decls:
					debug("Multiple declarations of " + fun.gen_decl_hash_py(), 3)

					other = known_decls[fun.gen_decl_hash_py()]
					if fun.mangled_name == other.mangled_name:
						fun.duplicate = True
						debug('Disabled "' + fun.gen_decl_hash_py() + '"', 3)
						continue

					other.gen_alias()
					fun.gen_alias()
				else:
					known_decls[fun.gen_decl_hash_py()] = fun
			known_decls = []
			for con in class_.found_constrs:
				if con.gen_decl_hash_py() in known_decls:
					debug("Multiple declarations of " + con.gen_decl_hash_py(), 3)
					con.duplicate = True
				else:
					known_decls.append(con.gen_decl_hash_py())
	known_decls = []
	for fun in unowned_functions:
		if fun.gen_decl_hash_py() in known_decls:
			debug("Multiple declarations of " + fun.gen_decl_hash_py(), 3)
			fun.duplicate = True
		else:
			known_decls.append(fun.gen_decl_hash_py())


def gen_wrappers(filename, debug_level_=0):
	filename = Path(filename)

	debug.debug_level = debug_level_
	for source in sources:
		parse_header(source)

	expand_functions()
	inherit_members()
	clean_duplicates()

	import shutil
	import math

	col = shutil.get_terminal_size((80, 20)).columns
	debug("-" * col, 1)
	debug(
		"-" * math.floor((col - 7) / 2) + "SUMMARY" + "-" * math.ceil((col - 7) / 2), 1
	)
	debug("-" * col, 1)
	for source in sources:
		for class_ in source.classes:
			debug(
				"Class "
				+ assure_length(class_.name, len(max(classnames, key=len)), True)
				+ " contains "
				+ assure_length(str(len(class_.found_vars)), 3, False)
				+ " member variables, "
				+ assure_length(str(len(class_.found_funs)), 3, False)
				+ " methods and "
				+ assure_length(str(len(class_.found_constrs)), 2, False)
				+ " constructors",
				1,
			)
			if len(class_.found_constrs) == 0:
				class_.found_constrs.append(WConstructor(source.name, class_))
	debug(str(len(unowned_functions)) + " functions are unowned", 1)
	debug(str(len(unowned_functions)) + " global variables", 1)
	for enum in enums:
		debug(
			"Enum "
			+ assure_length(enum.name, len(max(enum_names, key=len)), True)
			+ " contains "
			+ assure_length(str(len(enum.values)), 2, False)
			+ " values",
			1,
		)
	debug("-" * col, 1)

	tpl = __file_dir__ / "wrappers_tpl.cc"
	with open(tpl, encoding="utf8") as f, open(
		filename, "w", encoding="utf8"
	) as wrapper_file:
		do_line_directive = True
		for i, line in enumerate(f):
			if do_line_directive:
				wrapper_file.write(f'#line {i + 1} "{tpl}"\n')
				do_line_directive = False
			if "<!-- generated includes -->" in line:
				for source in sources:
					wrapper_file.write(f'#include "{source.name}.h"\n')
				do_line_directive = True
			elif "<!-- generated top-level code -->" in line:
				wrapper_file.write("// Opaque Container Declaration\n")
				for i, (container_identifier, container) in enumerate(WMember.opaque_containers.items()):
					wrapper_file.write(f"using {container_identifier} = {container.gen_text_cpp()};\n")
					wrapper_file.write(f'PYBIND11_MAKE_OPAQUE({container_identifier})\n')
				wrapper_file.write("\n")
				do_line_directive = True
			elif "<!-- generated YOSYS_PYTHON namespace-level code -->" in line:
				do_line_directive = True
			elif "<!-- generated pymod-level code -->" in line:
				wrapper_file.write("\t\t// Opaque Container Binding\n")
				for container in WMember.opaque_containers.values():
					container.cont.gen_boost_py(stream=wrapper_file)
				wrapper_file.write("\n")

				wrapper_file.write("\t\t// Enums\n")
				for enum in enums:
					enum.gen_boost_py(stream=wrapper_file)
				wrapper_file.write("\n")

				wrapper_file.write("\t\t// Classes\n")
				for source in sources:
					for wclass in source.classes:
						wclass.gen_boost_py(stream=wrapper_file)
				wrapper_file.write("\n")

				wrapper_file.write("\t\t// Global Functions\n")
				for fun in sorted(unowned_functions, key=lambda x: x.alias):
					fun.gen_boost_py(stream=wrapper_file)
				wrapper_file.write("\n")

				wrapper_file.write("\t\t// Global Variables\n")
				wrapper_file.write('\t\tpy::class_<YosysStatics>(m, "Yosys")\n')
				for glbl in sorted(glbls, key=lambda x: (not x.is_const, x.name)):
					glbl.gen_boost_py(stream=wrapper_file)
				wrapper_file.write("\t\t\t;\n")
				do_line_directive = True
			else:
				wrapper_file.write(line)


def print_includes():
	for source in sources:
		print(source.name + ".pyh")


if __name__ == "__main__":
	ap = argparse.ArgumentParser()
	ap.add_argument("--print-includes", action="store_true")
	ap.add_argument("--debug", default=0, type=int)
	ap.add_argument("output", nargs="?")
	ns = ap.parse_args()
	if ns.print_includes:
		print_includes()
		exit(0)
	gen_wrappers(ns.output, ns.debug)
