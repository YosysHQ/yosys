#
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
#  Author Benedikt Tutzer
#

import copy

#Map c++ operator Syntax to Python functions
wrappable_operators = {
		"<" : "__lt__",
		"==": "__eq__",
		"!=": "__ne__",
		"+" : "__add__",
		"-" : "__sub__",
		"*" : "__mul__",
		"/" : "__div__",
		"()": "__call__"
	}

#Restrict certain strings from being function names in Python
keyword_aliases = {
		"in" : "in_",
		"False" : "False_",
		"None" : "None_",
		"True" : "True_",
		"and" : "and_",
		"as" : "as_",
		"assert" : "assert_",
		"break" : "break_",
		"class" : "class_",
		"continue" : "continue_",
		"def" : "def_",
		"del" : "del_",
		"elif" : "elif_",
		"else" : "else_",
		"except" : "except_",
		"for" : "for_",
		"from" : "from_",
		"global" : "global_",
		"if" : "if_",
		"import" : "import_",
		"in" : "in_",
		"is" : "is_",
		"lambda" : "lambda_",
		"nonlocal" : "nonlocal_",
		"not" : "not_",
		"or" : "or_",
		"pass" : "pass_",
		"raise" : "raise_",
		"return" : "return_",
		"try" : "try_",
		"while" : "while_",
		"with" : "with_",
		"yield" : "yield_"
	}

#These can be used without any explicit conversion
primitive_types = ["void", "bool", "int", "double", "size_t", "std::string",
		"string", "State", "char_p"]

from enum import Enum

#Ways to link between Python- and C++ Objects
class link_types(Enum):
	global_list = 1		#Manage a global list of objects in C++, the Python
						#object contains a key to find the corresponding C++
						#object and a Pointer to the object to verify it is
						#still the same, making collisions unlikely to happen
	ref_copy = 2		#The Python object contains a copy of the C++ object.
						#The C++ object is deleted when the Python object gets
						#deleted
	pointer = 3			#The Python Object contains a pointer to it's C++
						#counterpart
	derive = 4			#The Python-Wrapper is derived from the C++ object.

class attr_types(Enum):
	star = "*"
	amp = "&"
	ampamp = "&&"
	default = ""

#For source-files
class Source:
	name = ""
	classes = []

	def __init__(self, name, classes):
		self.name = name
		self.classes = classes

#Splits a list by the given delimiter, without splitting strings inside
#pointy-brackets (< and >)
def split_list(str_def, delim):
	str_def = str_def.strip()
	if len(str_def) == 0:
		return []
	if str_def.count(delim) == 0:
		return [str_def]
	if str_def.count("<") == 0:
		return str_def.split(delim)
	if str_def.find("<") < str_def.find(" "):
		closing = find_closing(str_def[str_def.find("<")+1:], "<", ">") + str_def.find("<")
		comma = str_def[closing:].find(delim)
		if comma == -1:
			return [str_def]
		comma = closing  + comma
	else:
		comma = str_def.find(delim)
	rest = split_list(str_def[comma+1:], delim)
	ret = [str_def[:comma]]
	if rest != None and len(rest) != 0:
		ret.extend(rest)
	return ret

#Represents a Type
class WType:
	name = ""
	cont = None
	attr_type = attr_types.default

	def __init__(self, name = "", cont = None, attr_type = attr_types.default):
		self.name = name
		self.cont = cont
		self.attr_type = attr_type

	#Python type-string
	def gen_text(self):
		text = self.name
		if self.name in enum_names:
			text = enum_by_name(self.name).namespace + "::" + self.name
		if self.cont != None:
			return known_containers[self.name].typename
		return text

	#C++ type-string
	def gen_text_cpp(self):
		postfix = ""
		if self.attr_type == attr_types.star:
			postfix = "*"
		if self.name in primitive_types:
			return self.name + postfix
		if self.name in enum_names:
			return enum_by_name(self.name).namespace + "::" + self.name + postfix
		if self.name in classnames:
			return class_by_name(self.name).namespace + "::" + self.name + postfix
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
		str_def = str_def.replace("RTLIL::SigSig", "std::pair<SigSpec, SigSpec>").replace("SigSig", "std::pair<SigSpec, SigSpec>")
		t = WType()
		t.name = ""
		t.cont = None
		t.attr_type = attr_types.default
		if str_def.find("<") != -1:# and str_def.find("<") < str_def.find(" "):
			str_def = str_def.replace("const ", "")

			candidate = WContainer.from_string(str_def, containing_file, line_number)
			if candidate == None:
				return None
			t.name = str_def[:str_def.find("<")]

			if t.name.count("*") + t.name.count("&") > 1:
				return None

			if t.name.count("*") == 1 or str_def[0] == '*' or str_def[-1] == '*':
				t.attr_type = attr_types.star
				t.name = t.name.replace("*","")
			elif t.name.count("&&") == 1:
				t.attr_type = attr_types.ampamp
				t.name = t.name.replace("&&","")
			elif t.name.count("&") == 1 or str_def[0] == '&' or str_def[-1] == '&':
				t.attr_type = attr_types.amp
				t.name = t.name.replace("&","")

			t.cont = candidate
			if(t.name not in known_containers):
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
			prefix= "long " + prefix
			str_def = str_def[5:]
		while str.startswith(str_def, "short "):
			prefix = "short " + prefix
			str_def = str_def[6:]

		str_def = str_def.split("::")[-1]

		if str_def.count("*") + str_def.count("&") >= 2:
			return None

		if str_def.count("*") == 1:
			t.attr_type = attr_types.star
			str_def = str_def.replace("*","")
		elif str_def.count("&&") == 1:
			t.attr_type = attr_types.ampamp
			str_def = str_def.replace("&&","")
		elif str_def.count("&") == 1:
			t.attr_type = attr_types.amp
			str_def = str_def.replace("&","")

		if len(str_def) > 0 and str_def.split("::")[-1] not in primitive_types and str_def.split("::")[-1] not in classnames and str_def.split("::")[-1] not in enum_names:
			return None

		if str_def.count(" ") == 0:
			t.name = (prefix + str_def).replace("char_p", "char *")
			t.cont = None
			return t
		return None

#Represents a container-type
class WContainer:
	name = ""
	args = []

	def from_string(str_def, containing_file, line_number):
		if str_def == None or len(str_def) < 4:
			return None
		cont = WContainer()
		cont.name = str_def[:str_def.find("<")]
		str_def = str_def[str_def.find("<")+1:find_closing(str_def, "<", ">")]
		cont.args = []
		for arg in split_list(str_def, ","):
			candidate = WType.from_string(arg.strip(), containing_file, line_number)
			if candidate == None:
				return None
			if candidate.name == "void":
				return None
			cont.args.append(candidate)
		return cont

#Translators between Python and C++ containers
#Base Type
class Translator:
	tmp_cntr = 0
	typename = "DefaultType"
	orig_name = "DefaultCpp"

	@classmethod
	def gen_type(c, types):
		return "\nImplement a function that outputs the c++ type of this container here\n"

	@classmethod
	def translate(c, varname, types, prefix):
		return "\nImplement a function translating a python container to a c++ container here\n"

	@classmethod
	def translate_cpp(c, varname, types, prefix, ref):
		return "\nImplement a function translating a c++ container to a python container here\n"

#Translates list-types (vector, pool, set), that only differ in their name and
#the name of the insertion function
class PythonListTranslator(Translator):
	typename = "boost::python::list"
	insert_name = "Default"

	#generate the c++ type string
	@classmethod
	def gen_type(c, types):
		text = c.orig_name + "<"
		if types[0].name in primitive_types:
			text += types[0].name
		elif types[0].name in known_containers:
			text += known_containers[types[0].name].gen_type(types[0].cont.args)
		else:
			text += class_by_name(types[0].name).namespace + "::" + types[0].name
			if types[0].attr_type == attr_types.star:
				text += "*"
		text += ">"
		return text

	#Generate C++ code to translate from a boost::python::list
	@classmethod
	def translate(c, varname, types, prefix):
		text  = prefix + c.gen_type(types) + " " + varname + "___tmp;"
		cntr_name = "cntr_" + str(Translator.tmp_cntr)
		Translator.tmp_cntr = Translator.tmp_cntr + 1
		text += prefix + "for(int " + cntr_name + " = 0; " + cntr_name + " < len(" + varname + "); " + cntr_name + "++)"
		text += prefix + "{"
		tmp_name = "tmp_" + str(Translator.tmp_cntr)
		Translator.tmp_cntr = Translator.tmp_cntr + 1
		if types[0].name in known_containers:
			text += prefix + "\t" + known_containers[types[0].name].typename + " " + tmp_name + " = boost::python::extract<" + known_containers[types[0].name].typename + ">(" + varname + "[" + cntr_name + "]);"
			text += known_containers[types[0].name].translate(tmp_name, types[0].cont.args, prefix+"\t")
			tmp_name = tmp_name + "___tmp"
			text += prefix + "\t" + varname + "___tmp" + c.insert_name + "(" + tmp_name + ");"
		elif types[0].name in classnames:
			text += prefix + "\t" + types[0].name + "* " + tmp_name + " = boost::python::extract<" + types[0].name + "*>(" + varname + "[" + cntr_name + "]);"
			if types[0].attr_type == attr_types.star:
				text += prefix + "\t" + varname + "___tmp" + c.insert_name + "(" + tmp_name + "->get_cpp_obj());"
			else:
				text += prefix + "\t" + varname + "___tmp" + c.insert_name + "(*" + tmp_name + "->get_cpp_obj());"
		else:
			text += prefix + "\t" + types[0].name + " " + tmp_name + " = boost::python::extract<" + types[0].name + ">(" + varname + "[" + cntr_name + "]);"
			text += prefix + "\t" + varname + "___tmp" + c.insert_name + "(" + tmp_name + ");"
		text += prefix + "}"
		return text

	#Generate C++ code to translate to a boost::python::list
	@classmethod
	def translate_cpp(c, varname, types, prefix, ref):
		text  = prefix + c.typename + " " + varname + "___tmp;"
		tmp_name = "tmp_" + str(Translator.tmp_cntr)
		Translator.tmp_cntr = Translator.tmp_cntr + 1
		if ref:
			text += prefix + "for(auto " + tmp_name + " : *" + varname + ")"
		else:
			text += prefix + "for(auto " + tmp_name + " : " + varname + ")"
		text += prefix + "{"
		if types[0].name in classnames:
			if types[0].attr_type == attr_types.star:
				text += prefix + "\t" + varname + "___tmp.append(" + types[0].name + "::get_py_obj(" + tmp_name + "));"
			else:
				text += prefix + "\t" + varname + "___tmp.append(*" + types[0].name + "::get_py_obj(&" + tmp_name + "));"
		elif types[0].name in known_containers:
			text += known_containers[types[0].name].translate_cpp(tmp_name, types[0].cont.args, prefix + "\t", types[0].attr_type == attr_types.star)
			text += prefix + "\t" + varname + "___tmp.append(" + tmp_name + "___tmp);"
		else:
			text += prefix + "\t" + varname + "___tmp.append(" + tmp_name + ");"
		text += prefix + "}"
		return text

class IDictTranslator(PythonListTranslator):
	typename = "boost::python::list"
	orig_name = "idict"
	insert_name = ""

#Sub-type for std::set
class SetTranslator(PythonListTranslator):
	insert_name = ".insert"
	orig_name = "std::set"

#Sub-type for std::vector
class VectorTranslator(PythonListTranslator):
	insert_name = ".push_back"
	orig_name = "std::vector"

#Sub-type for pool
class PoolTranslator(PythonListTranslator):
	insert_name = ".insert"
	orig_name = "pool"

#Sub-type for ObjRange
class ObjRangeTranslator(PythonListTranslator):
	orig_name = "RTLIL::ObjRange"

#Translates dict-types (dict, std::map), that only differ in their name and
#the name of the insertion function
class PythonDictTranslator(Translator):
	typename = "boost::python::dict"
	insert_name = "Default"

	@classmethod
	def gen_type(c, types):
		text = c.orig_name + "<"
		if types[0].name in primitive_types:
			text += types[0].name
		elif types[0].name in known_containers:
			text += known_containers[types[0].name].gen_type(types[0].cont.args)
		else:
			text += class_by_name(types[0].name).namespace + "::" + types[0].name
			if types[0].attr_type == attr_types.star:
				text += "*"
		text += ", "
		if types[1].name in primitive_types:
			text += types[1].name
		elif types[1].name in known_containers:
			text += known_containers[types[1].name].gen_type(types[1].cont.args)
		else:
			text += class_by_name(types[1].name).namespace + "::" + types[1].name
			if types[1].attr_type == attr_types.star:
				text += "*"
		text += ">"
		return text

	#Generate c++ code to translate from a boost::python::dict
	@classmethod
	def translate(c, varname, types, prefix):
		text  = prefix + c.gen_type(types) + " " + varname + "___tmp;"
		text += prefix + "boost::python::list " + varname + "_keylist = " + varname + ".keys();"
		cntr_name = "cntr_" + str(Translator.tmp_cntr)
		Translator.tmp_cntr = Translator.tmp_cntr + 1
		text += prefix + "for(int " + cntr_name + " = 0; " + cntr_name + " < len(" + varname + "_keylist); " + cntr_name + "++)"
		text += prefix + "{"
		key_tmp_name = "key_tmp_" + str(Translator.tmp_cntr)
		val_tmp_name = "val_tmp_" + str(Translator.tmp_cntr)
		Translator.tmp_cntr = Translator.tmp_cntr + 1

		if types[0].name in known_containers:
			text += prefix + "\t" + known_containers[types[0].name].typename + " " + key_tmp_name + " = boost::python::extract<" + known_containers[types[0].name].typename + ">(" + varname + "_keylist[ " + cntr_name + " ]);"
			text += known_containers[types[0].name].translate(key_tmp_name, types[0].cont.args, prefix+"\t")
			key_tmp_name = key_tmp_name + "___tmp"
		elif types[0].name in classnames:
			text += prefix + "\t" + types[0].name + "* " + key_tmp_name + " = boost::python::extract<" + types[0].name + "*>(" + varname + "_keylist[ " + cntr_name + " ]);"
		else:
			text += prefix + "\t" + types[0].name + " " + key_tmp_name + " = boost::python::extract<" + types[0].name + ">(" + varname + "_keylist[ " + cntr_name + " ]);"

		if types[1].name in known_containers:
			text += prefix + "\t" + known_containers[types[1].name].typename + " " + val_tmp_name + " = boost::python::extract<" + known_containers[types[1].name].typename + ">(" + varname + "[" + varname + "_keylist[ " + cntr_name + " ]]);"
			text += known_containers[types[1].name].translate(val_tmp_name, types[1].cont.args, prefix+"\t")
			val_tmp_name = val_tmp_name + "___tmp"
		elif types[1].name in classnames:
			text += prefix + "\t" + types[1].name + "* " + val_tmp_name + " = boost::python::extract<" + types[1].name + "*>(" + varname + "[" + varname + "_keylist[ " + cntr_name + " ]]);"
		else:
			text += prefix + "\t" + types[1].name + " " + val_tmp_name + " = boost::python::extract<" + types[1].name + ">(" + varname + "[" + varname + "_keylist[ " + cntr_name + " ]]);"

		text += prefix + "\t" + varname + "___tmp." + c.insert_name + "(std::pair<" + types[0].gen_text_cpp() + ", " + types[1].gen_text_cpp() + ">("

		if types[0].name not in classnames:
			text += key_tmp_name
		else:
			if types[0].attr_type != attr_types.star:
				text += "*"
			text += key_tmp_name + "->get_cpp_obj()"
		
		text += ", "
		if types[1].name not in classnames:
			text += val_tmp_name
		else:
			if types[1].attr_type != attr_types.star:
				text += "*"
			text += val_tmp_name + "->get_cpp_obj()"
		text += "));\n" + prefix + "}"
		return text
	
	#Generate c++ code to translate to a boost::python::dict
	@classmethod
	def translate_cpp(c, varname, types, prefix, ref):
		text  = prefix + c.typename + " " + varname + "___tmp;"
		tmp_name = "tmp_" + str(Translator.tmp_cntr)
		Translator.tmp_cntr = Translator.tmp_cntr + 1
		if ref:
			text += prefix + "for(auto " + tmp_name + " : *" + varname + ")"
		else:
			text += prefix + "for(auto " + tmp_name + " : " + varname + ")"
		text += prefix + "{"
		if types[1].name in known_containers:
			text += prefix + "\tauto " + tmp_name + "_second = " + tmp_name + ".second;"
			text += known_containers[types[1].name].translate_cpp(tmp_name + "_second", types[1].cont.args, prefix + "\t", types[1].attr_type == attr_types.star)

		if types[0].name in classnames:
			text += prefix + "\t" + varname + "___tmp[" + types[0].name + "::get_py_obj(" + tmp_name + ".first)] = "
		elif types[0].name not in known_containers:
			text += prefix + "\t" + varname + "___tmp[" + tmp_name + ".first] = "

		if types[1].name in classnames:
			if types[1].attr_type == attr_types.star:
				text += types[1].name + "::get_py_obj(" + tmp_name + ".second);"
			else:
				text += "*" + types[1].name + "::get_py_obj(&" + tmp_name + ".second);"
		elif types[1].name in known_containers:
			text += tmp_name + "_second___tmp;"
		else:
			text += tmp_name + ".second;"
		text += prefix + "}"
		return text

#Sub-type for dict
class DictTranslator(PythonDictTranslator):
	insert_name = "insert"
	orig_name = "dict"

#Sub_type for std::map
class MapTranslator(PythonDictTranslator):
	insert_name = "insert"
	orig_name = "std::map"	

#Translator for std::pair. Derived from PythonDictTranslator because the
#gen_type function is the same (because both have two template parameters)
class TupleTranslator(PythonDictTranslator):
	typename = "boost::python::tuple"
	orig_name = "std::pair"

	#Generate c++ code to translate from a boost::python::tuple
	@classmethod
	def translate(c, varname, types, prefix):
		text  = prefix + types[0].name + " " + varname + "___tmp_0 = boost::python::extract<" + types[0].name + ">(" + varname + "[0]);"
		text += prefix + types[1].name + " " + varname + "___tmp_1 = boost::python::extract<" + types[1].name + ">(" + varname + "[1]);"
		text += prefix + TupleTranslator.gen_type(types) + " " + varname + "___tmp("
		if types[0].name.split(" ")[-1] in primitive_types:
			text += varname + "___tmp_0, "
		else:
			text += varname + "___tmp_0.get_cpp_obj(), "
		if types[1].name.split(" ")[-1] in primitive_types:
			text += varname + "___tmp_1);"
		else:
			text += varname + "___tmp_1.get_cpp_obj());"
		return text

	#Generate c++ code to translate to a boost::python::tuple
	@classmethod
	def translate_cpp(c, varname, types, prefix, ref):
		# if the tuple is a pair of SigSpecs (aka SigSig), then we need
		# to call get_py_obj() on each item in the tuple
		if types[0].name in classnames:
			first_var = types[0].name + "::get_py_obj(" + varname + ".first)"
		else:
			first_var = varname + ".first"
		if types[1].name in classnames:
			second_var = types[1].name + "::get_py_obj(" + varname + ".second)"
		else:
			second_var = varname + ".second"
		text  = prefix + TupleTranslator.typename + " " + varname + "___tmp = boost::python::make_tuple(" + first_var + ", " + second_var + ");"
		return text

#Associate the Translators with their c++ type
known_containers = {
	"std::set"        : SetTranslator,
	"std::vector"     : VectorTranslator,
	"pool"            : PoolTranslator,
	"idict"           : IDictTranslator,
	"dict"            : DictTranslator,
	"std::pair"       : TupleTranslator,
	"std::map"        : MapTranslator,
	"RTLIL::ObjRange" : ObjRangeTranslator
}

class Attribute:
	wtype = None
	varname = None
	is_const = False
	default_value = None
	pos = None
	pos_counter = 0

	def __init__(self, wtype, varname, is_const = False, default_value = None):
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
			prefix= "long " + prefix
			str_def = str_def[5:]
		while str.startswith(str_def, "short "):
			prefix = "short " + prefix
			str_def = str_def[6:]

		if str_def.find("<") != -1 and str_def.find("<") < str_def.find(" "):
			closing = find_closing(str_def[str_def.find("<"):], "<", ">") + str_def.find("<") + 1
			arg.wtype = WType.from_string(str_def[:closing].strip(), containing_file, line_number)
			str_def = str_def[closing+1:]
		else:
			if str_def.count(" ") > 0:
				arg.wtype = WType.from_string(prefix + str_def[:str_def.find(" ")].strip(), containing_file, line_number)
				str_def = str_def[str_def.find(" ")+1:]
			else:
				arg.wtype = WType.from_string(prefix + str_def.strip(), containing_file, line_number)
				str_def = ""
				arg.varname = ""

		if arg.wtype == None:
			return None
		if str_def.count("=") == 0:
			arg.varname = str_def.strip()
			if arg.varname.find(" ") > 0:
				return None
		else:
			arg.varname = str_def[:str_def.find("=")].strip()
			if arg.varname.find(" ") > 0:
				return None
			str_def = str_def[str_def.find("=")+1:].strip()
			arg.default_value = str_def[arg.varname.find("=")+1:].strip()
		if len(arg.varname) == 0:
			arg.varname = None
			return arg
		if arg.varname[0] == '*':
			arg.wtype.attr_type = attr_types.star
			arg.varname = arg.varname[1:]
		elif arg.varname[0] == '&':
			if arg.wtype.attr_type != attr_types.default:
				return None
			if arg.varname[1] == '&':
				arg.wtype.attr_type = attr_types.ampamp
				arg.varname = arg.varname[2:]
			else:
				arg.wtype.attr_type = attr_types.amp
				arg.varname = arg.varname[1:]
		return arg

	#Generates the varname. If the attribute has no name in the header file,
	#a name is generated
	def gen_varname(self):
		if self.varname != None:
			return self.varname
		if self.wtype.name == "void":
			return ""
		if self.pos == None:
			self.pos = Attribute.pos_counter
			Attribute.pos_counter = Attribute.pos_counter + 1
		return "gen_varname_" + str(self.pos)

	#Generates the text for the function headers with wrapper types
	def gen_listitem(self):
		prefix = ""
		if self.is_const:
			prefix = "const "
		if self.wtype.name in classnames:
			return prefix + self.wtype.name + "* " + self.gen_varname()
		if self.wtype.name in known_containers:
			return prefix + known_containers[self.wtype.name].typename + " " + self.gen_varname()
		return prefix + self.wtype.name + " " + self.gen_varname()

	#Generates the test for the function headers with c++ types
	def gen_listitem_cpp(self):
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
			return prefix + known_containers[self.wtype.name].gen_type(self.wtype.cont.args) + " " + infix + self.gen_varname()
		if self.wtype.name in classnames:
			return prefix + class_by_name(self.wtype.name).namespace + "::" + self.wtype.name + " " + infix + self.gen_varname()
		return prefix + self.wtype.name + " " + infix + self.gen_varname()

	#Generates the listitem withtout the varname, so the signature can be
	#compared
	def gen_listitem_hash(self):
		prefix = ""
		if self.is_const:
			prefix = "const "
		if self.wtype.name in classnames:
			return prefix + self.wtype.name + "* "
		if self.wtype.name in known_containers:
			return known_containers[self.wtype.name].typename
		return prefix + self.wtype.name
		
	#Generate Translation code for the attribute
	def gen_translation(self):
		if self.wtype.name in known_containers:
			return known_containers[self.wtype.name].translate(self.gen_varname(), self.wtype.cont.args, "\n\t\t")
		return ""

	#Generate Translation code from c++ for the attribute
	def gen_translation_cpp(self):
		if self.wtype.name in known_containers:
			return known_containers[self.wtype.name].translate_cpp(self.gen_varname(), self.wtype.cont.args, "\n\t\t", self.wtype.attr_type == attr_types.star)
		return ""

	#Generate Text for the call
	def gen_call(self):
		ret = self.gen_varname()
		if self.wtype.name in known_containers:
			if self.wtype.attr_type == attr_types.star:
				return "&" + ret + "___tmp"
			return ret + "___tmp"
		if self.wtype.name in classnames:
			if self.wtype.attr_type != attr_types.star:
				ret = "*" + ret
			return ret + "->get_cpp_obj()"
		if self.wtype.name == "char *" and self.gen_varname() in ["format", "fmt"]:
			return "\"%s\", " + self.gen_varname()
		if self.wtype.attr_type == attr_types.star:
			return "&" + ret
		return ret

	def gen_call_cpp(self):
		ret = self.gen_varname()
		if self.wtype.name.split(" ")[-1] in primitive_types or self.wtype.name in enum_names:
			if self.wtype.attr_type == attr_types.star:
				return "&" + ret
			return ret
		if self.wtype.name not in classnames:
			if self.wtype.attr_type == attr_types.star:
				return "&" + ret + "___tmp"
			return ret + "___tmp"
		if self.wtype.attr_type != attr_types.star:
			ret = "*" + ret
		return self.wtype.name + "::get_py_obj(" + self.gen_varname()  + ")"

	#Generate cleanup code
	def gen_cleanup(self):
		if self.wtype.name in primitive_types or self.wtype.name in classnames or self.wtype.name in enum_names or not self.wtype.attr_type == attr_types.star or (self.wtype.name in known_containers and self.wtype.attr_type == attr_types.star):
			return ""
		return "\n\t\tdelete " + self.gen_varname() + "___tmp;"

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

	def __init__(self, name, link_type, id_, string_id = None, hash_id = None, needs_clone = False):
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

	def printable_constrs(self):
		ret = 0
		for con in self.found_constrs:
			if not con.protected:
				ret += 1
		return ret

	def gen_decl(self, filename):
		long_name = self.namespace + "::" + self.name

		text = "\n\t// WRAPPED from " + filename
		text += "\n\tstruct " + self.name
		if self.link_type == link_types.derive:
			text += " : public " + self.namespace + "::" + self.name
		text += "\n\t{\n"

		if self.link_type != link_types.derive:

			text += "\t\t" + long_name + "* ref_obj;\n"

			if self.link_type == link_types.ref_copy or self.link_type == link_types.pointer:
				text += "\n\t\t" + long_name + "* get_cpp_obj() const\n\t\t{\n\t\t\treturn ref_obj;\n\t\t}\n"
			elif self.link_type == link_types.global_list:
				text += "\t\t" + self.id_.wtype.name + " " + self.id_.varname + ";\n"
				text += "\n\t\t" + long_name + "* get_cpp_obj() const\n\t\t{"
				text += "\n\t\t\t" + long_name + "* ret = " + long_name + "::get_all_" + self.name.lower() + "s()->at(this->" + self.id_.varname + ");"
				text += "\n\t\t\tif(ret != NULL && ret == this->ref_obj)"
				text += "\n\t\t\t\treturn ret;"
				text += "\n\t\t\tthrow std::runtime_error(\"" + self.name + "'s c++ object does not exist anymore.\");"
				text += "\n\t\t\treturn NULL;"
				text += "\n\t\t}\n"

			#if self.link_type != link_types.pointer:
			text += "\n\t\tstatic " + self.name + "* get_py_obj(" + long_name + "* ref)\n\t\t{"
			text += "\n\t\t\tif(ref == nullptr){"
			text += "\n\t\t\t\tthrow std::runtime_error(\"" + self.name + " does not exist.\");"
			text += "\n\t\t\t}"
			text += "\n\t\t\t" + self.name + "* ret = (" + self.name + "*)malloc(sizeof(" + self.name + "));"
			if self.link_type == link_types.pointer:
				text += "\n\t\t\tret->ref_obj = ref;"
			if self.link_type == link_types.ref_copy:
				if self.needs_clone:
					text += "\n\t\t\tret->ref_obj = ref->clone();"
				else:
					text += "\n\t\t\tret->ref_obj = new "+long_name+"(*ref);"
			if self.link_type == link_types.global_list:
				text += "\n\t\t\tret->ref_obj = ref;"
				text += "\n\t\t\tret->" + self.id_.varname + " = ret->ref_obj->" + self.id_.varname + ";"
			text += "\n\t\t\treturn ret;"
			text += "\n\t\t}\n"

			if self.link_type == link_types.ref_copy:
				text += "\n\t\tstatic " + self.name + "* get_py_obj(" + long_name + " ref)\n\t\t{"
				text += "\n\t\t\t" + self.name + "* ret = (" + self.name + "*)malloc(sizeof(" + self.name + "));"
				if self.needs_clone:
					text += "\n\t\t\tret->ref_obj = ref.clone();"
				else:
					text += "\n\t\t\tret->ref_obj = new "+long_name+"(ref);"
				text += "\n\t\t\treturn ret;"
				text += "\n\t\t}\n"

			for con in self.found_constrs:
				text += con.gen_decl()
			if self.base_class is not None:
				text += "\n\t\tvirtual ~" + self.name + "() { };"
			for var in self.found_vars:
				text += var.gen_decl()
			for fun in self.found_funs:
				text += fun.gen_decl()


		if self.link_type == link_types.derive:
			duplicates = {}
			for fun in self.found_funs:
				if fun.name in duplicates:
					fun.gen_alias()
					duplicates[fun.name].gen_alias()
				else:
					duplicates[fun.name] = fun

			text += "\n\t\t" + long_name + "* get_cpp_obj() const\n\t\t{\n\t\t\treturn (" + self.namespace + "::" + self.name +"*)this;\n\t\t}\n"
			text += "\n\t\tstatic " + self.name + "* get_py_obj(" + long_name + "* ref)\n\t\t{"
			text += "\n\t\t\treturn (" + self.name + "*)ref;"
			text += "\n\t\t}\n"

			for con in self.found_constrs:
				text += con.gen_decl_derive()
			for var in self.found_vars:
				text += var.gen_decl()
			for fun in self.found_funs:
				text += fun.gen_decl_virtual()

		if self.hash_id != None:
			text += "\n\t\tunsigned int get_hash_py()"
			text += "\n\t\t{"
			suffix = f"->{self.hash_id}" if self.hash_id else f"->{self.hash_id}"
			if self.hash_id == "":
				text += f"\n\t\t\treturn run_hash(*(get_cpp_obj()));"
			else:
				text += f"\n\t\t\treturn run_hash(get_cpp_obj()->{self.hash_id});"
			text += "\n\t\t}"

		text += "\n\t};\n"

		if self.link_type == link_types.derive:
			text += "\n\tstruct " + self.name + "Wrap : " + self.name + ", boost::python::wrapper<" + self.name + ">"
			text += "\n\t{"

			for con in self.found_constrs:
				text += con.gen_decl_wrapperclass()
			for fun in self.found_funs:
				text += fun.gen_default_impl()

			text += "\n\t};"

		text += "\n\tstd::ostream &operator<<(std::ostream &ostr, const " + self.name + " &ref)"
		text += "\n\t{"
		text += "\n\t\tostr << \"" + self.name
		if self.string_id != None:
			text +=" \\\"\""
			text += " << ref.get_cpp_obj()->" + self.string_id
			text += " << \"\\\"\""
		else:
			text += " at \" << ref.get_cpp_obj()"
		text += ";"
		text += "\n\t\treturn ostr;"
		text += "\n\t}"
		text += "\n"

		return text

	def gen_funs(self, filename):
		text = ""
		if self.link_type != link_types.derive:
			for con in self.found_constrs:
				text += con.gen_def()
			for var in self.found_vars:
				text += var.gen_def()
			for fun in self.found_funs:
				text += fun.gen_def()
		else:
			for var in self.found_vars:
				text += var.gen_def()
			for fun in self.found_funs:
				text += fun.gen_def_virtual()
		return text

	def gen_boost_py_body(self):
		text = ""
		if self.printable_constrs() == 0 or not self.contains_default_constr():
			text += ", no_init"
		text += ")"
		text += "\n\t\t\t.def(boost::python::self_ns::str(boost::python::self_ns::self))"
		text += "\n\t\t\t.def(boost::python::self_ns::repr(boost::python::self_ns::self))"
		for con in self.found_constrs:
			text += con.gen_boost_py()
		for var in self.found_vars:
			text += var.gen_boost_py()
		static_funs = []
		for fun in self.found_funs:
			text += fun.gen_boost_py()
			if fun.is_static and fun.alias not in static_funs:
				static_funs.append(fun.alias)
		for fun in static_funs:
			text += "\n\t\t\t.staticmethod(\"" + fun + "\")"

		if self.hash_id != None:
			text += "\n\t\t\t.def(\"__hash__\", &" + self.name + "::get_hash_py)"
		text += "\n\t\t\t;\n"
		return text

	def gen_boost_py(self):
		body = self.gen_boost_py_body()
		base_info = ""
		if self.base_class is not None:
			base_info = ", bases<" + (self.base_class.name) + ">"

		if self.link_type == link_types.derive:
			text = "\n\t\tclass_<" + self.name + base_info + ">(\"Cpp" + self.name + "\""
			text += body
			text += "\n\t\tclass_<" + self.name
			text += "Wrap, boost::noncopyable"
			text += ">(\"" + self.name + "\""
			text += body
		else:
			text = "\n\t\tclass_<" + self.name + base_info + ">(\"" + self.name + "\""
			text += body
		return text
	

	def contains_default_constr(self):
		for c in self.found_constrs:
			if len(c.args) == 0:
				return True
		return False

#CONFIGURE HEADER-FILES TO BE PARSED AND CLASSES EXPECTED IN THEM HERE

sources = [
	Source("kernel/celltypes",[
		WClass("CellType", link_types.pointer, None, None, "type", True),
		WClass("CellTypes", link_types.pointer, None, None, None, True)
		]
		),
	Source("kernel/consteval",[
		WClass("ConstEval", link_types.pointer, None, None, None, True)
		]
		),
	Source("kernel/log",[]),
	Source("kernel/register",[
		WClass("Pass", link_types.derive, None, None, None, True),
		]
		),
	Source("kernel/rtlil",[
		WClass("IdString", link_types.ref_copy, None, "str()", ""),
		WClass("Const", link_types.ref_copy, None, "as_string()", ""),
		WClass("AttrObject", link_types.ref_copy, None, None, None),
		WClass("NamedObject", link_types.ref_copy, None, None, None),
		WClass("Selection", link_types.ref_copy, None, None, None),
		WClass("Monitor", link_types.derive, None, None, None),
		WClass("CaseRule",link_types.ref_copy, None, None, None, True),
		WClass("SwitchRule",link_types.ref_copy, None, None, None, True),
		WClass("SyncRule", link_types.ref_copy, None, None, None, True),
		WClass("Process",  link_types.ref_copy, None, "name.c_str()", "name"),
		WClass("SigChunk", link_types.ref_copy, None, None, None),
		WClass("SigBit", link_types.ref_copy, None, None, ""),
		WClass("SigSpec", link_types.ref_copy, None, None, ""),
		WClass("Cell", link_types.global_list, Attribute(WType("unsigned int"), "hashidx_"), "name.c_str()", ""),
		WClass("Wire", link_types.global_list, Attribute(WType("unsigned int"), "hashidx_"), "name.c_str()", ""),
		WClass("Memory", link_types.global_list, Attribute(WType("unsigned int"), "hashidx_"), "name.c_str()", ""),
		WClass("Module", link_types.global_list, Attribute(WType("unsigned int"), "hashidx_"), "name.c_str()", ""),
		WClass("Design", link_types.global_list, Attribute(WType("unsigned int"), "hashidx_"), "hashidx_", "")
		]
		),
	#Source("kernel/satgen",[
	#	]
	#	),
	#Source("libs/ezsat/ezsat",[
	#	]
	#	),
	#Source("libs/ezsat/ezminisat",[
	#	]
	#	),
	Source("kernel/sigtools",[
		WClass("SigMap", link_types.pointer, None, None, None, True)
		]
		),
	Source("kernel/yosys",[
		]
		),
	Source("kernel/cost",[])
	]

blacklist_methods = ["YOSYS_NAMESPACE::Pass::run_register", "YOSYS_NAMESPACE::Module::Pow"]

enum_names = ["State","SyncType","ConstFlags"]

enums = [] #Do not edit
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
	return text.find(close_tok) + find_closing(text[text.find(close_tok)+1:], open_tok, close_tok) + 1

def unpretty_string(s):
	s = s.strip()
	while s.find("  ") != -1:
		s = s.replace("  "," ")
	while s.find("\t") != -1:
		s = s.replace("\t"," ")
	s = s.replace(" (","(")
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
		if(len(split) != 2):
			return None
		enum.name = split[0].strip()
		if enum.name not in enum_names:
			return None
		str_def = split[1]
		if str_def.count("{") != str_def.count("}") != 1:
			return None
		if len(str_def) < str_def.find("}")+2 or str_def[str_def.find("}")+1] != ';':
			return None
		str_def = str_def.split("{")[-1].split("}")[0]
		enum.values = []
		for val in str_def.split(','):
			enum.values.append(val.strip().split('=')[0].strip())
		enum.namespace = namespace
		return enum

	def gen_boost_py(self):
		text = "\n\t\tenum_<" + self.namespace + "::" + self.name + ">(\"" + self.name + "\")\n"
		for value in self.values:
			text += "\t\t\t.value(\"" + value + "\"," + self.namespace + "::" + value + ")\n"
		text += "\t\t\t;\n"
		return text

	def __str__(self):
		ret = "Enum " + self.namespace + "::" + self.name + "(\n"
		for val in self.values:
			ret = ret + "\t" + val + "\n"
		return ret + ")"

	def __repr__(self):
		return __str__(self)

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

	def from_string(str_def, containing_file, class_, line_number, protected = False):
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
		str_def = str_def[len(class_.name)+1:]
		found = find_closing(str_def, "(", ")")
		if found == -1:
			return None
		str_def = str_def[0:found].strip()
		if len(str_def) == 0:
			return con
		for arg in split_list(str_def, ","):
			parsed = Attribute.from_string(arg.strip(), containing_file, line_number)
			if parsed == None:
				return None
			con.args.append(parsed)
		return con

	def gen_decl(self):
		if self.duplicate or self.protected:
			return ""
		text =  "\n\t\t// WRAPPED from \"" + self.orig_text.replace("\n"," ") + "\" in " + self.containing_file
		text += "\n\t\t" + self.member_of.name + "("
		for arg in self.args:
			text += arg.gen_listitem() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += ");\n"
		return text

	def gen_decl_derive(self):
		if self.duplicate or self.protected:
			return ""
		text =  "\n\t\t// WRAPPED from \"" + self.orig_text.replace("\n"," ") + "\" in " + self.containing_file
		text += "\n\t\t" + self.member_of.name + "("
		for arg in self.args:
			text += arg.gen_listitem() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += ")"
		if len(self.args) == 0:
			return text + "{}"
		text += " : "
		text += self.member_of.namespace + "::" + self.member_of.name + "("
		for arg in self.args:
			text += arg.gen_call() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += "){}\n"
		return text

	def gen_decl_wrapperclass(self):
		if self.duplicate or self.protected:
			return ""
		text =  "\n\t\t// WRAPPED from \"" + self.orig_text.replace("\n"," ") + "\" in " + self.containing_file
		text += "\n\t\t" + self.member_of.name + "Wrap("
		for arg in self.args:
			text += arg.gen_listitem() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += ")"
		if len(self.args) == 0:
			return text + "{}"
		text += " : "
		text += self.member_of.name + "("
		for arg in self.args:
			text += arg.gen_call() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += "){}\n"
		return text

	def gen_decl_hash_py(self):
		text = self.member_of.name + "("
		for arg in self.args:
			text += arg.gen_listitem_hash() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += ");"
		return text

	def gen_def(self):
		if self.duplicate or self.protected:
			return ""
		text = "\n\t// WRAPPED from \"" + self.orig_text.replace("\n"," ") + "\" in " + self.containing_file
		text += "\n\t" + self.member_of.name + "::" + self.member_of.name + "("
		for arg in self.args:
			text += arg.gen_listitem() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		text +=")\n\t{"
		for arg in self.args:
			text += arg.gen_translation()
		if self.member_of.link_type != link_types.derive:
			text += "\n\t\tthis->ref_obj = new " + self.member_of.namespace + "::" + self.member_of.name + "("
		for arg in self.args:
			text += arg.gen_call() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		if self.member_of.link_type != link_types.derive:
			text += ");"
		if self.member_of.link_type == link_types.global_list:
			text += "\n\t\tthis->" + self.member_of.id_.varname + " = this->ref_obj->" + self.member_of.id_.varname + ";"
		for arg in self.args:
			text += arg.gen_cleanup()
		text += "\n\t}\n"
		return text

	def gen_boost_py(self):
		if self.duplicate or self.protected or len(self.args) == 0:
			return ""
		text  = "\n\t\t\t.def(init"
		text += "<"
		for a in self.args:
			text += a.gen_listitem_hash() + ", "
		text = text[0:-2] + ">())"
		return text

class WFunction:
	orig_text = None
	is_static = False
	is_inline = False
	is_virtual = False
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
		str_def = str_def.replace("operator ","operator")

		# remove attributes from the start
		if str.startswith(str_def, "[[") and "]]" in str_def:
			str_def = str_def[str_def.find("]]")+2:]

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

		func.ret_type = WType.from_string(prefix + parts[0], containing_file, line_number)

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

		post_qualifiers = str_def[found + 1:].lstrip().replace("{", " {") + " "
		if post_qualifiers.startswith("const "):
			func.is_const = True

		str_def = str_def[0:found]
		if func.name in blacklist_methods:
			return None
		if func.namespace != None and func.namespace != "":
			if (func.namespace + "::" + func.name) in blacklist_methods:
				return None
			if func.member_of != None:
				if (func.namespace + "::" + func.member_of.name + "::" + func.name) in blacklist_methods:
					return None
		if func.is_operator and func.name.replace(" ","").replace("operator","").split("::")[-1] not in wrappable_operators:
			return None

		testname = func.name
		if func.is_operator:
			testname = testname[:testname.find("operator")]
		if testname.count(")") != 0 or testname.count("(") != 0 or testname.count("~") != 0 or testname.count(";") != 0 or testname.count(">") != 0 or testname.count("<") != 0 or testname.count("throw") != 0:
			return None

		func.alias = func.name
		if func.name in keyword_aliases:
			func.alias = keyword_aliases[func.name]
		str_def = str_def[:found].strip()
		if(len(str_def) == 0):
			return func
		for arg in split_list(str_def, ","):
			if arg.strip() == "...":
				continue
			parsed = Attribute.from_string(arg.strip(), containing_file, line_number)
			if parsed == None:
				return None
			func.args.append(parsed)
		return func

	@property
	def mangled_name(self):
		mangled_typename = lambda code: code.replace("::", "_").replace("<","_").replace(">","_") \
										   .replace(" ","").replace("*","").replace(",","")

		return self.name + "".join(
			f"__{mangled_typename(arg.wtype.gen_text_cpp())}" for arg in self.args
		)

	def gen_alias(self):
		self.alias = self.mangled_name

	def gen_post_qualifiers(self, derived=False):
		if self.member_of != None and self.member_of.link_type == link_types.derive and self.is_virtual and derived:
			# we drop the qualifiers when deriving callbacks to be implemented in Python
			return ''
		return ' const' if self.is_const else ''

	def gen_decl(self):
		if self.duplicate:
			return ""
		text =  "\n\t\t// WRAPPED from \"" + self.orig_text.replace("\n"," ") + "\" in " + self.containing_file
		text += "\n\t\t"
		if self.is_static:
			text += "static "
		text += self.ret_type.gen_text() + " " + self.alias + "("
		for arg in self.args:
			text += arg.gen_listitem()
			text += ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += f"){self.gen_post_qualifiers()};\n"
		return text

	def gen_decl_virtual(self):
		if self.duplicate:
			return ""
		if not self.is_virtual:
			return self.gen_decl()
		text =  "\n\t\t// WRAPPED from \"" + self.orig_text.replace("\n"," ") + "\" in " + self.containing_file
		text += "\n\t\tvirtual "
		if self.is_static:
			text += "static "
		text += self.ret_type.gen_text() + " py_" + self.alias + "("
		for arg in self.args:
			text += arg.gen_listitem()
			text += ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += ")"
		if len(self.args) == 0 and self.ret_type.name == "void":
			text += "{}"
		else:
			text += "\n\t\t{"
			for arg in self.args:
				text += "\n\t\t\t(void)" + arg.gen_varname() + ";"
			if self.ret_type.name == "void":
				pass
			elif self.ret_type.name == "bool":
				text += "\n\t\t\treturn false;"
			else:
				raise NotImplementedError(self.ret_type.name)
			text += "\n\t\t}\n"
		text += "\n\t\tvirtual "
		if self.is_static:
			text += "static "
		text += self.ret_type.gen_text() + " " + self.name + "("
		for arg in self.args:
			text += arg.gen_listitem_cpp()
			text += ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += f"){self.gen_post_qualifiers()} override;\n"
		return text

	def gen_decl_hash_py(self):
		text = self.ret_type.gen_text() + " " + self.alias + "("
		for arg in self.args:
			text += arg.gen_listitem_hash() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += ");"
		return text

	def gen_def(self):
		if self.duplicate:
			return ""
		text  = "\n\t// WRAPPED from \"" + self.orig_text.replace("\n"," ") + "\" in " + self.containing_file
		text += "\n\t" + self.ret_type.gen_text() + " "
		if self.member_of != None:
			text += self.member_of.name + "::"
		text += self.alias + "("
		for arg in self.args:
			text += arg.gen_listitem()
			text += ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += f"){self.gen_post_qualifiers()}\n\t{{"
		for arg in self.args:
			text += arg.gen_translation()
		text += "\n\t\t"
		if self.ret_type.name != "void":
			if self.ret_type.name in known_containers:
				text += self.ret_type.gen_text_cpp()
			else:
				text += self.ret_type.gen_text()
			if self.ret_type.name in classnames or (self.ret_type.name in known_containers and self.ret_type.attr_type == attr_types.star):
				text += "*"
			text += " ret_ = "
			if self.ret_type.name in classnames:
				text += self.ret_type.name + "::get_py_obj("
		if self.member_of == None:
			text += "::" + self.namespace + "::" + self.alias + "("
		elif self.is_static:
			text += self.member_of.namespace + "::" + self.member_of.name + "::" + self.name + "("
		else:
			text += "this->get_cpp_obj()->" + self.name + "("
		for arg in self.args:
			text += arg.gen_call() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		if self.ret_type.name in classnames:
			text += ")"
		text += ");"
		for arg in self.args:
			text += arg.gen_cleanup()
		if self.ret_type.name != "void":
			if self.ret_type.name in classnames:
				text += "\n\t\treturn *ret_;"
			elif self.ret_type.name in known_containers:
				text += known_containers[self.ret_type.name].translate_cpp("ret_", self.ret_type.cont.args, "\n\t\t", self.ret_type.attr_type == attr_types.star)
				text += "\n\t\treturn ret____tmp;"
			else:
				text += "\n\t\treturn ret_;"
		text += "\n\t}\n"
		return text

	def gen_def_virtual(self):
		if self.duplicate:
			return ""
		if not self.is_virtual:
			return self.gen_def()
		text =  "\n\t// WRAPPED from \"" + self.orig_text.replace("\n"," ") + "\" in " + self.containing_file
		text += "\n\t"
		if self.is_static:
			text += "static "
		text += self.ret_type.gen_text() + " " + self.member_of.name + "::" + self.name + "("
		for arg in self.args:
			text += arg.gen_listitem_cpp()
			text += ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += f"){self.gen_post_qualifiers()}\n\t{{"
		for arg in self.args:
			text += arg.gen_translation_cpp()
		return_stmt = "return " if self.ret_type.name != "void" else ""
		text += f"\n\t\t{return_stmt}"
		if self.member_of == None:
			text += "::" + self.namespace + "::" + self.alias + "("
		elif self.is_static:
			text += self.member_of.namespace + "::" + self.member_of.name + "::" + self.name + "("
		else:
			text += f"const_cast<{self.member_of.name}*>(this)->py_" + self.alias + "("
		for arg in self.args:
			text += arg.gen_call_cpp() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		if self.ret_type.name in classnames:
			text += ")"
		text += ");"
		for arg in self.args:
			text += arg.gen_cleanup()
		text += "\n\t}\n"
		return text

	def gen_default_impl(self):
		if self.duplicate:
			return ""
		if not self.is_virtual:
			return ""
		text = "\n\n\t\t" + self.ret_type.gen_text() + " py_" + self.alias + "("
		for arg in self.args:
			text += arg.gen_listitem() + ", "
		if len(self.args) > 0:
			text = text[:-2]

		call_string = "py_" + self.alias + "("
		for arg in self.args:
			call_string += arg.gen_varname() + ", "
		if len(self.args) > 0:
			call_string = call_string[0:-2]
		call_string += ");"

		return_stmt = "return " if self.ret_type.name != "void" else ""

		text += ")\n\t\t{"
		text += "\n\t\t\tif (boost::python::override py_" + self.alias + " = this->get_override(\"py_" + self.alias + "\")) {"
		text += "\n\t\t\t\ttry {"
		text += f"\n\t\t\t\t\t{return_stmt}" + call_string
		text += "\n\t\t\t\t} catch (boost::python::error_already_set &) {"
		text += "\n\t\t\t\t\tlog_python_exception_as_error();"
		text += "\n\t\t\t\t}"
		text += "\n\t\t\t} else {"
		text += f"\n\t\t\t\t{return_stmt}" + self.member_of.name + "::" + call_string
		text += "\n\t\t\t}"
		text += "\n\t\t}"

		text += "\n\n\t\t" + self.ret_type.gen_text() + " default_py_" + self.alias + "("
		for arg in self.args:
			text += arg.gen_listitem() + ", "
		if len(self.args) > 0:
			text = text[:-2]
		text += f")\n\t\t{{"
		text += f"\n\t\t\t{return_stmt}this->" + self.member_of.name + "::" + call_string
		text += "\n\t\t}"
		return text


	def gen_boost_py(self):
		if self.duplicate:
			return ""
		if self.member_of == None:
			text = "\n\t\tdef"
		else:
			text = "\n\t\t\t.def"
		if len(self.args) > -1:
			if self.ret_type.name in known_containers:
				text += "<" + known_containers[self.ret_type.name].typename + " "
			else:
				text += "<" + self.ret_type.name + " "
			if self.member_of == None or self.is_static:
				text += "(*)("
			else:
				text += "(" + self.member_of.name + "::*)("
			for a in self.args:
				text += a.gen_listitem_hash() + ", "
			if len(self.args) > 0:
				text = text[0:-2] + f"){self.gen_post_qualifiers(True)}>"
			else:
				text += f"void){self.gen_post_qualifiers(True)}>"

		if self.is_operator:
			text += "(\"" + wrappable_operators[self.name.replace("operator","")] + "\""
		else:
			if self.member_of != None and self.member_of.link_type == link_types.derive and self.is_virtual:
				text += "(\"py_" + self.alias + "\""
			else:
				text += "(\"" + self.alias + "\""
		if self.member_of != None:
			text += ", &" + self.member_of.name + "::"
			if self.member_of.link_type == link_types.derive and self.is_virtual:
				text += "py_" + self.alias
				text += ", &" + self.member_of.name + "Wrap::default_py_" + self.alias
			else:
				text += self.alias

			text += ")"
		else:
			text += ", " + "YOSYS_PYTHON::" + self.alias + ");"
		return text

class WMember:
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

		member.wtype = WType.from_string(prefix + parts[0], containing_file, line_number)

		if member.wtype == None:
			return None

		str_def = parts[1]
		for part in parts[2:]:
			str_def = str_def + " " + part

		if str_def.find("(") != -1 or str_def.find(")") != -1 or str_def.find("{") != -1 or str_def.find("}") != -1:
			return None

		found = str_def.find(";")
		if found == -1:
			return None

		found_eq = str_def.find("=")
		if found_eq != -1:
			found = found_eq

		member.name = str_def[:found]
		str_def = str_def[found+1:]
		if member.name.find("*") == 0:
			member.name = member.name.replace("*", "")
			member.wtype.attr_type = attr_types.star
		if member.name.find("&&") == 0:
			member.name = member.name.replace("&&", "")
			member.wtype.attr_type = attr_types.ampamp
		if member.name.find("&") == 0:
			member.name = member.name.replace("&", "")
			member.wtype.attr_type = attr_types.amp

		if(len(str_def.strip()) != 0):
			return None

		if len(member.name.split(",")) > 1:
			member_list = []
			for name in member.name.split(","):
				name = name.strip();
				member_list.append(WMember())
				member_list[-1].orig_text = member.orig_text
				member_list[-1].wtype = member.wtype
				member_list[-1].name = name
				member_list[-1].containing_file = member.containing_file
				member_list[-1].member_of = member.member_of
				member_list[-1].namespace = member.namespace
				member_list[-1].is_const = member.is_const
			return member_list

		return member

	def gen_decl(self):
		text = "\n\t\t" + self.wtype.gen_text() + " get_var_py_" + self.name + "();\n"
		if self.is_const:
			return text
		if self.wtype.name in classnames:
			text += "\n\t\tvoid set_var_py_" + self.name + "(" + self.wtype.gen_text() + " *rhs);\n"
		else:
			text += "\n\t\tvoid set_var_py_" + self.name + "(" + self.wtype.gen_text() + " rhs);\n"
		return text

	def gen_def(self):
		text = "\n\t" + self.wtype.gen_text() + " " + self.member_of.name +"::get_var_py_" + self.name + "()"
		text += "\n\t{\n\t\t"
		if self.wtype.attr_type == attr_types.star:
			text += "if(this->get_cpp_obj()->" + self.name + " == NULL)\n\t\t\t"
			text += "throw std::runtime_error(\"Member \\\"" + self.name + "\\\" is NULL\");\n\t\t"
		if self.wtype.name in known_containers:
			text += self.wtype.gen_text_cpp()
		else:
			text += self.wtype.gen_text()

		if self.wtype.name in classnames or (self.wtype.name in known_containers and self.wtype.attr_type == attr_types.star):
			text += "*"
		text += " ret_ = "
		if self.wtype.name in classnames:
			text += self.wtype.name + "::get_py_obj("
			if self.wtype.attr_type != attr_types.star:
				text += "&"
		text += "this->get_cpp_obj()->" + self.name
		if self.wtype.name in classnames:
			text += ")"
		text += ";"
		
		if self.wtype.name in classnames:
			text += "\n\t\treturn *ret_;"
		elif self.wtype.name in known_containers:
			text += known_containers[self.wtype.name].translate_cpp("ret_", self.wtype.cont.args, "\n\t\t", self.wtype.attr_type == attr_types.star)
			text += "\n\t\treturn ret____tmp;"
		else:
			text += "\n\t\treturn ret_;"
		text += "\n\t}\n"

		if self.is_const:
			return text

		ret = Attribute(self.wtype, "rhs");

		if self.wtype.name in classnames:
			text += "\n\tvoid " + self.member_of.name+ "::set_var_py_" + self.name + "(" + self.wtype.gen_text() + " *rhs)"
		else:
			text += "\n\tvoid " + self.member_of.name+ "::set_var_py_" + self.name + "(" + self.wtype.gen_text() + " rhs)"
		text += "\n\t{"
		text += ret.gen_translation()
		text += "\n\t\tthis->get_cpp_obj()->" + self.name + " = " + ret.gen_call() + ";"
		text += "\n\t}\n"		

		return text;

	def gen_boost_py(self):
		text = "\n\t\t\t.add_property(\"" + self.name + "\", &" + self.member_of.name + "::get_var_py_" + self.name 
		if not self.is_const:
			text += ", &" + self.member_of.name + "::set_var_py_" + self.name
		text += ")"
		return text

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

		if str_def.find("(") != -1 or str_def.find(")") != -1 or str_def.find("{") != -1 or str_def.find("}") != -1:
			return None

		found = str_def.find(";")
		if found == -1:
			return None

		found_eq = str_def.find("=")
		if found_eq != -1:
			found = found_eq

		glbl.name = str_def[:found]
		str_def = str_def[found+1:]
		if glbl.name.find("*") == 0:
			glbl.name = glbl.name.replace("*", "")
			glbl.wtype.attr_type = attr_types.star
		if glbl.name.find("&&") == 0:
			glbl.name = glbl.name.replace("&&", "")
			glbl.wtype.attr_type = attr_types.ampamp
		if glbl.name.find("&") == 0:
			glbl.name = glbl.name.replace("&", "")
			glbl.wtype.attr_type = attr_types.amp

		if(len(str_def.strip()) != 0):
			return None

		if len(glbl.name.split(",")) > 1:
			glbl_list = []
			for name in glbl.name.split(","):
				name = name.strip();
				glbl_list.append(WGlobal())
				glbl_list[-1].orig_text = glbl.orig_text
				glbl_list[-1].wtype = glbl.wtype
				glbl_list[-1].name = name
				glbl_list[-1].containing_file = glbl.containing_file
				glbl_list[-1].namespace = glbl.namespace
				glbl_list[-1].is_const = glbl.is_const
			return glbl_list

		return glbl

	def gen_def(self):
		text = "\n\t"
		if self.is_const:
			text += "const "
		text += self.wtype.gen_text() + " get_var_py_" + self.name + "()"
		text += "\n\t{\n\t\t"
		if self.wtype.attr_type == attr_types.star:
			text += "if(" + self.namespace + "::" + self.name + " == NULL)\n\t\t\t"
			text += "throw std::runtime_error(\"" + self.namespace + "::" + self.name + " is NULL\");\n\t\t"
		if self.wtype.name in known_containers:
			text += self.wtype.gen_text_cpp()
		else:
			if self.is_const:
				text += "const "
			text += self.wtype.gen_text()

		if self.wtype.name in classnames or (self.wtype.name in known_containers and self.wtype.attr_type == attr_types.star):
			text += "*"
		text += " ret_ = "
		if self.wtype.name in classnames:
			text += self.wtype.name + "::get_py_obj("
			if self.wtype.attr_type != attr_types.star:
				text += "&"
		text += self.namespace + "::" + self.name
		if self.wtype.name in classnames:
			text += ")"
		text += ";"
		
		if self.wtype.name in classnames:
			text += "\n\t\treturn *ret_;"
		elif self.wtype.name in known_containers:
			text += known_containers[self.wtype.name].translate_cpp("ret_", self.wtype.cont.args, "\n\t\t", self.wtype.attr_type == attr_types.star)
			text += "\n\t\treturn ret____tmp;"
		else:
			text += "\n\t\treturn ret_;"
		text += "\n\t}\n"

		if self.is_const:
			return text

		ret = Attribute(self.wtype, "rhs");

		if self.wtype.name in classnames:
			text += "\n\tvoid set_var_py_" + self.name + "(" + self.wtype.gen_text() + " *rhs)"
		else:
			text += "\n\tvoid set_var_py_" + self.name + "(" + self.wtype.gen_text() + " rhs)"
		text += "\n\t{"
		text += ret.gen_translation()
		text += "\n\t\t" + self.namespace + "::" + self.name + " = " + ret.gen_call() + ";"
		text += "\n\t}\n"		

		return text;

	def gen_boost_py(self):
		text = "\n\t\t\t.add_static_property(\"" + self.name + "\", &" + "YOSYS_PYTHON::get_var_py_" + self.name 
		if not self.is_const:
			text += ", &YOSYS_PYTHON::set_var_py_" + self.name
		text += ")"
		return text

def concat_namespace(tuple_list):
	if len(tuple_list) == 0:
		return ""
	ret = ""
	for namespace in tuple_list:
		ret += "::" + namespace[0]
	return ret[2:]

def calc_ident(text):
	if len(text) == 0 or text[0] != ' ':
		return 0
	return calc_ident(text[1:]) + 1

def assure_length(text, length, left = False):
	if len(text) > length:
		return text[:length]
	if left:
		return text + " "*(length - len(text))
	return " "*(length - len(text)) + text

def nesting_delta(s):
	return s.count("{") - s.count("}")

def parse_header(source):
	debug("Parsing " + source.name + ".pyh",1)
	source_file = open(source.name + ".pyh", "r")

	source_text = []
	in_line = source_file.readline()

	namespaces = []

	while(in_line):
		if(len(in_line)>1):
			source_text.append(in_line.replace("char *", "char_p ").replace("char* ", "char_p "))
		in_line = source_file.readline()

	i = 0

	namespaces = []
	classes = []
	private_segment = False

	while i < len(source_text):
		line = source_text[i].replace("YOSYS_NAMESPACE_BEGIN", "                    namespace YOSYS_NAMESPACE{").replace("YOSYS_NAMESPACE_END","                    }")
		ugly_line = unpretty_string(line)
		debug(f"READ:>> {line}", 2)

		# for anonymous unions, ignore union enclosure by skipping start line and replacing end line with new line
		if 'union {' in line:
			j = i+1
			while j < len(source_text):
				union_line = source_text[j]
				if '};' in union_line:
					source_text[j] = '\n'
					break
				j += 1
			if j != len(source_text):
				i += 1
				continue

		if str.startswith(ugly_line, "namespace "):# and ugly_line.find("std") == -1 and ugly_line.find("__") == -1:
			namespace_name = ugly_line[10:].replace("{","").strip()
			namespaces.append((namespace_name, ugly_line.count("{")))
			debug("-----NAMESPACE " + concat_namespace(namespaces) + "-----",3)
			i += 1
			continue

		if len(namespaces) != 0:
			namespaces[-1] = (namespaces[-1][0], namespaces[-1][1] + nesting_delta(ugly_line))
			if namespaces[-1][1] == 0:
				debug("-----END NAMESPACE " + concat_namespace(namespaces) + "-----",3)
				namespaces.pop()
				i += 1
				continue

		if (str.startswith(ugly_line, "struct ") or str.startswith(ugly_line, "class")) and ugly_line.count(";") == 0:
			# Opening a record declaration which isn't a forward declaration
			struct_name = ugly_line.split(" ")[1].split("::")[-1]
			impl_namespaces = ugly_line.split(" ")[1].split("::")[:-1]
			complete_namespace = concat_namespace(namespaces)
			for namespace in impl_namespaces:
				complete_namespace += "::" + namespace
			debug("\tFound " + struct_name + " in " + complete_namespace,2)

			base_class_name = None
			if len(ugly_line.split(" : ")) > 1: # class is derived
				deriv_str = ugly_line.split(" : ")[1]
				if len(deriv_str.split("::")) > 1: # namespace of base class is given
					base_class_name = deriv_str.split("::", 1)[1]
				else:
					base_class_name = deriv_str.split(" ")[0]
				debug("\t  " + struct_name + " is derived from " + base_class_name,2)
			base_class = class_by_name(base_class_name)

			c = (class_by_name(struct_name), ugly_line.count("{"))#calc_ident(line))
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

		if class_ != None and (line.find("private:") != -1 or line.find("protected:") != -1):
			private_segment = True
			i += 1
			continue
		if class_ != None and line.find("public:") != -1:
			private_segment = False
			i += 1
			continue

		candidate = None

		if private_segment and class_ != None and class_[0] != None:
			candidate = WConstructor.from_string(ugly_line, source.name, class_[0], i, True)
			if candidate != None:
				debug("\t\tFound constructor of class \"" + class_[0].name + "\" in namespace " + concat_namespace(namespaces),2)
				class_[0].found_constrs.append(candidate)
				i += 1
				continue

		if not private_segment and (class_ == None or class_[0] != None):
			if class_ != None:
				candidate = WFunction.from_string(ugly_line, source.name, class_[0], i, concat_namespace(namespaces))
			else:
				candidate = WFunction.from_string(ugly_line, source.name, None, i, concat_namespace(namespaces))
			if candidate != None and candidate.name.find("::") == -1:
				if class_ == None:
					debug("\tFound unowned function \"" + candidate.name + "\" in namespace " + concat_namespace(namespaces),2)
					unowned_functions.append(candidate)
				else:
					debug("\t\tFound function \"" + candidate.name + "\" of class \"" + class_[0].name + "\" in namespace " + concat_namespace(namespaces),2)
					class_[0].found_funs.append(candidate)
			else:
				candidate = WEnum.from_string(ugly_line, concat_namespace(namespaces), i)
				if candidate != None:
					enums.append(candidate)
					debug("\tFound enum \"" + candidate.name + "\" in namespace " + concat_namespace(namespaces),2)
				elif class_ != None and class_[1] == 1:
					candidate = WConstructor.from_string(ugly_line, source.name, class_[0], i)
					if candidate != None:
						debug("\t\tFound constructor of class \"" + class_[0].name + "\" in namespace " + concat_namespace(namespaces),2)
						class_[0].found_constrs.append(candidate)
					else:
						candidate = WMember.from_string(ugly_line, source.name, class_[0], i, concat_namespace(namespaces))
						if candidate != None:
							if type(candidate) == list:
								for c in candidate:
									debug("\t\tFound member \"" + c.name + "\" of class \"" + class_[0].name + "\" of type \"" + c.wtype.name + "\"", 2)
								class_[0].found_vars.extend(candidate)
							else:
								debug("\t\tFound member \"" + candidate.name + "\" of class \"" + class_[0].name + "\" of type \"" + candidate.wtype.name + "\"", 2)
								class_[0].found_vars.append(candidate)
				if candidate == None and class_ == None:
					candidate = WGlobal.from_string(ugly_line, source.name, i, concat_namespace(namespaces))
					if candidate != None:
						if type(candidate) == list:
							for c in candidate:
								glbls.append(c)
								debug("\tFound global \"" + c.name + "\" in namespace " + concat_namespace(namespaces), 2)
						else:
							glbls.append(candidate)
							debug("\tFound global \"" + candidate.name + "\" in namespace " + concat_namespace(namespaces), 2)

			j = i
			line = unpretty_string(line)
			while candidate == None and j+1 < len(source_text) and  line.count(';') <= 1 and line.count("(") >= line.count(")"):
				j += 1
				line = line + "\n" + unpretty_string(source_text[j])
				if class_ != None:
					candidate = WFunction.from_string(ugly_line, source.name, class_[0], i, concat_namespace(namespaces))
				else:
					candidate = WFunction.from_string(ugly_line, source.name, None, i, concat_namespace(namespaces))
				if candidate != None and candidate.name.find("::") == -1:
					if class_ == None:
						debug("\tFound unowned function \"" + candidate.name + "\" in namespace " + concat_namespace(namespaces),2)
						unowned_functions.append(candidate)
					else:
						debug("\t\tFound function \"" + candidate.name + "\" of class \"" + class_[0].name + "\" in namespace " + concat_namespace(namespaces),2)
						class_[0].found_funs.append(candidate)
					continue
				candidate = WEnum.from_string(line, concat_namespace(namespaces), i)
				if candidate != None:
					enums.append(candidate)
					debug("\tFound enum \"" + candidate.name + "\" in namespace " + concat_namespace(namespaces),2)
					continue
				if class_ != None:
					candidate = WConstructor.from_string(line, source.name, class_[0], i)
					if candidate != None:
						debug("\t\tFound constructor of class \"" + class_[0].name + "\" in namespace " + concat_namespace(namespaces),2)
						class_[0].found_constrs.append(candidate)
						continue
				if class_ == None:
					candidate = WGlobal.from_string(line, source.name, i, concat_namespace(namespaces))
					if candidate != None:
						if type(candidate) == list:
							for c in candidate:
								glbls.append(c)
								debug("\tFound global \"" + c.name + "\" in namespace " + concat_namespace(namespaces), 2)
						else:
							glbls.append(candidate)
							debug("\tFound global \"" + candidate.name + "\" in namespace " + concat_namespace(namespaces), 2)
						continue
		if candidate != None:
			while i < j:
				i += 1
				line = source_text[i].replace("YOSYS_NAMESPACE_BEGIN", "                    namespace YOSYS_NAMESPACE{").replace("YOSYS_NAMESPACE_END","                    }")
				ugly_line = unpretty_string(line)
				if len(namespaces) != 0:
					namespaces[-1] = (namespaces[-1][0], namespaces[-1][1] + nesting_delta(ugly_line))
					if namespaces[-1][1] == 0:
						debug("-----END NAMESPACE " + concat_namespace(namespaces) + "-----",3)
						namespaces.pop()
				if len(classes):
					c = (classes[-1][0] , classes[-1][1] + nesting_delta(ugly_line))
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

def expand_function(f):
	fun_list = []
	arg_list = []
	for arg in f.args:
		if arg.default_value != None and (arg.wtype.name.split(" ")[-1] in primitive_types or arg.wtype.name in enum_names or (arg.wtype.name in classnames and arg.default_value == "nullptr")):
			fi = copy.deepcopy(f)
			fi.args = copy.deepcopy(arg_list)
			fun_list.append(fi)
		arg_list.append(arg)
	fun_list.append(f)
	return fun_list

def expand_functions():
	global unowned_functions
	new_funs = []
	for fun in unowned_functions:
		new_funs.extend(expand_function(fun))
	unowned_functions = new_funs
	for source in sources:
		for class_ in source.classes:
			new_funs = []
			for fun in class_.found_funs:
				new_funs.extend(expand_function(fun))
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
					debug("Multiple declarations of " + fun.gen_decl_hash_py(),3)

					other = known_decls[fun.gen_decl_hash_py()]
					if fun.mangled_name == other.mangled_name:
						fun.duplicate = True
						debug("Disabled \"" + fun.gen_decl_hash_py() + "\"", 3)
						continue

					other.gen_alias()
					fun.gen_alias()
				else:
					known_decls[fun.gen_decl_hash_py()] = fun
			known_decls = []
			for con in class_.found_constrs:
				if con.gen_decl_hash_py() in known_decls:
					debug("Multiple declarations of " + con.gen_decl_hash_py(),3)
					con.duplicate = True
				else:
					known_decls.append(con.gen_decl_hash_py())
	known_decls = []
	for fun in unowned_functions:
		if fun.gen_decl_hash_py() in known_decls:
			debug("Multiple declarations of " + fun.gen_decl_hash_py(),3)
			fun.duplicate = True
		else:
			known_decls.append(fun.gen_decl_hash_py())

def gen_wrappers(filename, debug_level_ = 0):
	debug.debug_level = debug_level_
	for source in sources:
		parse_header(source)

	expand_functions()
	inherit_members()
	clean_duplicates()

	import shutil
	import math
	col = shutil.get_terminal_size((80,20)).columns
	debug("-"*col, 1)
	debug("-"*math.floor((col-7)/2)+"SUMMARY"+"-"*math.ceil((col-7)/2), 1)
	debug("-"*col, 1)
	for source in sources:
		for class_ in source.classes:
			debug("Class " + assure_length(class_.name, len(max(classnames, key=len)), True) + " contains " + assure_length(str(len(class_.found_vars)), 3, False) + " member variables, "+ assure_length(str(len(class_.found_funs)), 3, False) + " methods and " + assure_length(str(len(class_.found_constrs)), 2, False) + " constructors", 1)
			if len(class_.found_constrs) == 0:
				class_.found_constrs.append(WConstructor(source.name, class_))
	debug(str(len(unowned_functions)) + " functions are unowned", 1)
	debug(str(len(unowned_functions)) + " global variables", 1)
	for enum in enums:
		debug("Enum " + assure_length(enum.name, len(max(enum_names, key=len)), True) + " contains " + assure_length(str(len(enum.values)), 2, False) + " values", 1)
	debug("-"*col, 1)
	wrapper_file = open(filename, "w+")
	wrapper_file.write(
"""/*
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
 *  This is a generated file and can be overwritten by make
 */

#ifdef WITH_PYTHON
""")
	for source in sources:
		wrapper_file.write("#include \""+source.name+".h\"\n")
	wrapper_file.write("""
#include <boost/python/module.hpp>
#include <boost/python/class.hpp>
#include <boost/python/wrapper.hpp>
#include <boost/python/call.hpp>
#include <boost/python.hpp>
#include <iosfwd> // std::streamsize
#include <iostream>
#include <boost/iostreams/concepts.hpp>	// boost::iostreams::sink
#include <boost/iostreams/stream.hpp>
USING_YOSYS_NAMESPACE

namespace YOSYS_PYTHON {

	[[noreturn]] static void log_python_exception_as_error() {
		PyErr_Print();
		log_error("Python interpreter encountered an exception.\\n");
	}

	struct YosysStatics{};
""")

	for source in sources:
		for wclass in source.classes:
			wrapper_file.write("\n\tstruct " + wclass.name + ";")

	wrapper_file.write("\n")

	for source in sources:
		for wclass in source.classes:
			wrapper_file.write(wclass.gen_decl(source.name))

	wrapper_file.write("\n")

	for source in sources:
		for wclass in source.classes:
			wrapper_file.write(wclass.gen_funs(source.name))

	for fun in unowned_functions:
		wrapper_file.write(fun.gen_def())

	for glbl in glbls:
		wrapper_file.write(glbl.gen_def())

	wrapper_file.write("""	struct Initializer
	{
		Initializer() {
			if(!Yosys::yosys_already_setup())
			{
				Yosys::log_streams.push_back(&std::cout);
				Yosys::log_error_stderr = true;
				Yosys::yosys_setup();
			}
		}

		Initializer(Initializer const &) {}

		~Initializer() {
			Yosys::yosys_shutdown();
		}
	};


	/// source: https://stackoverflow.com/questions/26033781/converting-python-io-object-to-stdostream-when-using-boostpython?noredirect=1&lq=1
	/// @brief Type that implements the Boost.IOStream's Sink and Flushable
	///        concept for writing data to Python object that support:
	///          n = object.write(str) # n = None or bytes written
	///          object.flush()        # if flush exists, then it is callable
	class PythonOutputDevice
	{
	public:

		// This class models both the Sink and Flushable concepts.
		struct category
			: boost::iostreams::sink_tag,
				boost::iostreams::flushable_tag
		{};

		explicit
		PythonOutputDevice(boost::python::object object)
			: object_(object)
		{}

	// Sink concept.
	public:

		typedef char char_type;

		std::streamsize write(const char* buffer, std::streamsize buffer_size)
		{
			namespace python = boost::python;
			// Copy the buffer to a python string.
			python::str data(buffer, buffer_size);

			// Invoke write on the python object, passing in the data.	The following
			// is equivalent to:
			//	 n = object_.write(data)
			python::extract<std::streamsize> bytes_written(
				object_.attr("write")(data));

			// Per the Sink concept, return the number of bytes written.	If the
			// Python return value provides a numeric result, then use it.	Otherwise,
			// such as the case of a File object, use the buffer_size.
			return bytes_written.check()
				? bytes_written
				: buffer_size;
		}

	// Flushable concept.
	public:

		bool flush()
		{
			// If flush exists, then call it.
			boost::python::object flush = object_.attr("flush");
			if (!flush.is_none())
			{
				flush();
			}

			// Always return true.	If an error occurs, an exception should be thrown.
				return true;
		}

	private:
		boost::python::object object_;
	};

	/// @brief Use an auxiliary function to adapt the legacy function.
	void log_to_stream(boost::python::object object)
	{
		// Create an ostream that delegates to the python object.
		boost::iostreams::stream<PythonOutputDevice>* output = new boost::iostreams::stream<PythonOutputDevice>(object);
		Yosys::log_streams.insert(Yosys::log_streams.begin(), output);
	};


	BOOST_PYTHON_MODULE(libyosys)
	{
		using namespace boost::python;

		class_<Initializer>("Initializer");
		scope().attr("_hidden") = new Initializer();

		def("log_to_stream", &log_to_stream);
""")

	for enum in enums:
		wrapper_file.write(enum.gen_boost_py())

	for source in sources:
		for wclass in source.classes:
			wrapper_file.write(wclass.gen_boost_py())

	for fun in unowned_functions:
		wrapper_file.write(fun.gen_boost_py())

	wrapper_file.write("\n\n\t\tclass_<YosysStatics>(\"Yosys\")\n")
	for glbl in glbls:
		wrapper_file.write(glbl.gen_boost_py())
	wrapper_file.write("\t\t;\n")

	wrapper_file.write("\n\t}\n}\n#endif")

def print_includes():
	for source in sources:
		print(source.name + ".pyh")
