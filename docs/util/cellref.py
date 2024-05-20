#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path, PosixPath, WindowsPath
import re

from typing import Any
from sphinx.application import Sphinx
from sphinx.ext import autodoc
from sphinx.ext.autodoc import Documenter
from sphinx.util import logging

logger = logging.getLogger(__name__)

# cell signature
cell_ext_sig_re = re.compile(
    r'''^ (?:([^:\s]+):)?        # explicit file name
          ([\w$._]+?)?           # module and/or class name(s)
          (?:\.([\w_]+))?        # optional: thing name
          (::[\w_]+)?            #           attribute
          \s* $                  # and nothing more
          ''', re.VERBOSE)

class SimHelper:
    name: str = ""
    title: str = ""
    ports: str = ""
    source: str = ""
    desc: list[str]
    code: list[str]
    group: str = ""
    ver: str = "1"

    def __init__(self) -> None:
        self.desc = []

def simcells_reparse(cell: SimHelper):
    # cut manual signature
    cell.desc = cell.desc[3:]

    # code-block truth table
    new_desc = []
    indent = ""
    for line in cell.desc:
        if line.startswith("Truth table:"):
            indent = "   "
            new_desc.pop()
            new_desc.extend(["::", ""])
        new_desc.append(indent + line)
    cell.desc = new_desc

    # set version
    cell.ver = "2a"

def load_cell_lib(file: Path):
    simHelpers: dict[str, SimHelper] = {}
    simHelper = SimHelper()
    with open(file, "r") as f:
        lines = f.readlines()

    for lineno, line in enumerate(lines, 1):
        line = line.rstrip()
        # special comments
        if line.startswith("//-"):
            simHelper.desc.append(line[4:] if len(line) > 4 else "")
        elif line.startswith("//* "):
            _, key, val = line.split(maxsplit=2)
            setattr(simHelper, key, val)
        
        # code parsing
        if line.startswith("module "):
            clean_line = line[7:].replace("\\", "").replace(";", "")
            simHelper.name, simHelper.ports = clean_line.split(maxsplit=1)
            simHelper.code = []
            simHelper.source = f'{file.name}:{lineno}'
        elif not line.startswith("endmodule"):
            line = "    " + line
        try:
            simHelper.code.append(line.replace("\t", "    "))
        except AttributeError:
            # no module definition, ignore line
            pass
        if line.startswith("endmodule"):
            if simHelper.ver == "1" and file.name == "simcells.v":
                # default simcells parsing
                simcells_reparse(simHelper)
            if not simHelper.desc:
                # no help
                simHelper.desc.append("No help message for this cell type found.\n")
            elif simHelper.ver == "1" and file.name == "simlib.v" and simHelper.desc[1].startswith('    '):
                simHelper.desc.pop(1)
            simHelpers[simHelper.name] = simHelper
            simHelper = SimHelper()
    return simHelpers

class YosysCellDocumenter(Documenter):
    objtype = 'cell'
    parsed_libs: dict[Path, dict[str, SimHelper]] = {}
    object: SimHelper

    option_spec = {
        'source': autodoc.bool_option,
        'linenos': autodoc.bool_option,
    }

    @classmethod
    def can_document_member(
        cls,
        member: Any,
        membername: str,
        isattr: bool,
        parent: Any
    ) -> bool:
        sourcename = str(member).split(":")[0]
        if not sourcename.endswith(".v"):
            return False
        if membername == "__source":
            return False

    def parse_name(self) -> bool:
        try:
            matched = cell_ext_sig_re.match(self.name)
            path, modname, thing, attribute = matched.groups()
        except AttributeError:
            logger.warning(('invalid signature for auto%s (%r)') % (self.objtype, self.name),
                           type='cellref')
            return False
        
        if not path:
            return False

        self.modname = modname
        self.objpath = [path]
        self.attribute = attribute
        self.fullname = ((self.modname) + (thing or ''))

        return True
    
    def import_object(self, raiseerror: bool = False) -> bool:
        # find cell lib file
        objpath = Path('/'.join(self.objpath))
        if not objpath.exists():
            cells_loc: Path = self.config.cells_loc
            objpath = cells_loc / objpath

        # load cell lib
        try:
            parsed_lib = self.parsed_libs[objpath]
        except KeyError:
            try:
                parsed_lib = load_cell_lib(objpath)
            except FileNotFoundError:
                logger.warning(
                    f"unable to find cell lib at {'/'.join(self.objpath)}",
                    type = 'cellref',
                    subtype = 'import_object'
                )
                return False
            self.parsed_libs[objpath] = parsed_lib


        # get cell
        try:
            self.object = parsed_lib[self.modname]
        except KeyError:
            return False

        self.real_modname = f'{objpath}:{self.modname}'
        return True
    
    def get_sourcename(self) -> str:
        return self.objpath
    
    def format_name(self) -> str:
        return self.object.name

    def format_signature(self, **kwargs: Any) -> str:
        return f"{self.object.name} {self.object.ports}"
    
    def add_directive_header(self, sig: str) -> None:
        domain = getattr(self, 'domain', self.objtype)
        directive = getattr(self, 'directivetype', 'def')
        name = self.format_name()
        sourcename = self.get_sourcename()
        cell = self.object

        # cell definition
        self.add_line(f'.. {domain}:{directive}:: {name}', sourcename)

        # options
        opt_attrs = ["title", ]
        for attr in opt_attrs:
            val = getattr(cell, attr, None)
            if val:
                self.add_line(f'   :{attr}: {val}', sourcename)

        if self.options.noindex:
            self.add_line('   :noindex:', sourcename)
    
    def add_content(self, more_content: Any | None) -> None:
        # set sourcename and add content from attribute documentation
        sourcename = self.get_sourcename()
        startline = int(self.object.source.split(":")[1])

        for i, line in enumerate(self.object.desc, startline):
            self.add_line(line, sourcename, i)

        # add additional content (e.g. from document), if present
        if more_content:
            for line, src in zip(more_content.data, more_content.items):
                self.add_line(line, src[0], src[1])

    def filter_members(
        self,
        members: list[tuple[str, Any]],
        want_all: bool
    ) -> list[tuple[str, Any, bool]]:
        return [(x[0], x[1], False) for x in members]

    def get_object_members(
        self,
        want_all: bool
    ) -> tuple[bool, list[tuple[str, Any]]]:
        ret: list[tuple[str, str]] = []

        if self.options.source:
            ret.append(('__source', self.real_modname))

        return False, ret

    def document_members(self, all_members: bool = False) -> None:
        want_all = (all_members or
                    self.options.inherited_members)
        # find out which members are documentable
        members_check_module, members = self.get_object_members(want_all)

        # document non-skipped members
        memberdocumenters: list[tuple[Documenter, bool]] = []
        for (mname, member, isattr) in self.filter_members(members, want_all):
            classes = [cls for cls in self.documenters.values()
                       if cls.can_document_member(member, mname, isattr, self)]
            if not classes:
                # don't know how to document this member
                continue
            # prefer the documenter with the highest priority
            classes.sort(key=lambda cls: cls.priority)
            # give explicitly separated module name, so that members
            # of inner classes can be documented
            full_mname = self.real_modname + '::' + mname
            documenter = classes[-1](self.directive, full_mname, self.indent)
            memberdocumenters.append((documenter, isattr))

        member_order = self.options.member_order or self.config.autodoc_member_order
        memberdocumenters = self.sort_members(memberdocumenters, member_order)

        for documenter, isattr in memberdocumenters:
            documenter.generate(
                all_members=True, real_modname=self.real_modname,
                check_module=members_check_module and not isattr)

    def generate(
        self,
        more_content: Any | None = None,
        real_modname: str | None = None,
        check_module: bool = False,
        all_members: bool = False
    ) -> None:
        if not self.parse_name():
            # need a cell lib to import from
            logger.warning(
                f"don't know which cell lib to import for autodocumenting {self.name}",
                type = 'cellref'
            )
            return

        if not self.import_object():
            logger.warning(
                f"unable to load {self.name}",
                type = 'cellref'
            )
            return

        # check __module__ of object (for members not given explicitly)
        # if check_module:
        #     if not self.check_module():
        #         return

        sourcename = self.get_sourcename()
        self.add_line('', sourcename)

        # format the object's signature, if any
        try:
            sig = self.format_signature()
        except Exception as exc:
            logger.warning(('error while formatting signature for %s: %s'),
                           self.fullname, exc, type='cellref')
            return

        # generate the directive header and options, if applicable
        self.add_directive_header(sig)
        self.add_line('', sourcename)

        # e.g. the module directive doesn't have content
        self.indent += self.content_indent

        # add all content (from docstrings, attribute docs etc.)
        self.add_content(more_content)

        # document members, if possible
        self.document_members(all_members)

class YosysCellSourceDocumenter(YosysCellDocumenter):
    objtype = 'cellsource'
    priority = 20

    @classmethod
    def can_document_member(
        cls,
        member: Any,
        membername: str,
        isattr: bool,
        parent: Any
    ) -> bool:
        sourcename = str(member).split(":")[0]
        if not sourcename.endswith(".v"):
            return False
        if membername != "__source":
            return False
        if isinstance(parent, YosysCellDocumenter):
            return True
        return False
    
    def add_directive_header(self, sig: str) -> None:
        domain = getattr(self, 'domain', 'cell')
        directive = getattr(self, 'directivetype', 'source')
        name = self.format_name()
        sourcename = self.get_sourcename()
        cell = self.object

        # cell definition
        self.add_line(f'.. {domain}:{directive}:: {name}', sourcename)

        if self.options.linenos:
            self.add_line(f'   :source: {cell.source.split(":")[0]}', sourcename)
        else:
            self.add_line(f'   :source: {cell.source}', sourcename)
        self.add_line(f'   :language: verilog', sourcename)

        if self.options.linenos:
            startline = int(self.object.source.split(":")[1])
            self.add_line(f'   :lineno-start: {startline}', sourcename)

        if self.options.noindex:
            self.add_line('   :noindex:', sourcename)
    
    def add_content(self, more_content: Any | None) -> None:
        # set sourcename and add content from attribute documentation
        sourcename = self.get_sourcename()
        startline = int(self.object.source.split(":")[1])

        for i, line in enumerate(self.object.code, startline-1):
            self.add_line(line, sourcename, i)

        # add additional content (e.g. from document), if present
        if more_content:
            for line, src in zip(more_content.data, more_content.items):
                self.add_line(line, src[0], src[1])

    def get_object_members(
        self,
        want_all: bool
    ) -> tuple[bool, list[tuple[str, Any]]]:
        return False, []

def setup(app: Sphinx) -> dict[str, Any]:
    app.add_config_value('cells_loc', False, 'html', [Path, PosixPath, WindowsPath])
    app.setup_extension('sphinx.ext.autodoc')
    app.add_autodocumenter(YosysCellDocumenter)
    app.add_autodocumenter(YosysCellSourceDocumenter)
    return {
        'version': '1',
        'parallel_read_safe': True,
    }
