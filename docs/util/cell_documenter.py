#!/usr/bin/env python3
from __future__ import annotations

from dataclasses import dataclass
import json
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
    r'''^ ([^:\s]+::)?           # optional group or file name
          ([\w$._]+?)            # module name
          (?:\.([\w_]+))?        # optional: thing name
          (::[\w_]+)?            #           attribute
          \s* $                  # and nothing more
          ''', re.VERBOSE)

@dataclass
class YosysCell:
    name: str
    title: str
    ports: str
    source: str
    desc: str
    code: str
    inputs: list[str]
    outputs: list[str]
    properties: list[str]
    
class YosysCellGroupDocumenter(Documenter):
    objtype = 'cellgroup'
    priority = 10
    object: tuple[str, list[str]]
    lib_key = 'groups'

    option_spec = {
        'caption': autodoc.annotation_option,
        'members': autodoc.members_option,
        'source': autodoc.bool_option,
        'linenos': autodoc.bool_option,
    }

    __cell_lib: dict[str, list[str] | dict[str]] | None = None
    @property
    def cell_lib(self) -> dict[str, list[str] | dict[str]]:
        if not self.__cell_lib:
            self.__cell_lib = {}
            cells_obj: dict[str, dict[str, list[str] | dict[str]]]
            try:
                with open(self.config.cells_json, "r") as f:
                    cells_obj = json.loads(f.read())
            except FileNotFoundError:
                logger.warning(
                    f"unable to find cell lib at {self.config.cells_json}",
                    type = 'cellref',
                    subtype = 'cell_lib'
                )
            else:
                for (name, obj) in cells_obj.get(self.lib_key, {}).items():
                    self.__cell_lib[name] = obj
        return self.__cell_lib
    
    @classmethod
    def can_document_member(
        cls,
        member: Any,
        membername: str,
        isattr: bool,
        parent: Any
    ) -> bool:
        return False

    def parse_name(self) -> bool:
        if not self.options.caption:
            self.content_indent = ''
        self.fullname = self.modname = self.name
        return True
    
    def import_object(self, raiseerror: bool = False) -> bool:
        # get cell
        try:
            self.object = (self.modname, self.cell_lib[self.modname])
        except KeyError:
            if raiseerror:
                raise
            return False

        self.real_modname = self.modname
        return True
    
    def get_sourcename(self) -> str:
        return self.env.doc2path(self.env.docname)
    
    def format_name(self) -> str:
        return self.options.caption or ''

    def format_signature(self, **kwargs: Any) -> str:
        return self.modname
    
    def add_directive_header(self, sig: str) -> None:
        domain = getattr(self, 'domain', 'cell')
        directive = getattr(self, 'directivetype', 'group')
        name = self.format_name()
        sourcename = self.get_sourcename()
        cell_list = self.object

        # cell definition
        self.add_line(f'.. {domain}:{directive}:: {sig}', sourcename)
        self.add_line(f'   :caption: {name}', sourcename)

        if self.options.noindex:
            self.add_line('   :noindex:', sourcename)
    
    def add_content(self, more_content: Any | None) -> None:
        # groups have no native content
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

        if want_all:
            for member in self.object[1]:
                ret.append((member, self.modname))
        else:
            memberlist = self.options.members or []
            for name in memberlist:
                if name in self.object:
                    ret.append((name, self.modname))
                else:
                    logger.warning(('unknown module mentioned in :members: option: '
                                    f'group {self.modname}, module {name}'),
                                   type='cellref')

        return False, ret

    def document_members(self, all_members: bool = False) -> None:
        want_all = (all_members or
                    self.options.inherited_members or
                    self.options.members is autodoc.ALL)
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
            full_mname = self.format_signature() + '::' + mname
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

class YosysCellDocumenter(YosysCellGroupDocumenter):
    objtype = 'cell'
    priority = 15
    object: YosysCell
    lib_key = 'cells'

    @classmethod
    def can_document_member(
        cls,
        member: Any,
        membername: str,
        isattr: bool,
        parent: Any
    ) -> bool:
        if membername == "__source":
            return False
        if not membername.startswith('$'):
            return False
        return isinstance(parent, YosysCellGroupDocumenter)

    def parse_name(self) -> bool:
        try:
            matched = cell_ext_sig_re.match(self.name)
            group, modname, thing, attribute = matched.groups()
        except AttributeError:
            logger.warning(('invalid signature for auto%s (%r)') % (self.objtype, self.name),
                           type='cellref')
            return False

        self.modname = modname
        self.groupname = group or ''
        self.attribute = attribute or ''
        self.fullname = ((self.modname) + (thing or ''))

        return True
    
    def import_object(self, raiseerror: bool = False) -> bool:
        if super().import_object(raiseerror):
            self.object = YosysCell(self.modname, **self.object[1])
            return True
        return False
    
    def get_sourcename(self) -> str:
        return self.object.source.split(":")[0]
    
    def format_name(self) -> str:
        return self.object.name

    def format_signature(self, **kwargs: Any) -> str:
        return self.groupname + self.fullname + self.attribute
    
    def add_directive_header(self, sig: str) -> None:
        domain = getattr(self, 'domain', self.objtype)
        directive = getattr(self, 'directivetype', 'def')
        name = self.format_name()
        sourcename = self.get_sourcename()
        cell = self.object

        # cell definition
        self.add_line(f'.. {domain}:{directive}:: {sig}', sourcename)

        # options
        opt_attrs = ["title", "properties", ]
        for attr in opt_attrs:
            val = getattr(cell, attr, None)
            if isinstance(val, list):
                val = ' '.join(val)
            if val:
                self.add_line(f'   :{attr}: {val}', sourcename)

        self.add_line('\n', sourcename)

        if self.options.noindex:
            self.add_line('   :noindex:', sourcename)
    
    def add_content(self, more_content: Any | None) -> None:
        # set sourcename and add content from attribute documentation
        sourcename = self.get_sourcename()
        startline = int(self.object.source.split(":")[1])

        for i, line in enumerate(self.object.desc.splitlines(), startline):
            self.add_line(line, sourcename, i)

        # add additional content (e.g. from document), if present
        if more_content:
            for line, src in zip(more_content.data, more_content.items):
                self.add_line(line, src[0], src[1])

        # fields
        self.add_line('\n', sourcename)
        field_attrs = ["properties", ]
        for field in field_attrs:
            attr = getattr(self.object, field, [])
            for val in attr:
                self.add_line(f':{field} {val}:', sourcename)

    def get_object_members(
        self,
        want_all: bool
    ) -> tuple[bool, list[tuple[str, Any]]]:
        ret: list[tuple[str, str]] = []

        if self.options.source:
            ret.append(('__source', self.real_modname))

        return False, ret

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
        self.add_line(f'.. {domain}:{directive}:: {sig}', sourcename)

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

        for i, line in enumerate(self.object.code.splitlines(), startline-1):
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
    app.add_config_value('cells_json', False, 'html', [Path, PosixPath, WindowsPath])
    app.setup_extension('sphinx.ext.autodoc')
    app.add_autodocumenter(YosysCellDocumenter)
    app.add_autodocumenter(YosysCellSourceDocumenter)
    app.add_autodocumenter(YosysCellGroupDocumenter)
    return {
        'version': '1',
        'parallel_read_safe': True,
    }
