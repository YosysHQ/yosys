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

# cmd signature
cmd_ext_sig_re = re.compile(
    r'''^ ([\w$._]+?)            # module name
          (?:\.([\w_]+))?        # optional: thing name
          (::[\w_]+)?            #           attribute
          \s* $                  # and nothing more
          ''', re.VERBOSE)

@dataclass
class YosysCmdUsage:
    signature: str
    description: str
    options: list[tuple[str,str]]
    postscript: str

class YosysCmd:
    name: str
    title: str
    content: list[str]
    usages: list[YosysCmdUsage]
    experimental_flag: bool

    def __init__(
            self,
            name:str = "", title:str = "",
            content: list[str] = [],
            usages: list[dict[str]] = [],
            experimental_flag: bool = False
    ) -> None:
        self.name = name
        self.title = title
        self.content = content
        self.usages = [YosysCmdUsage(**u) for u in usages]
        self.experimental_flag = experimental_flag

    @property
    def source_file(self) -> str:
        return ""

    @property
    def source_line(self) -> int:
        return 0
    
class YosysCmdGroupDocumenter(Documenter):
    objtype = 'cmdgroup'
    priority = 10
    object: tuple[str, list[str]]
    lib_key = 'groups'

    option_spec = {
        'caption': autodoc.annotation_option,
        'members': autodoc.members_option,
        'source': autodoc.bool_option,
        'linenos': autodoc.bool_option,
    }

    __cmd_lib: dict[str, list[str] | dict[str]] | None = None
    @property
    def cmd_lib(self) -> dict[str, list[str] | dict[str]]:
        if not self.__cmd_lib:
            self.__cmd_lib = {}
            cmds_obj: dict[str, dict[str, list[str] | dict[str]]]
            try:
                with open(self.config.cmds_json, "r") as f:
                    cmds_obj = json.loads(f.read())
            except FileNotFoundError:
                logger.warning(
                    f"unable to find cmd lib at {self.config.cmds_json}",
                    type = 'cmdref',
                    subtype = 'cmd_lib'
                )
            else:
                for (name, obj) in cmds_obj.get(self.lib_key, {}).items():
                    self.__cmd_lib[name] = obj
        return self.__cmd_lib
    
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
        # get cmd
        try:
            self.object = (self.modname, self.cmd_lib[self.modname])
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
        domain = getattr(self, 'domain', 'cmd')
        directive = getattr(self, 'directivetype', 'group')
        name = self.format_name()
        sourcename = self.get_sourcename()
        cmd_list = self.object

        # cmd definition
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
                                   type='cmdref')

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
            # need a cmd lib to import from
            logger.warning(
                f"don't know which cmd lib to import for autodocumenting {self.name}",
                type = 'cmdref'
            )
            return

        if not self.import_object():
            logger.warning(
                f"unable to load {self.name} with {type(self)}",
                type = 'cmdref'
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
                           self.fullname, exc, type='cmdref')
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

class YosysCmdDocumenter(YosysCmdGroupDocumenter):
    objtype = 'cmd'
    priority = 15
    object: YosysCmd
    lib_key = 'cmds'

    @classmethod
    def can_document_member(
        cls,
        member: Any,
        membername: str,
        isattr: bool,
        parent: Any
    ) -> bool:
        if membername.startswith('$'):
            return False
        return isinstance(parent, YosysCmdGroupDocumenter)

    def parse_name(self) -> bool:
        try:
            matched = cmd_ext_sig_re.match(self.name)
            modname, thing, attribute = matched.groups()
        except AttributeError:
            logger.warning(('invalid signature for auto%s (%r)') % (self.objtype, self.name),
                           type='cmdref')
            return False

        self.modname = modname
        self.attribute = attribute or ''
        self.fullname = ((self.modname) + (thing or ''))

        return True

    def import_object(self, raiseerror: bool = False) -> bool:
        if super().import_object(raiseerror):
            self.object = YosysCmd(self.modname, **self.object[1])
            return True
        return False

    def get_sourcename(self) -> str:
        return self.object.source_file
    
    def format_name(self) -> str:
        return self.object.name

    def format_signature(self, **kwargs: Any) -> str:
        return self.fullname + self.attribute

    def add_directive_header(self, sig: str) -> None:
        domain = getattr(self, 'domain', self.objtype)
        directive = getattr(self, 'directivetype', 'def')
        source_name = self.object.source_file
        source_line = self.object.source_line

        # cmd definition
        self.add_line(f'.. {domain}:{directive}:: {sig}', source_name, source_line)

        if self.options.noindex:
            self.add_line('   :noindex:', source_name)
    
    def add_content(self, more_content: Any | None) -> None:
        # set sourcename and add content from attribute documentation
        domain = getattr(self, 'domain', self.objtype)
        source_name = self.object.source_file

        for usage in self.object.usages:
            self.add_line('', source_name)
            if usage.signature:
                self.add_line(f'   .. {domain}:usage:: {self.name}::{usage.signature}', source_name)
                self.add_line('', source_name)
            for line in usage.description.splitlines():
                self.add_line(f'   {line}', source_name)
                self.add_line('', source_name)
            if usage.options:
                self.add_line(f'   .. {domain}:optiongroup:: {self.name}::something', source_name)
                self.add_line('', source_name)
                for opt, desc in usage.options:
                    self.add_line(f'      :option {opt}: {desc}', source_name)
                self.add_line('', source_name)
            for line in usage.postscript.splitlines():
                self.add_line(f'   {line}', source_name)
                self.add_line('', source_name)

        for line in self.object.content:
            if line.startswith('..') and ':: ' in line:
                line = line.replace(':: ', f':: {self.name}::', 1)
            self.add_line(line, source_name)

        # add additional content (e.g. from document), if present
        if more_content:
            for line, src in zip(more_content.data, more_content.items):
                self.add_line(line, src[0], src[1])

        # fields
        self.add_line('\n', source_name)
        field_attrs = ["properties", ]
        for field in field_attrs:
            attr = getattr(self.object, field, [])
            for val in attr:
                self.add_line(f':{field} {val}:', source_name)

    def get_object_members(
        self,
        want_all: bool
    ) -> tuple[bool, list[tuple[str, Any]]]:

        return False, []

class YosysCmdUsageDocumenter(YosysCmdDocumenter):
    objtype = 'cmdusage'
    priority = 20
    object: YosysCmdUsage
    parent: YosysCmd

    def add_directive_header(self, sig: str) -> None:
        domain = getattr(self, 'domain', 'cmd')
        directive = getattr(self, 'directivetype', 'usage')
        name = self.format_name()
        sourcename = self.parent.source_file
        cmd = self.parent

        # cmd definition
        self.add_line(f'.. {domain}:{directive}:: {sig}', sourcename)
        if self.object.signature:
            self.add_line(f'   :usage: {self.object.signature}', sourcename)
        else:
            self.add_line(f'   :noindex:', sourcename)
        # for usage in self.object.signature.splitlines():
        #     self.add_line(f'   :usage: {usage}', sourcename)

        # if self.options.linenos:
        #     self.add_line(f'   :source: {cmd.source.split(":")[0]}', sourcename)
        # else:
        #     self.add_line(f'   :source: {cmd.source}', sourcename)
        # self.add_line(f'   :language: verilog', sourcename)

        if self.options.noindex:
            self.add_line('   :noindex:', sourcename)
    
    def add_content(self, more_content: Any | None) -> None:
        # set sourcename and add content from attribute documentation
        sourcename = self.parent.source_file
        startline = self.parent.source_line

        for line in self.object.description.splitlines():
            self.add_line(line, sourcename)

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
    app.add_config_value('cmds_json', False, 'html', [Path, PosixPath, WindowsPath])
    app.setup_extension('sphinx.ext.autodoc')
    app.add_autodocumenter(YosysCmdGroupDocumenter)
    app.add_autodocumenter(YosysCmdDocumenter)
    return {
        'version': '1',
        'parallel_read_safe': True,
    }
