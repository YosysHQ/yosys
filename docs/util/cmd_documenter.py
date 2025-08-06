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
    r'''^ ([\w/]+::)?            # optional group
          ([\w$._]+?)            # module name
          (?:\.([\w_]+))?        # optional: thing name
          (::[\w_]+)?            #           attribute
          \s* $                  # and nothing more
          ''', re.VERBOSE)

class YosysCmdContentListing:
    type: str
    body: str
    source_file: str
    source_line: int
    options: dict[str, str]
    content: list[YosysCmdContentListing]

    def __init__(
            self,
            type: str = "",
            body: str = "",
            source_file: str = "unknown",
            source_line: int = 0,
            options: dict[str, str] = {},
            content: list[dict[str]] = [],
    ):
        self.type = type
        self.body = body
        self.source_file = source_file
        self.source_line = source_line
        self.options = options
        self.content = [YosysCmdContentListing(**c) for c in content]

class YosysCmd:
    name: str
    title: str
    content: list[YosysCmdContentListing]
    group: str
    source_file: str
    source_line: int
    source_func: str
    experimental_flag: bool
    internal_flag: bool

    def __init__(
            self,
            name:str = "", title:str = "",
            content: list[dict[str]] = [],
            group: str = 'unknown',
            source_file: str = "",
            source_line: int = 0,
            source_func: str = "",
            experimental_flag: bool = False,
            internal_flag: bool = False,
    ) -> None:
        self.name = name
        self.title = title
        self.content = [YosysCmdContentListing(**c) for c in content]
        self.group = group
        self.source_file = source_file
        self.source_line = source_line
        self.source_func = source_func
        self.experimental_flag = experimental_flag
        self.internal_flag = internal_flag
    
class YosysCmdGroupDocumenter(Documenter):
    objtype = 'cmdgroup'
    priority = 10
    object: tuple[str, list[str]]
    lib_key = 'groups'

    option_spec = Documenter.option_spec.copy()
    option_spec.update({
        'caption': autodoc.annotation_option,
        'members': autodoc.members_option,
        'source': autodoc.bool_option,
        'linenos': autodoc.bool_option,
    })

    __cmd_lib: dict[str, list[str] | dict[str]] | None = None
    @property
    def cmd_lib(self) -> dict[str, list[str] | dict[str]]:
        if not self.__cmd_lib:
            self.__cmd_lib = {}
            cmds_obj: dict[str, dict[str, dict[str]]]
            try:
                with open(self.config.cmds_json, "r") as f:
                    cmds_obj = json.loads(f.read())
            except FileNotFoundError:
                logger.warning(
                    f"unable to find cmd lib at {self.config.cmds_json}",
                    type = 'cmdref',
                    subtype = 'cmd_lib'
                )
                cmds_obj = {}
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
        pass
    
    def add_content(self, more_content: Any | None) -> None:
        pass

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

        sourcename = self.get_sourcename()

        imported_object = self.import_object();
        if self.lib_key == 'groups' and self.name == 'unknown':
            if imported_object:
                logger.warning(f"Found commands assigned to group {self.name}: {[x[0] for x in self.object]}", type='cmdref')
            else:
                return
        elif not imported_object:
            log_msg = f"unable to load {self.name} with {type(self)}"
            if self.lib_key == 'groups':
                logger.info(log_msg, type = 'cmdref')
                self.add_line(f'.. warning:: No commands found for group {self.name!r}', sourcename)
                self.add_line('', sourcename)
                self.add_line('   Documentation may have been built without ``source_location`` support.', sourcename)
                self.add_line('   Try check :doc:`/cmd/index_other`.', sourcename)
            else:
                logger.warning(log_msg, type = 'cmdref')
            return

        # check __module__ of object (for members not given explicitly)
        # if check_module:
        #     if not self.check_module():
        #         return

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
            group, modname, thing, attribute = matched.groups()
        except AttributeError:
            logger.warning(('invalid signature for auto%s (%r)') % (self.objtype, self.name),
                           type='cmdref')
            return False

        self.modname = modname
        self.groupname = group or ''
        self.attribute = attribute or ''
        self.fullname = ((self.modname) + (thing or ''))

        return True

    def import_object(self, raiseerror: bool = False) -> bool:
        if super().import_object(raiseerror):
            self.object = YosysCmd(self.modname, **self.object[1])
            return True
        return False

    def get_sourcename(self) -> str:
        try:
            return self.object.source_file
        except AttributeError:
            return super().get_sourcename()
    
    def format_name(self) -> str:
        return self.object.name

    def format_signature(self, **kwargs: Any) -> str:
        return self.fullname + self.attribute

    def add_directive_header(self, sig: str) -> None:
        domain = getattr(self, 'domain', self.objtype)
        directive = getattr(self, 'directivetype', 'def')
        source_name = self.object.source_file
        source_line = self.object.source_line

        title = f'{self.object.name} - {self.object.title}'
        self.add_line(title, source_name, source_line)
        self.add_line('#' * len(title), source_name, source_line)

        # cmd definition
        self.add_line(f'.. {domain}:{directive}:: {sig}', source_name, source_line)
        if self.object.title:
            self.add_line(f'   :title: {self.object.title}', source_name, source_line)

        if self.options.noindex:
            self.add_line('   :noindex:', source_name)
    
    def add_content(self, more_content: Any | None) -> None:
        # set sourcename and add content from attribute documentation
        domain = getattr(self, 'domain', self.objtype)
        source_name = self.object.source_file
        source_line = self.object.source_line

        if self.object.experimental_flag:
            self.add_line(f'.. warning:: This command is experimental', source_name, source_line)
            self.add_line('\n', source_name)

        if self.object.internal_flag:
            self.add_line(f'.. warning:: This command is intended for internal developer use only', source_name, source_line)
            self.add_line('\n', source_name)

        def render(content_list: YosysCmdContentListing, indent: int=0):
            content_source = content_list.source_file or source_name
            indent_str = '   '*indent
            if content_list.type == 'usage':
                if content_list.body:
                    self.add_line(f'{indent_str}.. {domain}:{content_list.type}:: {self.name}::{content_list.body}', content_source)
                else:
                    self.add_line(f'{indent_str}.. {domain}:{content_list.type}:: {self.name}::', content_source)
                    self.add_line(f'{indent_str}   :noindex:', source_name)
                self.add_line('', source_name)
            elif content_list.type == 'option':
                self.add_line(f'{indent_str}:{content_list.type} {content_list.body}:', content_source)
            elif content_list.type == 'text':
                self.add_line(f'{indent_str}{content_list.body}', content_source)
                self.add_line('', source_name)
            elif content_list.type == 'code':
                language_str = content_list.options.get('language', '')
                self.add_line(f'{indent_str}.. code-block:: {language_str}', source_name)
                self.add_line('', source_name)
                for body_line in content_list.body.splitlines():
                    self.add_line(f'{indent_str}   {body_line}', content_source)
                self.add_line('', source_name)
            else:
                logger.warning(f"unknown content type '{content_list.type}'")
            for content in content_list.content:
                render(content, indent+1)

        for content in self.object.content:
            render(content)

        if self.get_sourcename() != 'unknown':
            self.add_line('\n', source_name)
            self.add_line(f'.. note:: Help text automatically generated from :file:`{source_name}:{source_line}`', source_name)

        # add additional content (e.g. from document), if present
        if more_content:
            for line, src in zip(more_content.data, more_content.items):
                self.add_line(line, src[0], src[1])

    def get_object_members(
        self,
        want_all: bool
    ) -> tuple[bool, list[tuple[str, Any]]]:

        return False, []

class YosysCmdRstDocumenter(YosysCmdDocumenter):
    objtype = 'cmd_rst'
    priority = 0

    @classmethod
    def can_document_member(cls, *args) -> bool:
        return False

    def add_directive_header(self, sig):
        source_name = self.object.source_file
        cmd = self.object.name
        self.add_line(f'.. code-block:: rst', source_name)
        self.add_line(f'   :caption: Generated rst for ``.. autocmd:: {cmd}``', source_name)

    def add_content(self, more_content):
        source_name = self.object.source_file
        cmd = self.object.name
        self.domain = 'cmd'
        super().add_directive_header(cmd)
        self.add_line('', source_name)
        self.indent += self.content_indent
        super().add_content(more_content)

def setup(app: Sphinx) -> dict[str, Any]:
    app.add_config_value('cmds_json', False, 'html', [Path, PosixPath, WindowsPath])
    app.setup_extension('sphinx.ext.autodoc')
    app.add_autodocumenter(YosysCmdGroupDocumenter)
    app.add_autodocumenter(YosysCmdDocumenter)
    app.add_autodocumenter(YosysCmdRstDocumenter)
    return {
        'version': '2',
        'parallel_read_safe': True,
    }
