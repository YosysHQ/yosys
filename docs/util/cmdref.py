# based on https://github.com/ofosos/sphinxrecipes/blob/master/sphinxrecipes/sphinxrecipes.py

from __future__ import annotations

import re
from typing import cast

from docutils import nodes
from docutils.nodes import Node, Element, system_message
from docutils.parsers.rst import directives
from docutils.parsers.rst.states import Inliner
from sphinx.application import Sphinx
from sphinx.domains import Domain, Index
from sphinx.domains.std import StandardDomain
from sphinx.environment import BuildEnvironment
from sphinx.roles import XRefRole
from sphinx.directives import ObjectDescription
from sphinx.directives.code import container_wrapper
from sphinx.util.nodes import make_refnode
from sphinx.util.docfields import Field
from sphinx import addnodes

class TocNode(ObjectDescription):    
    def add_target_and_index(
        self,
        name: str,
        sig: str,
        signode: addnodes.desc_signature
    ) -> None:
        idx = ".".join(name.split("::"))
        signode['ids'].append(idx)

    def _object_hierarchy_parts(self, sig_node: addnodes.desc_signature) -> tuple[str, ...]:
        if 'fullname' not in sig_node:
            return ()

        modname = sig_node.get('module')
        fullname = sig_node['fullname']

        if modname:
            return (modname, *fullname.split('::'))
        else:
            return tuple(fullname.split('::'))

    def _toc_entry_name(self, sig_node: addnodes.desc_signature) -> str:
        if not sig_node.get('_toc_parts'):
            return ''

        config = self.env.app.config
        objtype = sig_node.parent.get('objtype')
        *parents, name = sig_node['_toc_parts']
        if config.toc_object_entries_show_parents == 'domain':
            return sig_node.get('tocname', name)
        if config.toc_object_entries_show_parents == 'hide':
            return name
        if config.toc_object_entries_show_parents == 'all':
            return '.'.join(parents + [name])
        return ''

class CommandNode(TocNode):
    """A custom node that describes a command."""

    name = 'cmd'
    required_arguments = 1

    option_spec = {
        'title': directives.unchanged,
        'tags': directives.unchanged
    }

    def handle_signature(self, sig, signode: addnodes.desc_signature):
        signode['fullname'] = sig
        signode += addnodes.desc_addname(text="yosys> help ")
        signode += addnodes.desc_name(text=sig)
        return signode['fullname']

    def add_target_and_index(self, name_cls, sig, signode):
        idx = type(self).name + '-' + sig
        signode['ids'].append(idx)
        if 'noindex' not in self.options:
            name = "{}.{}.{}".format(self.name, type(self).__name__, sig)
            tagmap = self.env.domaindata[type(self).name]['obj2tag']
            tagmap[name] = list(self.options.get('tags', '').split(' '))
            title = self.options.get('title', sig)
            titlemap = self.env.domaindata[type(self).name]['obj2title']
            titlemap[name] = title
            objs = self.env.domaindata[type(self).name]['objects']
            # (name, sig, typ, docname, anchor, prio)
            objs.append((name,
                         sig,
                         type(self).name,
                         self.env.docname,
                         idx,
                         0))

class PropNode(TocNode):
    name = 'prop'
    fieldname = 'props'

    def handle_signature(self, sig: str, signode: addnodes.desc_signature):
        signode['fullname'] = sig
        signode['tocname'] = tocname = sig.split('::')[-1]
        signode += addnodes.desc_name(text=tocname)
        return signode['fullname']

    def add_target_and_index(
        self,
        name: str,
        sig: str,
        signode: addnodes.desc_signature
    ) -> None:
        idx = ".".join(name.split("::"))
        signode['ids'].append(idx)
        if 'noindex' not in self.options:
            tocname: str = signode.get('tocname', name)
            objs = self.env.domaindata[self.domain]['objects']
            # (name, sig, typ, docname, anchor, prio)
            objs.append((name,
                         tocname,
                         type(self).name,
                         self.env.docname,
                         idx,
                         1))

class CellGroupedField(Field):
    """Custom version of GroupedField which doesn't require content."""
    is_grouped = True
    list_type = nodes.bullet_list

    def __init__(self, name: str, names: tuple[str, ...] = (), label: str = None,
                 rolename: str = None, can_collapse: bool = False) -> None:
        super().__init__(name, names, label, True, rolename)
        self.can_collapse = can_collapse

    def make_field(self, types: dict[str, list[Node]], domain: str,
                   items: tuple, env: BuildEnvironment = None,
                   inliner: Inliner = None, location: Node = None) -> nodes.field:
        fieldname = nodes.field_name('', self.label)
        listnode = self.list_type()
        for fieldarg, content in items:
            par = nodes.paragraph()
            if fieldarg:
                par.extend(self.make_xrefs(self.rolename, domain,
                                           fieldarg, nodes.Text,
                                           env=env, inliner=inliner, location=location))

            if len(content) == 1 and (
                    isinstance(content[0], nodes.Text) or
                    (isinstance(content[0], nodes.inline) and len(content[0]) == 1 and
                    isinstance(content[0][0], nodes.Text))):
                par += nodes.Text(' -- ')
                par += content
            listnode += nodes.list_item('', par)

        if len(items) == 1 and self.can_collapse:
            list_item = cast(nodes.list_item, listnode[0])
            fieldbody = nodes.field_body('', list_item[0])
            return nodes.field('', fieldname, fieldbody)

        fieldbody = nodes.field_body('', listnode)
        return nodes.field('', fieldname, fieldbody)

class CellNode(TocNode):
    """A custom node that describes an internal cell."""

    name = 'cell'

    option_spec = {
        'title': directives.unchanged,
        'ports': directives.unchanged,
        'properties': directives.unchanged,
    }

    doc_field_types = [
        CellGroupedField('props', label='Properties', rolename='prop',
                       names=('properties', 'property', 'tag', 'tags'),
                       can_collapse=True),
    ]

    def handle_signature(self, sig: str, signode: addnodes.desc_signature):
        signode['fullname'] = sig
        signode['tocname'] = tocname = sig.split('::')[-1]
        signode += addnodes.desc_addname(text="yosys> help ")
        signode += addnodes.desc_name(text=tocname)
        return signode['fullname']

    def add_target_and_index(
        self,
        name: str,
        sig: str,
        signode: addnodes.desc_signature
    ) -> None:
        idx = ".".join(name.split("::"))
        signode['ids'].append(idx)
        if 'noindex' not in self.options:
            tocname: str = signode.get('tocname', name)
            title: str = self.options.get('title', sig)
            titlemap = self.env.domaindata[self.domain]['obj2title']
            titlemap[name] = title
            props = self.options.get('properties', '')
            if props:
                propmap = self.env.domaindata[self.domain]['obj2prop']
                propmap[name] = props.split(' ')
            objs = self.env.domaindata[self.domain]['objects']
            # (name, sig, typ, docname, anchor, prio)
            objs.append((name,
                         tocname,
                         type(self).name,
                         self.env.docname,
                         idx,
                         0))
            
    def transform_content(self, contentnode: addnodes.desc_content) -> None:
        # Add the cell title to the body
        if 'title' in self.options:
            titlenode = nodes.paragraph()
            titlenode += nodes.strong()
            titlenode[-1] += nodes.Text(self.options['title'])
            contentnode.insert(0, titlenode)

class CellSourceNode(TocNode):
    """A custom code block for including cell source."""

    name = 'cellsource'

    option_spec = {
        "source": directives.unchanged_required,
        "language": directives.unchanged_required,
        'lineno-start': int,
    }

    def handle_signature(
        self,
        sig,
        signode: addnodes.desc_signature
    ) -> str:
        language = self.options.get('language')
        signode['fullname'] = sig
        signode['tocname'] = f"{sig.split('::')[-2]} {language}"
        signode += addnodes.desc_name(text="Simulation model")
        signode += addnodes.desc_sig_space()
        signode += addnodes.desc_addname(text=f'({language})')
        return signode['fullname']

    def run(self) -> list[Node]:
        """Override run to parse content as a code block"""
        if ':' in self.name:
            self.domain, self.objtype = self.name.split(':', 1)
        else:
            self.domain, self.objtype = '', self.name
        self.indexnode = addnodes.index(entries=[])

        node = addnodes.desc()
        node.document = self.state.document
        source, line = self.get_source_info()
        if line is not None:
            line -= 1
        self.state.document.note_source(source, line)
        node['domain'] = self.domain
        # 'desctype' is a backwards compatible attribute
        node['objtype'] = node['desctype'] = self.objtype
        node['noindex'] = noindex = ('noindex' in self.options)
        node['noindexentry'] = ('noindexentry' in self.options)
        node['nocontentsentry'] = ('nocontentsentry' in self.options)
        if self.domain:
            node['classes'].append(self.domain)
        node['classes'].append(node['objtype'])

        self.names = []
        signatures = self.get_signatures()
        for sig in signatures:
            # add a signature node for each signature in the current unit
            # and add a reference target for it
            signode = addnodes.desc_signature(sig, '')
            self.set_source_info(signode)
            node.append(signode)
            try:
                # name can also be a tuple, e.g. (classname, objname);
                # this is strictly domain-specific (i.e. no assumptions may
                # be made in this base class)
                name = self.handle_signature(sig, signode)
            except ValueError:
                # signature parsing failed
                signode.clear()
                signode += addnodes.desc_name(sig, sig)
                continue  # we don't want an index entry here
            finally:
                # Private attributes for ToC generation. Will be modified or removed
                # without notice.
                if self.env.app.config.toc_object_entries:
                    signode['_toc_parts'] = self._object_hierarchy_parts(signode)
                    signode['_toc_name'] = self._toc_entry_name(signode)
                else:
                    signode['_toc_parts'] = ()
                    signode['_toc_name'] = ''
            if name not in self.names:
                self.names.append(name)
                if not noindex:
                    # only add target and index entry if this is the first
                    # description of the object with this name in this desc block
                    self.add_target_and_index(name, sig, signode)
        
        # handle code
        code = '\n'.join(self.content)
        literal: Element = nodes.literal_block(code, code)
        if 'lineno-start' in self.options:
            literal['linenos'] = True
            literal['highlight_args'] = {
                'linenostart': self.options['lineno-start']
            }
        literal['classes'] += self.options.get('class', [])
        literal['language'] = self.options.get('language')
        literal = container_wrapper(self, literal, self.options.get('source'))

        return [self.indexnode, node, literal]

class CellGroupNode(TocNode):
    name = 'cellgroup'

    option_spec = {
        'caption': directives.unchanged,
    }

    def add_target_and_index(self, name: str, sig: str, signode: addnodes.desc_signature) -> None:
        if self.options.get('caption', ''):
            super().add_target_and_index(name, sig, signode)

    def handle_signature(
        self,
        sig,
        signode: addnodes.desc_signature
    ) -> str:
        signode['fullname'] = fullname = sig
        caption = self.options.get("caption", fullname)
        if caption:
            signode['tocname'] = caption
            signode += addnodes.desc_name(text=caption)
        return fullname

class TagIndex(Index):
    """A custom directive that creates a tag matrix."""
    
    name = 'tag'
    localname = 'Tag Index'
    shortname = 'Tag'
    
    def __init__(self, *args, **kwargs):
        super(TagIndex, self).__init__(*args, **kwargs)

    def generate(self, docnames=None):
        """Return entries for the index given by *name*.  If *docnames* is
        given, restrict to entries referring to these docnames.
        The return value is a tuple of ``(content, collapse)``, where
        * collapse* is a boolean that determines if sub-entries should
        start collapsed (for output formats that support collapsing
        sub-entries).
        *content* is a sequence of ``(letter, entries)`` tuples, where *letter*
        is the "heading" for the given *entries*, usually the starting letter.
        *entries* is a sequence of single entries, where a single entry is a
        sequence ``[name, subtype, docname, anchor, extra, qualifier, descr]``.
        The items in this sequence have the following meaning:
        - `name` -- the name of the index entry to be displayed
        - `subtype` -- sub-entry related type:
          0 -- normal entry
          1 -- entry with sub-entries
          2 -- sub-entry
        - `docname` -- docname where the entry is located
        - `anchor` -- anchor for the entry within `docname`
        - `extra` -- extra info for the entry
        - `qualifier` -- qualifier for the description
        - `descr` -- description for the entry
        Qualifier and description are not rendered e.g. in LaTeX output.
        """

        content = {}

        objs = {name: (dispname, typ, docname, anchor)
                for name, dispname, typ, docname, anchor, prio
                in self.domain.get_objects()}
        
        tmap = {}
        tags = self.domain.data[f'obj2{self.name}']
        for name, tags in tags.items():
            for tag in tags:
                tmap.setdefault(tag,[])
                tmap[tag].append(name)
            
        for tag in tmap.keys():
            lis = content.setdefault(tag, [])
            objlis = tmap[tag]
            for objname in objlis:
                dispname, typ, docname, anchor = objs[objname]
                lis.append((
                    dispname, 0, docname,
                    anchor,
                    docname, '', typ
                ))
        ret = [(k, v) for k, v in sorted(content.items())]

        return (ret, True)

class CommandIndex(Index):    
    name = 'cmd'
    localname = 'Command Reference'
    shortname = 'Command'
    
    def __init__(self, *args, **kwargs):
        super(CommandIndex, self).__init__(*args, **kwargs)

    def generate(self, docnames=None):
        """Return entries for the index given by *name*.  If *docnames* is
        given, restrict to entries referring to these docnames.
        The return value is a tuple of ``(content, collapse)``, where
        * collapse* is a boolean that determines if sub-entries should
        start collapsed (for output formats that support collapsing
        sub-entries).
        *content* is a sequence of ``(letter, entries)`` tuples, where *letter*
        is the "heading" for the given *entries*, usually the starting letter.
        *entries* is a sequence of single entries, where a single entry is a
        sequence ``[name, subtype, docname, anchor, extra, qualifier, descr]``.
        The items in this sequence have the following meaning:
        - `name` -- the name of the index entry to be displayed
        - `subtype` -- sub-entry related type:
          0 -- normal entry
          1 -- entry with sub-entries
          2 -- sub-entry
        - `docname` -- docname where the entry is located
        - `anchor` -- anchor for the entry within `docname`
        - `extra` -- extra info for the entry
        - `qualifier` -- qualifier for the description
        - `descr` -- description for the entry
        Qualifier and description are not rendered e.g. in LaTeX output.
        """

        content = {}
        items = ((name, dispname, typ, docname, anchor)
                 for name, dispname, typ, docname, anchor, prio
                 in self.domain.get_objects()
                 if typ == self.name)
        items = sorted(items, key=lambda item: item[0])
        for name, dispname, typ, docname, anchor in items:
            lis = content.setdefault(self.shortname, [])
            lis.append((
                dispname, 0, docname,
                anchor,
                '', '', typ
            ))
        ret = [(k, v) for k, v in sorted(content.items())]

        return (ret, True)

class CellIndex(CommandIndex):
    name = 'cell'
    localname = 'Internal cell reference'
    shortname = 'Internal cell'

class PropIndex(TagIndex):
    """A custom directive that creates a properties matrix."""
    
    name = 'prop'
    localname = 'Property Index'
    shortname = 'Prop'
    fieldname = 'props'

    def generate(self, docnames=None):
        content = {}

        cells = {name: (dispname, docname, anchor)
                for name, dispname, typ, docname, anchor, _
                in self.domain.get_objects()
                if typ == 'cell'}
        props = {name: (dispname, docname, anchor)
                for name, dispname, typ, docname, anchor, _
                in self.domain.get_objects()
                if typ == 'prop'}

        tmap: dict[str, list[str]] = {}
        tags: dict[str, list[str]] = self.domain.data[f'obj2{self.name}']
        for name, tags in tags.items():
            for tag in tags:
                tmap.setdefault(tag,[])
                tmap[tag].append(name)

        for tag in sorted(tmap.keys()):
            test = re.match(r'^(\w+[_-])', tag)
            tag_prefix = test.group(1)
            lis = content.setdefault(tag_prefix, [])
            try:
                dispname, docname, anchor = props[tag]
            except KeyError:
                dispname = tag
                docname = anchor = ''
            lis.append((
                dispname, 1, docname,
                anchor,
                '', '', docname or 'unavailable'
            ))
            objlis = tmap[tag]
            for objname in sorted(objlis):
                dispname, docname, anchor = cells[objname]
                lis.append((
                    dispname, 2, docname,
                    anchor,
                    '', '', docname
                ))
        ret = [(k, v) for k, v in sorted(content.items())]

        return (ret, True)

class CommandDomain(Domain):
    name = 'cmd'
    label = 'Yosys commands'

    roles = {
        'ref': XRefRole()
    }

    directives = {
        'def': CommandNode,
    }

    indices = {
        CommandIndex,
        TagIndex
    }

    initial_data = {
        'objects': [],      # object list
        'obj2tag': {},      # name -> tags
        'obj2title': {},    # name -> title
    }

    def get_full_qualified_name(self, node):
        """Return full qualified name for a given node"""
        return "{}.{}.{}".format(type(self).name,
                                 type(node).__name__,
                                 node.arguments[0])

    def get_objects(self):
        for obj in self.data['objects']:
            yield(obj)

    def resolve_xref(self, env, fromdocname, builder, typ,
                     target, node, contnode):
        
        match = [(docname, anchor, name)
                 for name, sig, typ, docname, anchor, prio
                 in self.get_objects() if sig == target]

        if match:
            todocname = match[0][0]
            targ = match[0][1]
            qual_name = match[0][2]
            title = self.data['obj2title'].get(qual_name, targ)
            
            return make_refnode(builder,fromdocname,todocname,
                                targ, contnode, title)
        else:
            print(f"Missing ref for {target} in {fromdocname} ")
            return None
        
class CellDomain(CommandDomain):
    name = 'cell'
    label = 'Yosys internal cells'

    roles = CommandDomain.roles.copy()
    roles.update({
        'prop': XRefRole()
    })

    directives = {
        'def': CellNode,
        'defprop': PropNode,
        'source': CellSourceNode,
        'group': CellGroupNode,
    }

    indices = {
        CellIndex,
        PropIndex
    }

    initial_data = {
        'objects': [],      # object list
        'obj2prop': {},     # name -> properties
        'obj2title': {},    # name -> title
    }

    def get_objects(self):
        for obj in self.data['objects']:
            yield(obj)

def autoref(name, rawtext: str, text: str, lineno, inliner: Inliner,
            options=None, content=None):
    role = 'cell:ref' if text[0] == '$' else 'cmd:ref'
    if text.startswith("help ") and text.count(' ') == 1:
        _, cmd = text.split(' ', 1)
        text = f'{text} <{cmd}>'
    return inliner.interpreted(rawtext, text, role, lineno)

def setup(app: Sphinx):
    app.add_domain(CommandDomain)
    app.add_domain(CellDomain)

    StandardDomain.initial_data['labels']['commandindex'] =\
        ('cmd-cmd', '', 'Command Reference')
    StandardDomain.initial_data['labels']['tagindex'] =\
        ('cmd-tag', '', 'Tag Index')
    StandardDomain.initial_data['labels']['cellindex'] =\
        ('cell-cell', '', 'Internal cell reference')
    StandardDomain.initial_data['labels']['propindex'] =\
        ('cell-prop', '', 'Property Index')

    StandardDomain.initial_data['anonlabels']['commandindex'] =\
        ('cmd-cmd', '')
    StandardDomain.initial_data['anonlabels']['tagindex'] =\
        ('cmd-tag', '')
    StandardDomain.initial_data['anonlabels']['cellindex'] =\
        ('cell-cell', '')
    StandardDomain.initial_data['anonlabels']['propindex'] =\
        ('cell-prop', '')

    app.add_role('autoref', autoref)
    
    return {'version': '0.2'}
