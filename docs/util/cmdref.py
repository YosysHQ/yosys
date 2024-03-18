# based on https://github.com/ofosos/sphinxrecipes/blob/master/sphinxrecipes/sphinxrecipes.py
# license:
# Copyright 2019 Mark Meyer
# 
# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:
# 
# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import docutils
from docutils import nodes
import sphinx
from docutils.parsers import rst
from docutils.parsers.rst import directives
from sphinx.domains import Domain, Index
from sphinx.domains.std import StandardDomain
from sphinx.roles import XRefRole
from sphinx.directives import ObjectDescription
from sphinx.util.nodes import make_refnode
from sphinx import addnodes

class CommandNode(ObjectDescription):
    """A custom node that describes a command."""
  
    required_arguments = 1

    option_spec = {
        'title': directives.unchanged_required,
        'tags': directives.unchanged
    }

    def handle_signature(self, sig, signode: addnodes.desc_signature):
        signode += addnodes.desc_addname(text="yosys> help ")
        signode += addnodes.desc_name(text=sig)
        return sig

    def add_target_and_index(self, name_cls, sig, signode):
        signode['ids'].append('cmd' + '-' + sig)
        if 'noindex' not in self.options:
            name = "{}.{}.{}".format('cmd', type(self).__name__, sig)
            tagmap = self.env.domaindata['cmd']['obj2tag']
            tagmap[name] = list(self.options.get('tags', '').split(' '))
            title = self.options.get('title')
            titlemap = self.env.domaindata['cmd']['obj2title']
            titlemap[name] = title
            objs = self.env.domaindata['cmd']['objects']
            objs.append((name,
                         sig,
                         title,
                         self.env.docname,
                         'cmd' + '-' + sig,
                         0))

class TagIndex(Index):
    """A custom directive that creates an tag matrix."""
    
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
        tags = self.domain.data['obj2tag']
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
        re = [(k, v) for k, v in sorted(content.items())]

        return (re, True)


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
                 in self.domain.get_objects())
        items = sorted(items, key=lambda item: item[0])
        for name, dispname, typ, docname, anchor in items:
            lis = content.setdefault('Command', [])
            lis.append((
                dispname, 0, docname,
                anchor,
                '', '', typ
            ))
        re = [(k, v) for k, v in sorted(content.items())]

        return (re, True)


class CommandDomain(Domain):
    name = 'cmd'
    label = 'Command Sample'

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
        return "{}.{}.{}".format('cmd',
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

def setup(app):
    app.add_domain(CommandDomain)

    StandardDomain.initial_data['labels']['commandindex'] =\
        ('cmd-cmd', '', 'Command Reference')
    StandardDomain.initial_data['labels']['tagindex'] =\
        ('cmd-tag', '', 'Tag Index')

    StandardDomain.initial_data['anonlabels']['commandindex'] =\
        ('cmd-cmd', '')
    StandardDomain.initial_data['anonlabels']['tagindex'] =\
        ('cmd-tag', '')
    
    return {'version': '0.1'}
