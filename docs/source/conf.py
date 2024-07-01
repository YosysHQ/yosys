#!/usr/bin/env python3
from pathlib import Path
import sys
import os

project = 'YosysHQ Yosys'
author = 'YosysHQ GmbH'
copyright ='2024 YosysHQ GmbH'
yosys_ver = "0.42"

# select HTML theme
html_theme = 'furo-ys'
html_css_files = ['custom.css']

# These folders are copied to the documentation's HTML output
html_static_path = ['_static', "_images"]

# default to no highlight
highlight_language = 'none'

# default single quotes to attempt auto reference, or fallback to code
default_role = 'autoref'

extensions = ['sphinx.ext.autosectionlabel', 'sphinxcontrib.bibtex']

# Ensure that autosectionlabel will produce unique names
autosectionlabel_prefix_document = True
autosectionlabel_maxdepth = 1

# set version
if os.getenv("READTHEDOCS") and os.getenv("READTHEDOCS_VERSION") == "latest":
    release = yosys_ver + "-dev"
else:
    release = yosys_ver

# assign figure numbers
numfig = True

bibtex_bibfiles = ['literature.bib']
latex_elements = {
        'releasename': 'Version',
        'preamble': r'''
\usepackage{lmodern}
\usepackage{comment}

'''
}

# include todos during rewrite
extensions.append('sphinx.ext.todo')
todo_include_todos = False

# custom cmd-ref parsing/linking
sys.path += [os.path.dirname(__file__) + "/../"]
extensions.append('util.cmdref')

# use autodocs
extensions.append('sphinx.ext.autodoc')
extensions.append('util.cellref')
cells_json = Path(__file__).parent / 'generated' / 'cells.json'

from sphinx.application import Sphinx
def setup(app: Sphinx) -> None:
    from util.RtlilLexer import RtlilLexer
    app.add_lexer("RTLIL", RtlilLexer)

    from furo_ys.lexers.YoscryptLexer import YoscryptLexer
    app.add_lexer("yoscrypt", YoscryptLexer)
