#!/usr/bin/env python3
from pathlib import Path
import sys
import os

project = 'YosysHQ Yosys'
author = 'YosysHQ GmbH'
copyright ='2025 YosysHQ GmbH'
yosys_ver = "0.54"

# select HTML theme
html_theme = 'furo-ys'
html_css_files = ['custom.css']
html_theme_options: dict[str] = {
    "source_repository": "https://github.com/YosysHQ/yosys/",
    "source_branch": "main",
    "source_directory": "docs/source/",
}
html_context: dict[str] = {}

# try to fix the readthedocs detection
if os.getenv("READTHEDOCS"):
    html_context.update({
        "READTHEDOCS": True,
        "display_github": True,
        "github_user": "YosysHQ",
        "github_repo": "yosys",
        "slug": "yosys",
    })

# override source_branch if not main
git_slug = os.getenv("READTHEDOCS_VERSION_NAME")
if git_slug not in [None, "latest", "stable"]:
    html_theme_options["source_branch"] = git_slug

# edit only works on branches, not tags
if os.getenv("READTHEDOCS_VERSION_TYPE", "branch") != "branch":
        html_theme_options["top_of_page_buttons"] = ["view"]

# These folders are copied to the documentation's HTML output
html_static_path = ['_static', "_images"]

# default to no highlight
highlight_language = 'none'

# default single quotes to attempt auto reference, or fallback to code
default_role = 'autoref'

extensions = ['sphinx.ext.autosectionlabel', 'sphinxcontrib.bibtex']

if os.getenv("READTHEDOCS"):
    # Use rtds_action if we are building on read the docs and have a github token env var
    if os.getenv("GITHUB_TOKEN"):
        extensions += ['rtds_action']
        rtds_action_github_repo = "YosysHQ/yosys"
        rtds_action_path = "."
        rtds_action_artifact_prefix = "cmd-ref-"
        rtds_action_github_token = os.environ["GITHUB_TOKEN"]
    else:
        # We're on read the docs but have no github token, this is probably a PR preview build
        html_theme_options["announcement"] = 'Missing content? Check <a class="reference internal" href="https://tyrtd--2.org.readthedocs.build/en/2/appendix/building_docs.html#pr-previews-and-limitations">PR preview limitations</a>.'
        html_theme_options["light_css_variables"]["color-announcement-background"] = "var(--color-admonition-title-background--caution)"
        html_theme_options["light_css_variables"]["color-announcement-text"] = "var(--color-content-foreground)"

# Ensure that autosectionlabel will produce unique names
autosectionlabel_prefix_document = True
autosectionlabel_maxdepth = 1

# include todos for previews
extensions.append('sphinx.ext.todo')

# set version
if os.getenv("READTHEDOCS"):
    rtds_version = os.getenv("READTHEDOCS_VERSION")
    if rtds_version == "latest":
        release = yosys_ver + "-dev"
        todo_include_todos = False
    elif rtds_version.startswith("docs"):
        release = rtds_version
        todo_include_todos = True
    else:
        release = yosys_ver
        todo_include_todos = False
elif os.getenv("YOSYS_DOCS_RELEASE") is not None:
    release = yosys_ver
    todo_include_todos = False
else:
    release = yosys_ver
    todo_include_todos = True

# assign figure numbers
numfig = True

bibtex_bibfiles = ['literature.bib']
latex_elements = {
        'releasename': 'Version',
        'preamble': r'''
\pdfinfoomitdate 1
\pdfsuppressptexinfo 1
\pdftrailerid{}
\usepackage{lmodern}
\usepackage{comment}

'''
}

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

    try:
        from furo_ys.lexers.YoscryptLexer import YoscryptLexer
        app.add_lexer("yoscrypt", YoscryptLexer)
    except ModuleNotFoundError:
        from pygments.lexers.special import TextLexer
        app.add_lexer("yoscrypt", TextLexer)
