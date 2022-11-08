#!/usr/bin/env python3
import sys
import os

project = 'YosysHQ Yosys'
author = 'YosysHQ GmbH'
copyright ='2022 YosysHQ GmbH'

# select HTML theme
html_theme = 'press'
html_logo = '../static/logo.png'
html_favicon = '../static/favico.png'
html_css_files = ['yosyshq.css', 'custom.css']
html_sidebars = {'**': ['util/searchbox.html', 'util/sidetoc.html']}

# These folders are copied to the documentation's HTML output
html_static_path = ['../static', "../images"]

# code blocks style 
pygments_style = 'colorful'
highlight_language = 'none'

html_theme_options = {
    'external_links' : [
        ('YosysHQ Docs', 'https://yosyshq.readthedocs.io'),
        ('Blog', 'https://blog.yosyshq.com'),
        ('Website', 'https://www.yosyshq.com'),
    ],
}

extensions = ['sphinx.ext.autosectionlabel', 'sphinxcontrib.bibtex']

# Ensure that autosectionlabel will produce unique names
autosectionlabel_prefix_document = True
autosectionlabel_maxdepth = 1

# assign figure numbers
numfig = True

bibtex_bibfiles = ['literature.bib']

# unused docs
exclude_patterns = [
	"CHAPTER_Eval.rst",
	"appendix/CHAPTER_StateOfTheArt.rst"
]

latex_elements = {
        'preamble': r'''
\usepackage{lmodern}
\usepackage{comment}

'''
}

def setup(sphinx):
	sys.path += [os.path.dirname(__file__) + "/../util"]
	from RtlilLexer import RtlilLexer
	sphinx.add_lexer("RTLIL", RtlilLexer)

	from YoscryptLexer import YoscryptLexer
	sphinx.add_lexer("yoscrypt", YoscryptLexer)