#!/usr/bin/env python3
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
highlight_language = 'systemverilog'

html_theme_options = {
    'external_links' : [
        ('YosysHQ Docs', 'https://yosyshq.readthedocs.io'),
        ('Blog', 'https://blog.yosyshq.com'),
        ('Website', 'https://www.yosyshq.com'),
    ],
}

extensions = ['sphinx.ext.autosectionlabel']

# Ensure that autosectionlabel will produce unique names
autosectionlabel_prefix_document = True
autosectionlabel_maxdepth = 1
