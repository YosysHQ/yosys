Internal commands for developers
--------------------------------

.. autocmdgroup:: internal
   :members:

Writing command help
--------------------

- use `chformal` as an example
- generated help content below

.. _chformal autocmd:

.. autocmd:: chformal
   :noindex:

The ``formatted_help()`` method
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``PrettyHelp::get_current()``
- ``PrettyHelp::set_group()``

  + used with ``.. autocmdgroup:: <group>``
  + can assign group and return false
  + if no group is set, will try to use ``source_location`` and assign group
    from path to source file

- return value

  + true means help content added to current ``PrettyHelp``
  + false to use ``Pass::help()``

- adding content

  + help content is a list of ``ContentListing`` nodes, each one having a type,
    body, and its own list of children ``ContentListing``\ s
  + ``PrettyHelp::get_root()`` returns the root ``ContentListing`` (``type="root"``)
  + ``ContentListing::{usage, option, codeblock, paragraph}`` each add a
    ``ContentListing`` to the current node, with type the same as the method

    * the first argument is the body of the new node
    * ``usage`` shows how to call the command (i.e. its "signature")
    * ``paragraph`` content is formatted as a paragraph of text with line breaks
      added automatically
    * ``codeblock`` content is displayed verbatim, use line breaks as desired;
      takes an optional ``language`` argument for assigning the language in RST
      output for code syntax highlighting (use ``yoscrypt`` for yosys script
      syntax highlighting)
    * ``option`` lists a single option for the command, usually starting with a
      dash (``-``); takes an optional second argument which adds a paragraph
      node as a means of description

  + ``ContentListing::open_usage`` creates and returns a new usage node, can be
    used to e.g. add text/options specific to a given usage of the command
  + ``ContentListing::open_option`` creates and returns a new option node, can
    be used to e.g. add multiple paragraphs to an option's description
  + paragraphs are treated as raw RST, allowing for inline formatting and
    references as if it were written in the RST file itself

.. literalinclude:: /generated/chformal.cc
   :language: c++
   :start-at: bool formatted_help()
   :end-before: void execute
   :caption: ``ChformalPass::formatted_help()`` from :file:`passes/cmds/chformal.cc`

Dumping command help to json
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- `help -dump-cmds-json cmds.json`

  + generates a ``ContentListing`` for each command registered in Yosys
  + tries to parse unformatted ``Pass::help()`` output if
    ``Pass::formatted_help()`` is unimplemented or returns false

    * if a line starts with four spaces followed by the name of the command then
      a space, it is parsed as a signature (usage node)
    * if a line is indented and starts with a dash (``-``), it is parsed as an
      option
    * anything else is parsed as a codeblock and added to either the root node
      or the current option depending on the indentation

  + dictionary of command name to ``ContentListing``

    * uses ``ContentListing::to_json()`` recursively for each node in root
    * root node used for source location of class definition
    * includes flags set during pass constructor (e.g. ``experimental_flag`` set
      by ``Pass::experimental()``)
    * also title (``short_help`` argument in ``Pass::Pass``), group, and class
      name
   
  + dictionary of group name to list of commands in that group

- used by sphinx autodoc to generate help content

.. literalinclude:: /generated/cmds.json
   :language: json
   :start-at: "chformal": {
   :end-before: "chparam": {
   :caption: `chformal` in generated :file:`cmds.json`

.. note:: Synthesis command scripts are special cased

   If the final block of help output starts with the string `"The following
   commands are executed by this synthesis command:\n"`, then the rest of the
   code block is formatted as ``yoscrypt`` (e.g. `synth_ice40`).  The caveat
   here is that if the ``script()`` calls ``run()`` on any commands *prior* to
   the first ``check_label`` then the auto detection will break and revert to
   unformatted code (e.g. `synth_fabulous`). 

Command line rendering
~~~~~~~~~~~~~~~~~~~~~~

- if ``Pass::formatted_help()`` returns true, will call
  ``PrettyHelp::log_help()``

  + traverse over the children of the root node and render as plain text 
  + effectively the reverse of converting unformatted ``Pass::help()`` text
  + lines are broken at 80 characters while maintaining indentation (controlled
    by ``MAX_LINE_LEN`` in :file:`kernel/log_help.cc`)
  + each line is broken into words separated by spaces, if a given word starts
    and ends with backticks they will be stripped

- if it returns false it will call ``Pass::help()`` which should call ``log()``
  directly to print and format help text

  + if ``Pass::help()`` is not overridden then a default message about missing
    help will be displayed

.. literalinclude:: /generated/chformal.log
   :lines: 2-

RST generated from autocmd
~~~~~~~~~~~~~~~~~~~~~~~~~~

- below is the raw RST output from ``autocmd`` (``YosysCmdDocumenter`` class in
  :file:`docs/util/cmd_documenter.py`) for `chformal` command
- heading will be rendered as a subheading of the most recent heading (see
  `chformal autocmd`_ above rendered under `Writing command help`_)
- ``.. cmd:def:: <cmd>`` line is indexed for cross references with ``:cmd:ref:``
  directive (`chformal autocmd`_ above uses ``:noindex:`` option so that
  `chformal` still links to the correct location)

  + ``:title:`` option controls text that appears when hovering over the
    `chformal` link

- commands with warning flags (experimental or internal) add a ``.. warning``
  block before any of the help content
- if a command has no ``source_location`` the ``.. note`` at the bottom will
  instead link to :doc:`/cmd/index_other`

.. autocmd_rst:: chformal
