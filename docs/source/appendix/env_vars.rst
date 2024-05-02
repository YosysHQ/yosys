Yosys environment variables
===========================

``HOME``
   Yosys command history is stored in :file:`$HOME/.yosys_history`.  Graphics
   (from :cmd:ref:`show` and :cmd:ref:`viz` commands) will output to this
   directory by default.  This environment variable is also used in some cases
   for resolving filenames with :file:`~`.

``PATH``
   May be used in OpenBSD builds for finding the location of Yosys executable.

``TMPDIR``
   Used for storing temporary files.

``ABC``
   When compiling Yosys with out-of-tree ABC using :makevar:`ABCEXTERNAL`, this
   variable can be used to override the external ABC executable.

``YOSYS_NOVERIFIC``
   If Yosys was built with Verific, this environment variable can be used to
   temporarily disable Verific support.

``YOSYS_COVER_DIR`` and ``YOSYS_COVER_FILE``
   When using code coverage, these environment variables control the output file
   name/location.

``YOSYS_ABORT_ON_LOG_ERROR``
   Can be used for debugging Yosys internals.  Setting it to 1 causes abort() to
   be called when Yosys terminates with an error message.

