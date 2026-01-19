Synth commands
--------------

.. todo:: comment on common ``synth_*`` options, like ``-run``

Packaged ``synth_*`` commands
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A list of all synth commands included in Yosys for different platforms can be
found under :doc:`/cmd/index_techlibs`.  Each command runs a script of sub
commands specific to the platform being targeted.  Note that not all of these
scripts are actively maintained and may not be up-to-date.

General synthesis
~~~~~~~~~~~~~~~~~

In addition to the above hardware-specific synth commands, there is also
:cmd:title:`prep`.  This command is limited to coarse-grain synthesis, without
getting into any architecture-specific mappings or optimizations.  Among other
things, this is useful for design verification.

The following commands are executed by the `prep` command:

.. literalinclude:: /code_examples/macro_commands/prep.ys
   :start-at: begin:

:doc:`/getting_started/example_synth` covers most of these commands and what
they do.
