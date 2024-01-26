Synth commands
--------------

.. todo:: comment on common ``synth_*`` options, like ``-run``

Packaged ``synth_*`` commands
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following is a list of all synth commands included in Yosys for different
platforms.  Each command runs a script of sub commands specific to the platform
being targeted.  Note that not all of these scripts are actively maintained and
may not be up-to-date.

- :doc:`/cmd/synth_achronix`
- :doc:`/cmd/synth_anlogic`
- :doc:`/cmd/synth_coolrunner2`
- :doc:`/cmd/synth_easic`
- :doc:`/cmd/synth_ecp5`
- :doc:`/cmd/synth_efinix`
- :doc:`/cmd/synth_fabulous`
- :doc:`/cmd/synth_gatemate`
- :doc:`/cmd/synth_gowin`
- :doc:`/cmd/synth_greenpak4`
- :doc:`/cmd/synth_ice40`
- :doc:`/cmd/synth_intel` (MAX10, Cyclone IV)
- :doc:`/cmd/synth_intel_alm` (Cyclone V, Arria V, Cyclone 10 GX)
- :doc:`/cmd/synth_lattice`
- :doc:`/cmd/synth_nexus`
- :doc:`/cmd/synth_quicklogic`
- :doc:`/cmd/synth_sf2`
- :doc:`/cmd/synth_xilinx`

General synthesis
~~~~~~~~~~~~~~~~~

In addition to the above hardware-specific synth commands, there is also
:doc:`/cmd/prep`.  This command is limited to coarse-grain synthesis, without
getting into any architecture-specific mappings or optimizations.  Among other
things, this is useful for design verification.

The following commands are executed by the :cmd:ref:`prep` command:

.. literalinclude:: /cmd/prep.rst
   :start-at: begin:
   :end-before: .. raw:: latex
   :dedent:

:doc:`/getting_started/example_synth` covers most of these commands and what
they do.
