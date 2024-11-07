Synth commands
--------------

.. todo:: comment on common ``synth_*`` options, like ``-run``

Packaged ``synth_*`` commands
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following is a list of all synth commands included in Yosys for different
platforms.  Each command runs a script of sub commands specific to the platform
being targeted.  Note that not all of these scripts are actively maintained and
may not be up-to-date.

- :doc:`/cmd/techlibs/synth_achronix`
- :doc:`/cmd/techlibs/synth_anlogic`
- :doc:`/cmd/techlibs/synth_coolrunner2`
- :doc:`/cmd/techlibs/synth_easic`
- :doc:`/cmd/techlibs/synth_ecp5`
- :doc:`/cmd/techlibs/synth_efinix`
- :doc:`/cmd/techlibs/synth_fabulous`
- :doc:`/cmd/techlibs/synth_gatemate`
- :doc:`/cmd/techlibs/synth_gowin`
- :doc:`/cmd/techlibs/synth_greenpak4`
- :doc:`/cmd/techlibs/synth_ice40`
- :doc:`/cmd/techlibs/synth_intel` (MAX10, Cyclone IV)
- :doc:`/cmd/techlibs/synth_intel_alm` (Cyclone V, Arria V, Cyclone 10 GX)
- :doc:`/cmd/techlibs/synth_lattice`
- :doc:`/cmd/techlibs/synth_nexus`
- :doc:`/cmd/techlibs/synth_quicklogic`
- :doc:`/cmd/techlibs/synth_sf2`
- :doc:`/cmd/techlibs/synth_xilinx`

General synthesis
~~~~~~~~~~~~~~~~~

In addition to the above hardware-specific synth commands, there is also
:doc:`/cmd/techlibs/prep`.  This command is limited to coarse-grain synthesis,
without getting into any architecture-specific mappings or optimizations.  Among
other things, this is useful for design verification.

The following commands are executed by the `prep` command:

.. literalinclude:: /cmd/techlibs/prep.rst
   :start-at: begin:
   :end-before: .. only:: latex
   :dedent:

:doc:`/getting_started/example_synth` covers most of these commands and what
they do.
