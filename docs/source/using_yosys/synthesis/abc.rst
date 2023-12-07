The :cmd:ref:`abc` command
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: discuss abc (more stable) vs abc9 (newer, possibly better)

The :cmd:ref:`abc` command provides an interface to ABC_, an open source tool
for low-level logic synthesis.

.. _ABC: http://www.eecs.berkeley.edu/~alanmi/abc/

The :cmd:ref:`abc` command processes a netlist of internal gate types and can
perform:

- logic minimization (optimization)
- mapping of logic to standard cell library (liberty format)
- mapping of logic to k-LUTs (for FPGA synthesis)

Optionally :cmd:ref:`abc` can process registers from one clock domain and
perform sequential optimization (such as register balancing).

ABC is also controlled using scripts. An ABC script can be specified to use more
advanced ABC features. It is also possible to write the design with
:cmd:ref:`write_blif` and load the output file into ABC outside of Yosys.

Example
^^^^^^^

.. todo:: describe ``abc`` images

.. literalinclude:: /code_examples/synth_flow/abc_01.v
   :language: verilog
   :caption: ``docs/source/code_examples/synth_flow/abc_01.v``

.. literalinclude:: /code_examples/synth_flow/abc_01.ys
   :language: yoscrypt
   :caption: ``docs/source/code_examples/synth_flow/abc_01.ys``

.. figure:: /_images/code_examples/synth_flow/abc_01.*
   :class: width-helper
