Symbolic model checking
-----------------------

.. todo:: check text context

.. note:: 
    
    While it is possible to perform model checking directly in Yosys, it 
    is highly recommended to use SBY or EQY for formal hardware verification.

Symbolic Model Checking (SMC) is used to formally prove that a circuit has (or
has not) a given property.

One application is Formal Equivalence Checking: Proving that two circuits are
identical. For example this is a very useful feature when debugging custom
passes in Yosys.

Other applications include checking if a module conforms to interface standards.

The :cmd:ref:`sat` command in Yosys can be used to perform Symbolic Model
Checking.

Checking techmap
~~~~~~~~~~~~~~~~

.. todo:: add/expand supporting text

Let's take a look at an example included in the Yosys code base under
|code_examples/synth_flow|_:

.. |code_examples/synth_flow| replace:: :file:`docs/source/code_examples/synth_flow`
.. _code_examples/synth_flow: https://github.com/YosysHQ/yosys/tree/main/docs/source/code_examples/synth_flow

.. literalinclude:: /code_examples/synth_flow/techmap_01_map.v
   :language: verilog
   :caption: :file:`techmap_01_map.v`

.. literalinclude:: /code_examples/synth_flow/techmap_01.v
   :language: verilog
   :caption: :file:`techmap_01.v`

.. literalinclude:: /code_examples/synth_flow/techmap_01.ys
   :language: yoscrypt
   :caption: :file:`techmap_01.ys`

To see if it is correct we can use the following code:

.. todo:: replace inline code

.. code:: yoscrypt

    # read test design
    read_verilog techmap_01.v
    hierarchy -top test

    # create two version of the design: test_orig and test_mapped
    copy test test_orig
    rename test test_mapped

    # apply the techmap only to test_mapped
    techmap -map techmap_01_map.v test_mapped

    # create a miter circuit to test equivalence
    miter -equiv -make_assert -make_outputs test_orig test_mapped miter
    flatten miter

    # run equivalence check
    sat -verify -prove-asserts -show-inputs -show-outputs miter

Result:

.. code::

    Solving problem with 945 variables and 2505 clauses..
    SAT proof finished - no model found: SUCCESS!

AXI4 Stream Master
~~~~~~~~~~~~~~~~~~

The code used in this section is included in the Yosys code base under
|code_examples/axis|_.

.. |code_examples/axis| replace:: :file:`docs/source/code_examples/axis`
.. _code_examples/axis: https://github.com/YosysHQ/yosys/tree/main/docs/source/code_examples/axis

The following AXI4 Stream Master has a bug. But the bug is not exposed if the
slave keeps ``tready`` asserted all the time. (Something a test bench might do.)

Symbolic Model Checking can be used to expose the bug and find a sequence of
values for ``tready`` that yield the incorrect behavior.

.. todo:: add/expand supporting text

.. literalinclude:: /code_examples/axis/axis_master.v
   :language: verilog
   :caption: :file:`axis_master.v`

.. literalinclude:: /code_examples/axis/axis_test.v
   :language: verilog
   :caption: :file:`axis_test.v`

.. literalinclude:: /code_examples/axis/axis_test.ys
   :language: yoscrypt
   :caption: :file:`test.ys`

Result with unmodified :file:`axis_master.v`:

.. todo:: replace inline code

.. code::

    Solving problem with 159344 variables and 442126 clauses..
    SAT proof finished - model found: FAIL!

Result with fixed :file:`axis_master.v`:

.. code::

    Solving problem with 159144 variables and 441626 clauses..
    SAT proof finished - no model found: SUCCESS!
