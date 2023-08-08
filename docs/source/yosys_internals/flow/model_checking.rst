Symbolic model checking
-----------------------

.. todo:: copypaste

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

Remember the following example from :doc:`/getting_started/typical_phases`?

.. literalinclude:: ../../../resources/PRESENTATION_ExSyn/techmap_01_map.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/techmap_01_map.v``

.. literalinclude:: ../../../resources/PRESENTATION_ExSyn/techmap_01.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExSyn/techmap_01.v``

.. literalinclude:: ../../../resources/PRESENTATION_ExSyn/techmap_01.ys
   :language: yoscrypt
   :caption: ``docs/resources/PRESENTATION_ExSyn/techmap_01.ys``

Lets see if it is correct..

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

The following AXI4 Stream Master has a bug. But the bug is not exposed if the
slave keeps ``tready`` asserted all the time. (Something a test bench might do.)

Symbolic Model Checking can be used to expose the bug and find a sequence of
values for ``tready`` that yield the incorrect behavior.

.. literalinclude:: ../../../resources/PRESENTATION_ExOth/axis_master.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExOth/axis_master.v``

.. literalinclude:: ../../../resources/PRESENTATION_ExOth/axis_test.v
   :language: verilog
   :caption: ``docs/resources/PRESENTATION_ExOth/axis_test.v``


.. code:: yoscrypt

    read_verilog -sv axis_master.v axis_test.v
    hierarchy -top axis_test

    proc; flatten;;
    sat -seq 50 -prove-asserts

Result with unmodified ``axis_master.v``:

.. code::

    Solving problem with 159344 variables and 442126 clauses..
    SAT proof finished - model found: FAIL!

Result with fixed ``axis_master.v``:

.. code::

    Solving problem with 159144 variables and 441626 clauses..
    SAT proof finished - no model found: SUCCESS!
