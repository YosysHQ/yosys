Dataflow tracking
-------------------

Yosys can be used to answer questions such as "can this signal affect this other
signal?" via its *dataflow tracking* support. For this, four special cells,
`$get_tag`, `$set_tag`, `$overwrite_tag` and `$original_tag` are inserted into
the design (e.g. by a custom Yosys pass) and then the `dft_tag` is run, which
converts these cells into ordinary logic. Typically, one would then use `SBY`_
to prove assertions involving these cells.

.. _SBY: https://yosyshq.readthedocs.io/projects/sby

Ordinarily in Yosys, the state of a bit is simply ``0`` or ``1`` (or one of the
special values, ``z`` and ``x``). During dataflow tracking they are augmented
with a set of tags. For example, the state of a bit could be ``0`` and the set
of tags ``"KEY"`` and ``"OVERFLOW"``.

In addition to their usual operations on the logical bits, Yosys operations must
now also process the status of the tags. For this, tags are simply *forwarded*
or *propagated* (i.e. copied) from inputs to outputs, according to the following
general rule:

   A tag is forwarded from an input to an output if the input can affect the
   output, for that particular state of all other inputs.

For example, XOR, AND and OR cells propagate tags as follows:

#. XOR simply forwards all tags from its inputs to its output, because inputs to
   XOR can always affect the output.
#. AND forwards tags on a given input only if the other input is ``1``. Because
   if one input is ``0``, the other input can never affect the output.
#. Similarly, OR forwards tags only if the other input is ``0``.

There are two exceptions to this rule:

#. In general, propagation is only determined approximately. For example, unless
   the ``dft_tag`` code knows about a cell, it simply assumes the worst-case
   behaviour that all inputs can affect all outputs. Further, the code also does
   not consider that, when a signal affects multiple inputs of a cell, the
   resulting simultaneous changes of the inputs can cancel each other out, for
   example ``A ^ A`` or ``A ^ (B ^ A)`` is independent of ``A``, but its tags
   would be propagated nonetheless.
#. If tag groups are used, the rules are modified (see below).

Because of this propagation behaviour, we can answer questions about what
signals are affected by a certain signal, by injecting a tag at that point in
the circuit, and observing where the tag is visible.

Example use cases
~~~~~~~~~~~~~~~~~~

As an example use case, consider a cryptographic processor which is not supposed
to expose its secret keys to the outside world. We can tag all key bits with the
``"KEY"`` tag and use `SBY`_ to formally verify that no external signal ever
carries the ``"KEY"`` tag, meaning that key information is not visible to the
outside. As a caveat, we have to manually clear the ``"KEY"`` tag during
cryptographic operations, as proving that the cryptographic operations
themselves do not leak key information is beyond the ability of Yosys. However
we can still easily detect, if e.g. an engineer forgot to remove debugging code
that allows reading back key data.

As a different use case, we can modify all adders in the design to set the
``"OVERFLOW"`` tag on their output bits, if the addition overflowed, and then
add asserts to all flip-flop inputs and output signals that they do not carry
the ``"OVERFLOW"`` tag, i.e. that the results of overflowed additions never
affect system state. Note that in this particular example we use the ability of
tag insertion to be conditional on logic, in this case the overflow condition of
an adder.

Semantics of dataflow tracking cells
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

``$set_tag`` has inputs ``A``, ``SET``, ``CLR``, an output ``Y`` and a string
parameter ``TAG``. The logic value of ``A`` and all tags other than the one
named by the ``TAG`` parameter are simply copied to ``Y``. If ``SET`` is ``1``,
then the named tag is added to ``Y``. Otherwise, if ``CLR`` is ``1``, then the
named tag is removed. Otherwise, the tag is unchanged, i.e. it is present in
``Y`` if it is present in ``A``.

``$get_tag`` has an input ``A`` and an output ``Y`` and a string parameter
``TAG``. ``$get_tag`` inspects ``A`` for the presence or absence of a tag of the
given name and sets ``Y`` to ``1`` if the tag is present. The logical value of
``A`` is completely ignored.

``$overwrite_tag`` functions like ``$set_tag``, but lacks the ``Y`` output.
Instead of providing a modified version of the input signal, it modifies the
signal ``A`` "in-place", i.e. if a signal is input to ``$overwrite_tag``, that
is equivalent to interposing a ``$set_tag`` between its driver and all cells it
is connected to. The main purpose of ``$overwrite_tag`` is adding tags to
signals produced within a module that cannot or should not be modified itself.

``$original_tag`` functions identically to ``$get_tag``, but ignores
``$overwrite_tag``, i.e. when converting the ``$overwrite_tag`` to ``$set_tag``
as described above, it is equivalent to inserting the ``$get_tag`` *before* the
``$set_tag``.

Tag groups
~~~~~~~~~~~~~~

Tag groups are an advanced feature that modify the propagation rule discussed
above. To use tag groups, simply name tags according to the schema
``"group:name"``. For example, ``"key:0"``, ``"key:a"``, ``"key:b"`` would be
three tags in the ``"key"`` group.

The propagation rule is then amended by

   Inputs cannot block the propagation of each other's tags for tags of the same
   group.

For example, an AND gate will propagate a given tag on one input, if the other
input is either 1 or carries a tag of the same group. So if one input is ``0,
"key:a"`` and the other is ``0, "key:b"`` the result would be ``0, "key:a",
"key:b"``, rather than simply ``0``. Note that if we add an unrelated
``"overflow"`` tag to the first input, it would still not be propagated.