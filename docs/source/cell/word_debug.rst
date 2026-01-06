.. role:: verilog(code)
   :language: Verilog

Debugging cells
---------------

The `$print` cell is used to log the values of signals, akin to (and
translatable to) the ``$display`` and ``$write`` family of tasks in Verilog.  It
has the following parameters:

``FORMAT``
   The internal format string.  The syntax is described below.

``ARGS_WIDTH``
   The width (in bits) of the signal on the ``ARGS`` port.

``TRG_ENABLE``
   True if triggered on specific signals defined in ``TRG``; false if triggered
   whenever ``ARGS`` or ``EN`` change and ``EN`` is 1.

If ``TRG_ENABLE`` is true, the following parameters also apply:

``TRG_WIDTH``
   The number of bits in the ``TRG`` port.

``TRG_POLARITY``
   For each bit in ``TRG``, 1 if that signal is positive-edge triggered, 0 if
   negative-edge triggered.

``PRIORITY``
   When multiple `$print` or `$check` cells fire on the same trigger, they
   execute in descending priority order.

Ports:

``TRG``
   The signals that control when this `$print` cell is triggered.

   If the width of this port is zero and ``TRG_ENABLE`` is true, the cell is
   triggered during initial evaluation (time zero) only.

``EN``
   Enable signal for the whole cell.

``ARGS``
   The values to be displayed, in format string order.

.. autocellgroup:: debug
   :members:
   :source:
   :linenos:

Format string syntax
~~~~~~~~~~~~~~~~~~~~

The format string syntax resembles Python f-strings.  Regular text is passed
through unchanged until a format specifier is reached, starting with a ``{``.

Format specifiers have the following syntax.  Unless noted, all items are
required:

``{``
   Denotes the start of the format specifier.

size
   Signal size in bits; this many bits are consumed from the ``ARGS`` port by
   this specifier.

``:``
   Separates the size from the remaining items.

justify
   ``>`` for right-justified, ``<`` for left-justified.

padding
   ``0`` for zero-padding, or a space for space-padding.

width\ *?*
   (optional) The number of characters wide to pad to.

base
   * ``b`` for base-2 integers (binary)
   * ``o`` for base-8 integers	(octal)
   * ``d`` for base-10 integers (decimal)
   * ``h`` for base-16	integers (hexadecimal)
   * ``c`` for ASCII characters/strings
   * ``t`` and ``r`` for simulation time (corresponding to :verilog:`$time` and
     :verilog:`$realtime`)

For integers, this item may follow:

``+``\ *?*
   (optional, decimals only) Include a leading plus for non-negative numbers.
   This can assist with symmetry with negatives in tabulated output.

signedness
   ``u`` for unsigned, ``s`` for signed.  This distinction is only respected
   when rendering decimals.

ASCII characters/strings have no special options, but the signal size must be
divisible by 8.

For simulation time, the signal size must be zero.

Finally:

``}``
   Denotes the end of the format specifier.

Some example format specifiers:

+ ``{8:>02hu}`` - 8-bit unsigned integer rendered as hexadecimal,
  right-justified, zero-padded to 2 characters wide.
+ ``{32:< 15d+s}`` - 32-bit signed integer rendered as decimal, left-justified,
  space-padded to 15 characters wide, positive values prefixed with ``+``.
+ ``{16:< 10hu}`` - 16-bit unsigned integer rendered as hexadecimal,
  left-justified, space-padded to 10 characters wide.
+ ``{0:>010t}`` - simulation time, right-justified, zero-padded to 10 characters
  wide.

To include literal ``{`` and ``}`` characters in your format string, use ``{{``
and ``}}`` respectively.

It is an error for a format string to consume more or less bits from ``ARGS``
than the port width.

Values are never truncated, regardless of the specified width.

Note that further restrictions on allowable combinations of options may apply
depending on the backend used.

For example, Verilog does not have a format specifier that allows zero-padding a
string (i.e. more than 1 ASCII character), though zero-padding a single
character is permitted.

Thus, while the RTLIL format specifier ``{8:>02c}`` translates to ``%02c``,
``{16:>02c}`` cannot be represented in Verilog and will fail to emit.  In this
case, ``{16:> 02c}`` must be used, which translates to ``%2s``.
