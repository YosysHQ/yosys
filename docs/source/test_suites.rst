Test suites
===========

.. note:: Potentially significantly out of date information
    last updated circa 2015

.. todo:: copypaste

Continuously checking the correctness of Yosys and making sure that new features
do not break old ones is a high priority in Yosys.  Two external test suites
have been built for Yosys: VlogHammer and yosys-bigsim.  In addition to that,
yosys comes with approx 200 test cases used in ``make test``.  A debug build of
Yosys also contains a lot of asserts and checks the integrity of the internal
state after each command.

VlogHammer
----------

VlogHammer is a Verilog regression test suite developed to test the different
subsystems in Yosys by comparing them to each other and to the output created by
some other tools (Xilinx Vivado, Xilinx XST, Altera Quartus II, ...).

Yosys Subsystems tested: Verilog frontend, const folding, const eval, technology
mapping, simulation models, SAT models.

Thousands of auto-generated test cases containing code such as:

.. code-block:: verilog

    assign y9 = $signed(((+$signed((^(6'd2 ** a2))))<$unsigned($unsigned(((+a3))))));
    assign y10 = (-((+((+{2{(~^p13)}})))^~(!{{b5,b1,a0},(a1&p12),(a4+a3)})));
    assign y11 = (~&(-{(-3'sd3),($unsigned($signed($unsigned({p0,b4,b1}))))}));

Some bugs in Yosys were found and fixed thanks to VlogHammer. Over 50 bugs in
the other tools used as external reference where found and reported so far.

yosys-bigsim
------------

yosys-bigsim is a collection of real-world open-source Verilog designs and test
benches. yosys-bigsim compares the testbench outputs of simulations of the original
Verilog code and synthesis results.

The following designs are included in yosys-bigsim (excerpt):

- ``openmsp430`` -- an MSP430 compatible 16 bit CPU
- ``aes_5cycle_2stage`` -- an AES encryption core
- ``softusb_navre`` -- an AVR compatible 8 bit CPU
- ``amber23`` -- an ARMv2 compatible 32 bit CPU
- ``lm32`` -- another 32 bit CPU from Lattice Semiconductor
- ``verilog-pong`` -- a hardware pong game with VGA output
- ``elliptic_curve_group`` -- ECG point-add and point-scalar-mul core
- ``reed_solomon_decoder`` -- a Reed-Solomon Error Correction Decoder

Code available at https://github.com/YosysHQ/yosys-bigsim
