Testing Yosys
=============

.. todo:: adding tests (makefile-tests vs seed-tests)

Running the included test suite
-------------------------------

The Yosys source comes with a test suite to avoid regressions and keep
everything working as expected.  Tests can be run by calling ``make test`` from
the root Yosys directory.

Functional tests
~~~~~~~~~~~~~~~~

Testing functional backends (see
:doc:`/yosys_internals/extending_yosys/functional_ir`) has a few requirements in
addition to those listed in :ref:`getting_started/installation:Build
prerequisites`:

.. tab:: Ubuntu

   .. code:: console

      sudo apt-get install racket
      raco pkg install rosette
      pip install pytest-xdist pytest-xdist-gnumake

.. tab:: macOS

   .. code:: console

      brew install racket
      raco pkg install rosette
      pip install pytest-xdist pytest-xdist-gnumake

If you don't have one of the :ref:`getting_started/installation:CAD suite(s)`
installed, you should also install Z3 `following their
instructions <https://github.com/Z3Prover/z3>`_.

Then, set the :makevar:`ENABLE_FUNCTIONAL_TESTS` make variable when calling
``make test`` and the functional tests will be run as well.

Unit tests
~~~~~~~~~~

Running the unit tests requires the following additional packages:

.. tab:: Ubuntu

   .. code:: console

      sudo apt-get install libgtest-dev

.. tab:: macOS

   No additional requirements.

Unit tests can be run with ``make unit-test``. 

Docs tests
~~~~~~~~~~

There are some additional tests for checking examples included in the
documentation, which can be run by calling ``make test`` from the
:file:`yosys/docs` sub-directory (or ``make -C docs test`` from the root). This
also includes checking some macro commands to ensure that descriptions of them
are kept up to date, and is mostly intended for CI.


Automatic testing
-----------------

The `Yosys Git repo`_ has automatic testing of builds and running of the
included test suite on both Ubuntu and macOS, as well as across range of
compiler versions.  For up to date information, including OS versions, refer to
`the git actions page`_.

.. _Yosys Git repo: https://github.com/YosysHQ/yosys
.. _the git actions page: https://github.com/YosysHQ/yosys/actions

..
   How to add a unit test
   ----------------------

   Unit test brings some advantages, briefly, we can list some of them (reference
   [1](https://en.wikipedia.org/wiki/Unit_testing)):

   * Tests reduce bugs in new features;
   * Tests reduce bugs in existing features;
   * Tests are good documentation;
   * Tests reduce the cost of change;
   * Tests allow refactoring;

   With those advantages in mind, it was required to choose a framework which fits
   well with C/C++ code.  Hence, `google test`_ was chosen, because it is widely
   used and it is relatively easy learn.

   .. _google test: https://github.com/google/googletest

   Install and configure google test (manually)
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   In this section, you will see a brief description of how to install google test.
   However, it is strongly recommended that you take a look to the official
   repository (https://github.com/google/googletest) and refers to that if you have
   any problem to install it. Follow the steps below:

   * Install: cmake and pthread
   * Clone google test project from: https://github.com/google/googletest and enter
   in the project directory
   * Inside project directory, type:

   .. code-block:: console

      cmake -DBUILD_SHARED_LIBS=ON .
      make

   * After compilation, copy all ``*.so`` inside directory ``googlemock`` and
   ``googlemock/gtest`` to ``/usr/lib/``
   * Done! Now you can compile your tests.

   If you have any problem, go to the official repository to find help.

   Ps.: Some distros already have googletest packed. If your distro supports it,
   you can use it instead of compile.

   Create a new unit test
   ~~~~~~~~~~~~~~~~~~~~~~

   If you want to add new unit tests for Yosys, just follow the steps below:

   * Go to directory :file:`test/unit/`
   * In this directory you can find something similar Yosys's directory structure.
   To create your unit test file you have to follow this pattern:
   fileNameToImplementUnitTest + Test.cc. E.g.: if you want to implement the unit
   test for ``kernel/celledges.cc``, you will need to create a file like this:
   ``tests/unit/kernel/celledgesTest.cc``;
   * Implement your unit test

   Run unit tests
   ~~~~~~~~~~~~~~

   To compile and run all unit tests, just go to yosys root directory and type:

   .. code-block:: console

      make unit-test

   If you want to remove all unit test files, type:

   .. code-block:: console

      make clean-unit-test
