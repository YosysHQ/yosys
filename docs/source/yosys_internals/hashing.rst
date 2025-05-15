Hashing and associative data structures in Yosys
------------------------------------------------

Container classes based on hashing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Yosys uses ``dict<K, T>`` and ``pool<T>`` as main container classes.
``dict<K, T>`` is essentially a replacement for ``std::unordered_map<K, T>``
and ``pool<T>`` is a replacement for ``std::unordered_set<T>``.
The main characteristics are:

* ``dict<K, T>`` and ``pool<T>`` are about 2x faster than the std containers
   (though this claim hasn't been verified for over 10 years)

* references to elements in a ``dict<K, T>`` or ``pool<T>`` are invalidated by
   insert and remove operations (similar to ``std::vector<T>`` on ``push_back()``).

* some iterators are invalidated by ``erase()``. specifically, iterators
   that have not passed the erased element yet are invalidated. (``erase()``
   itself returns valid iterator to the next element.)

* no iterators are invalidated by ``insert()``. elements are inserted at
   ``begin()``. i.e. only a new iterator that starts at ``begin()`` will see the
   inserted elements.

* the method ``.count(key, iterator)`` is like ``.count(key)`` but only
   considers elements that can be reached via the iterator.

* iterators can be compared. ``it1 < it2`` means that the position of ``t2``
   can be reached via ``t1`` but not vice versa.

* the method ``.sort()`` can be used to sort the elements in the container
   the container stays sorted until elements are added or removed.

* ``dict<K, T>`` and ``pool<T>`` will have the same order of iteration across
   all compilers, standard libraries and architectures.

In addition to ``dict<K, T>`` and ``pool<T>`` there is also an ``idict<K>`` that
creates a bijective map from ``K`` to the integers. For example:

::

   idict<string, 42> si;
   log("%d\n", si("hello"));      // will print 42
   log("%d\n", si("world"));      // will print 43
   log("%d\n", si.at("world"));   // will print 43
   log("%d\n", si.at("dummy"));   // will throw exception
   log("%s\n", si[42].c_str()));  // will print hello
   log("%s\n", si[43].c_str()));  // will print world
   log("%s\n", si[44].c_str()));  // will throw exception

It is not possible to remove elements from an idict.

Finally ``mfp<K>`` implements a merge-find set data structure (aka. disjoint-set
or union-find) over the type ``K`` ("mfp" = merge-find-promote).

The hash function
~~~~~~~~~~~~~~~~~

The hash function generally used in Yosys is the XOR version of DJB2:

::

   state = ((state << 5) + state) ^ value

This is an old-school hash designed to hash ASCII characters. Yosys doesn't hash
a lot of ASCII text, but it still happens to be a local optimum due to factors
described later.

Hash function quality is multi-faceted and highly dependent on what is being
hashed. Yosys isn't concerned by any cryptographic qualities, instead the goal
is minimizing total hashing collision risk given the data patterns within Yosys.
In general, a good hash function typically folds values into a state accumulator
with a mathematical function that is fast to compute and has some beneficial
properties. One of these is the avalanche property, which demands that a small
change such as flipping a bit or incrementing by one in the input produces a
large, unpredictable change in the output. Additionally, the bit independence
criterion states that any pair of output bits should change independently when
any single input bit is inverted. These properties are important for avoiding
hash collision on data patterns like the hash of a sequence not colliding with
its permutation, not losing from the state the information added by hashing
preceding elements, etc.

DJB2 lacks these properties. Instead, since Yosys hashes large numbers of data
structures composed of incrementing integer IDs, Yosys abuses the predictability
of DJB2 to get lower hash collisions, with regular nature of the hashes
surviving through the interaction with the "modulo prime" operations in the
associative data structures. For example, some most common objects in Yosys are
interned ``IdString``\ s of incrementing indices or ``SigBit``\ s with bit
offsets into wire (represented by its unique ``IdString`` name) as the typical
case. This is what makes DJB2 a local optimum. Additionally, the ADD version of
DJB2 (like above but with addition instead of XOR) is used to this end for some
types, abandoning the general pattern of folding values into a state value.

Making a type hashable
~~~~~~~~~~~~~~~~~~~~~~

Let's first take a look at the external interface on a simplified level.
Generally, to get the hash for ``T obj``, you would call the utility function
``run_hash<T>(const T& obj)``, corresponding to ``hash_ops<T>::hash(obj)``,
the default implementation of which uses ``hash_ops<T>::hash_into(Hasher(), obj)``.
``Hasher`` is the class actually implementing the hash function, hiding its
initialized internal state, and passing it out on ``hash_t yield()`` with
perhaps some finalization steps.

``hash_ops<T>`` is the star of the show. By default it pulls the ``Hasher h``
through a ``Hasher T::hash_into(Hasher h)`` method. That's the method you have to
implement to make a record (class or struct) type easily hashable with Yosys
hashlib associative data structures.

``hash_ops<T>`` is specialized for built-in types like ``int`` or ``bool`` and
treats pointers the same as integers, so it doesn't dereference pointers. Since
many RTLIL data structures like ``RTLIL::Wire`` carry their own unique index
``Hasher::hash_t hashidx_;``, there are specializations for ``hash_ops<Wire*>``
and others in ``kernel/hashlib.h`` that actually dereference the pointers and
call ``hash_into`` on the instances pointed to.

``hash_ops<T>`` is also specialized for simple compound types like
``std::pair<U>`` by calling hash_into in sequence on its members. For flexible
size containers like ``std::vector<U>`` the size of the container is hashed
first. That is also how implementing hashing for a custom record data type
should be - unless there is strong reason to do otherwise, call ``h.eat(m)`` on
the ``Hasher h`` you have received for each member in sequence and ``return
h;``.

The ``hash_ops<T>::hash(obj)`` method is not indended to be called when
context of implementing the hashing for a record or other compound type.
When writing it, you should connect it to ``hash_ops<T>::hash_into(Hasher h)``
as shown below. If you have a strong reason to do so, and you have
to create a special implementation for top-level hashing, look at how
``hash_ops<RTLIL::SigBit>::hash(...)`` is implemented in ``kernel/rtlil.h``.

Porting plugins from the legacy interface
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Previously, the interface to implement hashing on custom types was just
``unsigned int T::hash() const``. This meant hashes for members were computed
independently and then ad-hoc combined with the hash function with some xorshift
operations thrown in to mix bits together somewhat. A plugin can stay compatible
with both versions prior and after the break by implementing both interfaces
based on the existance and value of `YS_HASHING_VERSION`.

.. code-block:: cpp
   :caption: Example hash compatibility wrapper
   :name: hash_plugin_compat

   #ifndef YS_HASHING_VERSION
   unsigned int T::hash() const {
      return mkhash(a, b);
   }
   #elif YS_HASHING_VERSION == 1
   Hasher T::hash_into(Hasher h) const {
      h.eat(a);
      h.eat(b);
      return h;
   }
   Hasher T::hash() const {
      Hasher h;
      h.eat(*this);
      return h;
   }
   #else
   #error "Unsupported hashing interface"
   #endif

Feel free to contact Yosys maintainers with related issues.
