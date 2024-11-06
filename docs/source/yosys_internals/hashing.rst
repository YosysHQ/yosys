Hashing and associative data structures in Yosys
------------------------------------------------

Yosys heavily relies on custom data structures such as dict or pool defined in
kernel/hashlib.h. There are various reasons for this.

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
``run_hash<T>(const T& obj)``, corresponding to ``hash_top_ops<T>::hash(obj)``,
the default implementation of which is ``hash_ops<T>::hash_acc(Hasher(), obj)``.
``Hasher`` is the class actually implementing the hash function, hiding its
initialized internal state, and passing it out on ``hash_t yield()`` with
perhaps some finalization steps.

``hash_ops<T>`` is the star of the show. By default it pulls the ``Hasher h``
through a ``Hasher T::hash_acc(Hasher h)`` method. That's the method you have to
implement to make a record (class or struct) type easily hashable with Yosys
hashlib associative data structures.

``hash_ops<T>`` is specialized for built-in types like ``int`` or ``bool`` and
treats pointers the same as integers, so it doesn't dereference pointers. Since
many RTLIL data structures like ``RTLIL::Wire`` carry their own unique index
``Hasher::hash_t hashidx_;``, there are specializations for ``hash_ops<Wire*>``
and others in ``kernel/hashlib.h`` that actually dereference the pointers and
call ``hash_acc`` on the instances pointed to.

``hash_ops<T>`` is also specialized for simple compound types like
``std::pair<U>`` by calling hash_acc in sequence on its members. For flexible
size containers like ``std::vector<U>`` the size of the container is hashed
first. That is also how implementing hashing for a custom record data type
should be - unless there is strong reason to do otherwise, call ``h.acc(m)`` on
the ``Hasher h`` you have received for each member in sequence and ``return
h;``. If you do have a strong reason to do so, look at how
``hash_top_ops<RTLIL::SigBit>`` is implemented in ``kernel/rtlil.h``.

Porting plugins from the legacy interface
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Previously, the interface to implement hashing on custom types was just
``unsigned int T::hash() const``. This meant hashes for members were computed
independently and then ad-hoc combined with the hash function with some xorshift
operations thrown in to mix bits together somewhat. A plugin can stay compatible
with both versions prior and after the break by implementing the aforementioned
current interface and redirecting the legacy one:

``void Hasher::acc(const T& t)`` hashes ``t`` into its internal state by also
redirecting to ``hash_ops<T>``

.. code-block:: cpp
   :caption: Example hash compatibility wrapper
   :name: hash_plugin_compat

   inline unsigned int T::hash() const {
       Hasher h;
       return (unsigned int)hash_acc(h).yield();
   }
