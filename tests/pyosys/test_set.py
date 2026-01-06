# -*- coding: utf-8 -*-
from pyosys.libyosys import StringSet, StringPool

for cls in [StringSet, StringPool]:
	print(f"Testing {cls.__name__}...")
	A = cls()
	A.add("a")

	B = cls()
	B = A | {"b"}

	assert A < B
	assert A <= B

	A.add("b")

	assert A == B
	assert A <= B
	assert not A < B

	A.add("c")

	assert A > B

	A &= B
	assert A == B

	Ø = A - B
	assert len(Ø) == 0

	C = cls({"A", "B", "C"})
	D = cls()
	C |= {"A", "B", "C"}
	D |= {"C", "D", "E"}
	c_symdiff_d = (C ^ D)
	assert c_symdiff_d == {"A", "B", "D", "E"} # compare against iterable

	repr_test = eval(repr(c_symdiff_d))
	assert c_symdiff_d == repr_test # compare against self


print("Done.")
