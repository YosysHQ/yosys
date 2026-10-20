from pyosys import libyosys as ys

d = ys.Design()
m = d.addModule("\\top")
a = m.addWire("\\a", 4)
b = m.addWire("\\b", 4)
y = m.addWire("\\y", 4)

assert a.src() == ys.SrcRef.Null
assert ys.SrcRef() == ys.SrcRef.Null

try:
	hash(a.src())
	assert False, "expected TypeError"
except TypeError:
	pass

srcs = d.srcs()
first = srcs.add("top.v:1.2-1.3")
second = srcs.add("top.v:2.2-2.3")
assert first != ys.SrcRef.Null
assert srcs.add("top.v:1.2-1.3") == first
assert srcs.str(first) == "top.v:1.2-1.3"

a.set_src(first)
assert a.src() == first
assert a.get_src_attribute() == "top.v:1.2-1.3"

b.set_src(a.src())
assert b.src() == first

both = srcs.merge(first, second)
assert set(srcs.leaves(both)) == {"top.v:1.2-1.3", "top.v:2.2-2.3"}
assert srcs.merge(both, first) == both

c = m.addAnd("\\and", ys.SigSpec(a), ys.SigSpec(b), ys.SigSpec(y), src_ref=both)
assert c.src() == both
assert c.srcs().str(c.src()) == srcs.str(both)
assert m.addOr("\\or", ys.SigSpec(a), ys.SigSpec(b), ys.SigSpec(y)).src() == ys.SrcRef.Null
