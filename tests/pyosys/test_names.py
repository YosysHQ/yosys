from pyosys import libyosys as ys

d = ys.Design()
m = d.addModule("\\top")
w = m.addWire("\\data", 4)
c = m.addCell("\\u_child", "\\child")
c.setPort("\\custom", ys.SigSpec(w))

assert m.wire("\\data").name == "\\data"
assert m.wire("\\missing") is None
assert d.id_find("\\missing") is None
assert str(m.uniquify("\\data")) != "\\data"

assert "\\data" in m.wires_
assert {w.name: 1}["\\data"] == 1
assert c.getPort("\\custom") == ys.SigSpec(w)

c.type = "\\other_child"
assert c.type == "\\other_child"
c.name = d.id_add("\\u_renamed")
assert c.name == "\\u_renamed"

w.attributes["\\note"] = ys.Const("hello")
assert w.get_string_attribute("\\note") == "hello"
del w.attributes["\\note"]
assert not w.has_attribute("\\note")

other = ys.Design()
assert other.addModule("\\other").addWire(w.name).name == "\\data"

try:
	m.addWire("no_prefix")
	assert False, "expected ValueError"
except ValueError:
	pass
