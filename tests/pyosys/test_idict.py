from pyosys import libyosys as ys

d = ys.Design()
hello, world, dummy, copy, the = [d.id_add(n) for n in ("\\hello", "\\world", "\\dummy", "\\copy", "\\the")]

my_idict = ys.IdstringIdict()
print(my_idict(hello))
print(my_idict(world))
print(my_idict.get(world))
try:
	print(my_idict.get(dummy))
except IndexError as e:
	print(f"{repr(e)}")
print(d.str(my_idict[0]))
print(d.str(my_idict[1]))
try:
	print(my_idict[2])
except IndexError as e:
	print(f"{repr(e)}")

for i in my_idict:
	print(d.str(i))

current_len = len(my_idict)
assert current_len == 2, "copy"

my_copy = my_idict.copy()
my_copy(copy)
assert len(my_idict) == current_len, "copy seemed to have mutate original idict"
assert len(my_copy) == current_len + 1, "copy not behaving as expected"

current_copy_len = len(my_copy)
my_copy |= (the, world) # 1 new element
assert len(my_copy) == current_copy_len + 1, "or operator returned unexpected result"
