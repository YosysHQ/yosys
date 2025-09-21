from pyosys import libyosys as ys

my_idict = ys.IdstringIdict()
print(my_idict(ys.IdString("\\hello")))
print(my_idict(ys.IdString("\\world")))
print(my_idict.get(ys.IdString("\\world")))
try:
	print(my_idict.get(ys.IdString("\\dummy")))
except IndexError as e:
	print(f"{repr(e)}")
print(my_idict[0])
print(my_idict[1])
try:
	print(my_idict[2])
except IndexError as e:
	print(f"{repr(e)}")

for i in my_idict:
	print(i)

current_len = len(my_idict)
assert current_len == 2, "copy"

my_copy = my_idict.copy()
my_copy(ys.IdString("\\copy"))
assert len(my_idict) == current_len, "copy seemed to have mutate original idict"
assert len(my_copy) == current_len + 1, "copy not behaving as expected"

current_copy_len = len(my_copy)
my_copy |= (ys.IdString(e) for e in ("\\the", "\\world")) # 1 new element
assert len(my_copy) == current_copy_len + 1, "or operator returned unexpected result"
