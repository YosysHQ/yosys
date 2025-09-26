from typing import Mapping
from pyosys import libyosys as ys

StringToStringDict = ys.StringToStringDict

my_dict = StringToStringDict()

assert isinstance(my_dict, Mapping)

my_dict["foo"] = "bar"
my_dict.update([("first", "second")])
my_dict.update({"key": "value"})
for key, value in my_dict.items():
    print(key, value)

new_dict = my_dict | {"tomato": "tomato"}
del new_dict["foo"]
assert set(my_dict.keys()) == {"first", "key", "foo"}
assert set(new_dict.keys()) == {"first", "key", "tomato"}

constructor_test_1 = ys.StringToStringDict(new_dict)
constructor_test_2 = ys.StringToStringDict([("tomato", "tomato")])
constructor_test_3 = ys.StringToStringDict({ "im running": "out of string ideas" })

the_great_or = constructor_test_1 | constructor_test_2 | constructor_test_3

assert set(the_great_or) ==  {"first", "key", "tomato", "im running"}
repr_test = eval(repr(the_great_or))
assert repr_test == the_great_or
