from pyosys import libyosys as ys

my_dict = ys.StringToStringDict()
my_dict["foo"] = "bar"
my_dict.update([("first", "second")])
my_dict.update({"key": "value"})
for key, value in my_dict.items():
    print(key, value)

new_dict = my_dict | {"tomato": "tomato"}
del new_dict["foo"]
assert set(my_dict.keys()) == {"first", "key", "foo"}
assert set(new_dict.keys()) == {"first", "key", "tomato"}
