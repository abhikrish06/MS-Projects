my_dict = {"January": 1, "February":2}
print(my_dict["January"]) # prints 1
my_dict["March"] = 3 # add new element
my_dict["January"] = "Start of the year" # overwrite old value
print(my_dict)

pairs = [("one",1), ("two",2)]
as_dict = dict(pairs)
same_as_pairs = as_dict.items()

print("pairs: ", pairs)
print("as_dict: ", as_dict)
print("same_as_pairs: ", same_as_pairs)