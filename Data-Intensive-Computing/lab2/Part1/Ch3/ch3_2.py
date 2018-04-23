my_list = ["a ", "b ", "c "]
print(my_list[0]) # prints "a "
my_list[0] = "A " # changes that element of the list
my_list.append("d ") # adds new element to the end
print(my_list)
# List elements can be ANYTHING
mixed_list = ["A ", 5.7, "B ", [1,2,3]]
print(mixed_list)

original_list = [1,2,3,4,5,6,7,8]
print(original_list)
squares = [x*x for x in original_list]
print(squares)
squares_of_evens = [x*x for x in original_list if x%2==0]   # error in book's code
print(squares_of_evens)