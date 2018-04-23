def my_function(x):
    y = x+1
    x_sqrd = x*x
    return x_sqrd

five_plus_one_sqrd = my_function(5)
print(five_plus_one_sqrd)

#########################
def rai(x, n=2):  # function name changed
    return pow(x,n)

two_sqrd = rai(2)
two_cubed = rai(2, n=3)
print(two_sqrd)
print(two_cubed)

######################
sqr = lambda x : x*x
five_sqrd = sqr(5)
print(five_sqrd)

######################
def apply_to_evens(a_list, a_func):
    return [a_func(x) for x in a_list if x%2==0]
my_list = [1,2,3,4,5]
sqrs_of_evens = apply_to_evens(my_list, lambda x:x*x)

print(sqrs_of_evens)
