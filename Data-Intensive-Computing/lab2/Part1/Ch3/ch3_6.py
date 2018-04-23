import pandas as pd

# Making data frame from a dictionary
# that maps column names to their values
df = pd.DataFrame({
    "name": ["Bob", "Alex", "Janice"],
    "age": [60, 25, 33]
})
# Reading a DataFrame from a file
other_df = pd.read_csv("C:/Krishna/UB/Spring18/CSE 574 ML/proj1/slump_test_data.csv")
# Making new columns from old ones
# is really easy
df["age_plus_one"] = df["age"] + 1
df["age_times_two"] = 2 * df["age"]
df["age_squared"] = df["age"] * df["age"]
df["over_30"] = (df["age"] > 30)  # this col is bools
# The columns have various built-in aggregate functions
total_age = df["age"].sum()
median_age = df["age"].quantile(0.5)
# You can select several rows of the DataFrame
# and make a new DataFrame out of them
df_below50 = df[df["age"] < 50]
# Apply a custom function to a column
df["age_squared"] = df["age"].apply(lambda x: x*x)

print(df)

#####################
df2 = pd.DataFrame({
"name": ["Bob", "Alex", "Jane"],
"age": [60, 25, 33]
})
print(df2.index) # prints 0‐2, the line numbers
# Create a DataFrame containing the same data,
# but where name is the index
df_w_name_as_ind = df2.set_index("name")

print(df_w_name_as_ind.index) # prints their names
# Get the row for Bob
bobs_row = df_w_name_as_ind.ix["Bob"]
print(bobs_row["age"]) # prints 60

print(df2)
