import pandas as pd
from matplotlib import pyplot as plt
import sklearn.datasets


def get_iris_df():
    ds = sklearn.datasets.load_iris()
    df = pd.DataFrame(ds['data'], columns=ds['feature_names'])
    code_species_map = dict(zip(range(3), ds['target_names']))
    df['species'] = [code_species_map[c] for c in ds['target']]
    return df


df = get_iris_df()

print(df["sepal width (cm)"].corr(df["sepal length (cm)"]))
print(df["sepal width (cm)"].corr(df["sepal length (cm)"], method="pearson"))

print(df["sepal width (cm)"].corr(df["sepal length (cm)"], method="spearman"))
print(df["sepal width (cm)"].corr(df["sepal length (cm)"], method="spearman"))
