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

col = 'sepal length (cm)'
df['ind'] = pd.Series(df.index).apply(lambda i: i % 50)
df.pivot('ind', 'species')[col].plot(kind='box')
plt.savefig('box_plot_sepal_length.jpg')
plt.show()

df.plot(kind="scatter", x="sepal length (cm)", y="sepal width (cm)")
plt.title("Length vs Width")
plt.savefig('scatter_plot_spl_len_vs_wid.jpg')
plt.show()

plt.close()
colors = ["r", "g", "b"]
markers = [".", "*", "^"]
fig, ax = plt.subplots(1, 1)
for i, spec in enumerate(df['species'].unique()):
    ddf = df[df['species'] == spec]
    ddf.plot(kind="scatter", x="sepal width (cm)", y="sepal length (cm)",
             alpha=0.5, s=10 * (i + 1), ax=ax, color=colors[i], marker=markers[i], label=spec)
plt.legend()
plt.savefig('scatter_plot_diff_markers.jpg')
plt.show()

plt.close()
from pandas.plotting import scatter_matrix  # old in book

scatter_matrix(df)
plt.savefig('scatter_matrix.jpg')
plt.show()

plt.close()
df.plot(kind="hexbin", x="sepal width (cm)", y="sepal length (cm)")
plt.savefig('histogram.jpg')
plt.show()
