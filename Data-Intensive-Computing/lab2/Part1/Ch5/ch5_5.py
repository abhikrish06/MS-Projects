import statsmodels.api as sm
from pandas.core import datetools
from matplotlib import pyplot as plt

dta = sm.datasets.co2.load_pandas().data
dta.plot()
plt.title("CO2 Levels")
plt.ylabel("Parts per million")
plt.savefig('timeseries_1.jpg')
plt.show()

