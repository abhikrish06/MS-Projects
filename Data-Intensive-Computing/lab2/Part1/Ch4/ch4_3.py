import re
street_pattern = r"^[0-9]*\s[A-Z][a-z]*" + \
    r"\s(Street|St|Rd|Road|Ave|Avenue|Blvd|Way|Wy)\.?$"
city_pattern = r"[A-Z][a-z]*,\s[A-Z]{2},\s[0-9]{5}$"
#address_pattern = street_pattern + r"\n" + city_pattern
address_pattern = r"^[0-9]*\s[A-Z][a-z]*" + \
    r"\s(Street|St|Rd|Road|Ave|Avenue|Blvd|Way|Wy)\.?" + r"\n" + city_pattern
print("address_pattern:", address_pattern)

address_re = re.compile(address_pattern)
city_re = re.compile(city_pattern)
street_re = re.compile(street_pattern)
address = """1 Pennsylvania Ave.
Buffalo, NY, 14214"""
print(address)
matchStreet = re.match(street_re, "1 Pennsylvania Ave.")
matchCity = re.match(city_re,"Buffalo, NY, 14214")
matches = re.match(address_re, address)
print(matchStreet)
print(matchCity)
print(matches)