s = "abc\xFF"
print(s)  # Note how last character isn’t a letter

print(str(s))


import dateutil.parser as p

print(p.parse("August 13, 1985"))

print(p.parse("2013-8-13"))

print(p.parse("2013-8-13 4:15am"))

