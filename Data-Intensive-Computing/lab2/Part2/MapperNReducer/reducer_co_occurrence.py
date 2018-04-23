#!/usr/bin/env python

import sys
import json
from operator import itemgetter

def reducer():
    current_word = None
    current_count = 0

    for line in sys.stdin:
        line = line.strip()
        
        co_occur_pair, count = line.split("\t", 1)
        
	try:
            count = int(count)
        except ValueError:
            continue

        if current_word == co_occur_pair:
            current_count += count
	else:
	    if current_word:
		print('%s\t%s' %(current_word,current_count))
	    current_word = co_occur_pair
	    current_count = count

    if current_word == co_occur_pair:
	print('%s\t%s' %(current_word,current_count))
        

reducer()
# ref: http://codingjunkie.net/cooccurrence/
# ref: https://github.com/monisjaved/Data-Processing-With-Hadoop