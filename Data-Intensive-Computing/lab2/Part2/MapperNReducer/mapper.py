#!/usr/bin/python

import sys
import pandas as pd
import re
import nltk
from nltk.corpus import stopwords
from nltk.tokenize import word_tokenize


def mapper():
    url_pattern = r"http\S+"
    url_pattern_re = re.compile(url_pattern)
    nyt_stop_words = ["york","times","navigation","subscribe","story","continue","reading","site","main"]
    for line in sys.stdin:
        temp = re.sub(url_pattern_re, '', line)
        temp = temp.strip().lower().decode("ascii","ignore")
        tokens_temp = re.split(r'[`\-=~!@#$%^&*()_\n\s+\[\]{};\'\\:"|<,./<>?]', temp)
        stop_words = set(stopwords.words('english'))
        for token in tokens_temp:
            if token not in stop_words and len(token) > 2 and not token[0].isdigit() and token not in nyt_stop_words:
                print("%s\t%s" %(token,1))
                
mapper()