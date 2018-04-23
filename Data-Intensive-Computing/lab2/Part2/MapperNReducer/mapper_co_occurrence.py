#!/usr/bin/env python

import sys
import re
import nltk
import json
from nltk.corpus import stopwords
#nltk.download('stopwords')
#nltk.download('punkt')
from nltk.tokenize import word_tokenize

def mapper():
    url_pattern = r"http\S+"
    url_pattern_re = re.compile(url_pattern)
    nyt_stop_words = ["york","times","navigation","subscribe","story","continue","reading","site","main","nytimes","subsciptions"]
    for line in sys.stdin:
        temp = re.sub(url_pattern_re, '', line)
        temp = temp.strip().lower().decode("ascii","ignore")
        tokens_temp = re.split(r'[`\-=~!@#$%^&*()_\n\s+\[\]{};\'\\:"|<,./<>?]', temp)
        stop_words = set(stopwords.words('english'))
        for i in range(len(tokens_temp)-1):
            if tokens_temp[i] not in stop_words and tokens_temp[i] not in nyt_stop_words and not tokens_temp[i].isdigit() and len(tokens_temp[i]) > 2 and tokens_temp[i+1] not in stop_words and tokens_temp[i+1] not in nyt_stop_words and len(tokens_temp[i+1]) > 2:
                print('%s|%s\t%s' %(tokens_temp[i],tokens_temp[i+1],1))

mapper()
# ref: http://codingjunkie.net/cooccurrence/
# ref: https://github.com/monisjaved/Data-Processing-With-Hadoop