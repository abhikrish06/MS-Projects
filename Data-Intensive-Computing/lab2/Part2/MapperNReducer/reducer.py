#!/usr/bin/python

import sys
def reducer():
    word_count = 0
    previous_word = None
    for line in sys.stdin:
        data = line.strip().split("\t")
        current_word, count = data
        if previous_word and previous_word != current_word:
            print("%s\t%s" % (previous_word, word_count))
            word_count = 0
        previous_word = current_word
        word_count += int(count)
    if previous_word != None:
        print("%s\t%s" % (previous_word, word_count))

