#! /usr/bin/env python2

import sys

if __name__ == '__main__':

    r = None
    f = open(sys.argv[1])
    for line in [ l.strip().split() for l in f ]:
        if len(line) == 0: continue
        if line[0].isdigit():
            if r: print r['n'], r['real'], r['user'], r['sys']
            r = {}
            r['n'] = int(line[0])
        else: r[line[0]] = line[1]
        
    if r: print r['n'], r['real'], r['user'], r['sys']
