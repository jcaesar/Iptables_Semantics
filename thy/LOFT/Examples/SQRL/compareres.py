#!/usr/bin/python
# coding=utf-8

from sys import exit, stdout, argv
import re

def parse(fp):
	cons = {}
	ifs = []
	with open(fp) as f:
		for line in f:
			m = re.compile('^.*: (.*) -> (.*): (.*)$')
			r = m.match(line)
			if r:
				f,t,s = r.groups()
				ifs.append(f)
				ifs.append(t)
				c = None
				if s == 'success':
					c = True
				elif s == 'fail':
					c = False
				else:
					raise "wat? {}".format(line)
				cons[(f,t)] = c
	return (ifs, cons)

i2, c2 = parse(argv[-1])
i1, c1 = parse(argv[-2])

ifs = sorted(set(i1).union(set(i2)))
mal = max([len(ifce) for ifce in ifs])
ifcop = ifs[:]
ifs.sort(key = lambda f: sum((f,t) not in c1 or not c1[(f,t)] for t in ifcop))
ifs.sort(key = lambda t: sum((f,t) not in c1 or not c1[(f,t)] for f in ifcop))


for f in ifs:
	stdout.write(f)
	i = mal - len(f)
	while i > 0:
		stdout.write(' ')
		i = i - 1	
	stdout.write(u'·')
	for t in ifs:
		if (f,t) in c1 and (f,t) in c2:
			if c1[(f,t)]:
				if c2[(f,t)]:
					stdout.write(u'■')
				else:
					stdout.write(u'◩')
			else:
				if c2[(f,t)]:
					stdout.write(u'◪')
				else:
					stdout.write(u'□')
		else:
			stdout.write(' ')
		stdout.write(u'·')
	stdout.write('\n')

