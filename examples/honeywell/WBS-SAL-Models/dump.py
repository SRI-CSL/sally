import os
import sys
import string
import re
import getopt
import sys


def build_keys(keyfile):
	filter_lines = open(keyfile).readlines()
	filters = []
	for f in filter_lines:
	    if f[0] == '#' : continue
   	    fil = []
	    for x in string.split(f,","):
		    fil.append(x.strip())
	    filters.append(fil)
	return filters



def filter_file(inputfile,filters):
	lines = open(inputfile).readlines()

	for l in lines:
	    for f in filters:
	#	print f, l, string.find(l,f.strip())
			if len(f) == 1 :
				if string.find(l,f[0])> -1:
					print l.strip()
			if len(f) == 2:
				if string.find(l,f[0])> -1 and string.find(l,f[1])> -1: 
					print l.strip()

def main(argv):
	inputfile = None
	keyfile = None
	try:
		opts, args = getopt.getopt(argv,'i:k:h',['ifile=','kfile=','help'])
		print opts,args
	except getopt.GetoptError:
		print 'dump.py -i <inputfile>  -k <keyfile>'
		sys.exit(2)
	for opt, arg in opts:
		if opt == '-h':
			print 'Usage : dump.py -i <inputfile> -k <keyfilename>'
			sys.exit()
		elif opt in ('-i', '--ifile'):
			inputfile = arg
		elif opt in ('-k', '--kfile'):
			keyfile = arg
	print inputfile,keyfile
	if inputfile == None or keyfile == None:
		print 'Usage : dump.py -i <inputfile> -k <keyfile> '
		sys.exit()
	keys = build_keys(keyfile)
	filter_file(inputfile,keys)



if __name__ == "__main__":
	main(sys.argv[1:])	