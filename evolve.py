#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
design genetic algorithm framework

purely functional, immutable variables
lists are assumed to have homogenous members
tuples are assumed to have heterogenous members
support lambda, higher-order functions, TypeVars

"""

import random
from test import unittest
from copy import copy,deepcopy
import math

class Type:
	A     = 0
	B     = 1
	C     = 2
	BOOL  = 3 # TODO: you know, maybe i can just use bool; won't work between python2/3 though...
	NUM   = 4
	FUN   = 5
	def __init__(self, type):
		self.type = type
	@staticmethod
	def is_scalar(type):
		return type in (Type.BOOL, Type.NUM)
	@staticmethod
	def is_typevar(t):
		return t in (Type.A, Type.B, Type.C)
	@staticmethod
	def match(spec, t):
		#print('match(spec=',spec,'t=',t,')')
		return (spec == t or Type.is_typevar(spec) or
		# recursively match non-scalar types
		(type(spec) == type(t) and not Type.is_scalar(spec) and len(spec) == len(t) and all([Type.match(x,y) for x,y in zip(spec,t)])))

	# return a list of all unique typevars in a potentially-multi-level type signature
	@staticmethod
	def typevars(typesig):
		if type(typesig) not in (list,tuple):
			if Type.is_typevar(typesig):
				return [typesig]
			else:
				return []
		tvs = []
		for t in typesig:
			if type(t) in (tuple,list):
				tvs += Type.typevars(t)
			elif Type.is_typevar(t):
				tvs.append(t)
		return list(set(tvs))

	# given a type signature and a tvs=dict{tv:type} perform replacement
	@staticmethod
	def typevar_replace(typesig, tvs):
		if type(typesig) in (tuple,list):
			x = [Type.typevar_replace(t, tvs) for t in typesig]
			if type(typesig) == tuple:
				x = tuple(x)
			return x
		elif Type.is_typevar(typesig):
			return tvs[typesig]
		else:
			return typesig

	# return a set() of all non-TypeVar types used
	# i need to distinguish between list and tuples explicitly, and python's set() cannot
	# handle lists. encode them specially.
	@staticmethod
	def make_set(typelist):
		s = []
		for t in typelist:
			if Type.is_typevar(t):
				continue
			if type(t) == list:
				nontv = tuple(x for x in t if not Type.is_typevar(x))
				if nontv != ():
					s.append(('list',tuple(t)))
			elif type(t) == tuple and t[0] == Type.FUN:
				# add function parameter types
				s += [x for x in t[2] if not Type.is_typevar(x)]
			else:
				s.append(t)
		return set(s)
		
	def describe(v):
		if type(v) == bool:
			return Type.BOOL
		elif type(v) in (int,float):
			return Type.NUM
		elif type(v) == tuple:
			# tuples are assumed heterogenous, describe each item
			return tuple(Type.describe(x) for x in v)
		elif type(v) == list:
			# lists are assumed homogenous, describe first item only
			return [Type.describe(v[0])]
	@staticmethod
	def repr(t):
		if t == Type.A:
			return 'A'
		elif t == Type.B:
			return 'B'
		elif t == Type.C:
			return 'C'
		elif t == Type.BOOL:
			return 'Bool'
		elif t == Type.NUM:
			return 'Num'
		elif type(t) == tuple:
			return '(' + ','.join([Type.repr(x) for x in t]) + ')'
		elif type(t) == list:
			return '[' + Type.repr(t[0]) + ']'
		elif t == Type.FUN:
			return 'Fun'
		else:
			return '??'

class Value:
	def __init__(self, type, val=None):
		self.type = type
		if val == None:
			val = self.randomval(type)
		self.val = val
	@staticmethod
	def randomval(type):
		if type == Type.NUM:
			return random.randint(1,5)
		elif type == Type.BOOL:
			return random.randint(0,1) == 0
		else:
			print('Unexpected type=',type)
			assert False
	def __repr__(self):
		return '%s' % (self.val,)

class Op:
	def __init__(self, name, outtype, intype, repr):
		self.name = name
		self.outtype = outtype
		self.intype = intype
		self.repr = repr
		self.intypeset = Type.make_set(intype)
		# TODO: we can greatly simplify Expr() by pre-calculating a bunch of stuff here, also globally about Ops
	def __repr__(self):
		return '%s %s%s' % (Type.repr(self.outtype), self.name, Type.repr(self.intype))
	# given a set of all possible available types from parameters and other function's output types, see if we match
	def inTypesMatch(self, availableTypes):
		# FIXME: this is overly simplistic regarding lambda/FUNs
		#print('inTypesMatch(intypeset=',self.intypeset,',availableTypes=',availableTypes,')')
		return self.intypeset <= availableTypes

Id = Op('id', Type.A, (Type.A,), lambda x: '%s' % (x,))
# NOTE: at the moment all these functions actually appear to work, I'm just testing various aspects of them
Ops = (
	Op('eq',  Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s == %s)' % (x,y)),
	Op('gt',  Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s > %s)' % (x,y)),
	Op('gte', Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s >= %s)' % (x,y)),
	Op('lt',  Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s < %s)' % (x,y)),
	Op('lte', Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s <= %s)' % (x,y)),
	Op('add', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s + %s)' % (x,y)),
	Op('sub', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s - %s)' % (x,y)),
	Op('mul', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s * %s)' % (x,y)),
	Op('div', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s / %s)' % (x,y)),
	Op('mod', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s %% %s)' % (x,y)),
	Op('min', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  'min(%s,%s)' % (x,y)),
	Op('max', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  'max(%s,%s)' % (x,y)),
	Op('if',  Type.A,	(Type.BOOL, Type.A, Type.A),	lambda x,y,z:'(%s if %s else %s)' % (y,x,z)),
	Op('sum', Type.NUM,	([Type.NUM],),			lambda x:    'sum(%s)' % (x,)),
	Op('map', [Type.B],	((Type.FUN,Type.B,(Type.A,)), [Type.A]),	lambda x,y: 'list(map(%s, %s))' % (x,y)),
	Op('filter', [Type.A],	((Type.FUN,Type.BOOL,(Type.A,)), [Type.A]),	lambda x,y: 'list(filter(%s, %s))' % (x,y)),
	#Op('len', Type.NUM,	([Type.A],),				lambda x:    'len(%s)' % (x,)),
)

OpOuttypes = Type.make_set([o.outtype for o in Ops])

class Lambda(Op):
	def __init__(self, outtype, intype, params):
		self.name = 'lambda'
		self.outtype = outtype
		self.intype = intype
		self.params = params
	def repr(self, expr):
		return 'lambda %s:%s' % (','.join(sorted(self.params.keys())), expr)

# pre-calculate logarithm
Log = tuple([0, math.log(2)] + [math.log(n) for n in range(2, 100)])

"""
Expression is a value that applies a function to parameters to arrive at its value
"""
class Expr(Value):
	# generate a random expression that generates a value of type 'outtype'
	# expression may be arbitrarily complex, but may only reference parameters, pre-defined Ops and random literals
	# @params dict{varname : type}
	# @outtype is a realized Type.X type, not a TypeVar.
	def __init__(self, params, outtype, depth=1, maxdepth=5):
		#print('Expr(params=',params,'outtype=',outtype,')')
		self.params = copy(params)
		self.outtype = copy(outtype)

		# special case for lambdas
		if type(outtype) == tuple and outtype[0] == Type.FUN:
			_,outp,inp = outtype
			# if we're generating a list-processing lambda, strip the list wrappers off the input/output types
			if type(inp[0]) == list and type(outp) == list:
				inp = (inp[0][0],)
				outp = outp[0]
			#print('created lambda inp=%s outp=%s' % (inp, outp))
			# reduce parameters to those being passed specifically, and rename for use within the function
			self.params = dict(zip(['x','y','z'], inp))
			self.op = Lambda(outp, inp, self.params)
			self.exprs = [Expr(self.params, outp, depth+1)]
			return

		# figure out all possible variables and ops that provide type 'outtype'
		opt = [o for o in Ops if Type.match(o.outtype, outtype)]
		#print('opt=',opt)
		r = random.random()
		if opt == [] or depth == maxdepth or r < Log[depth]/Log[maxdepth]:
			pt = Expr.params_by_type(params, outtype)
			# generate a literal or variable, out of chance or because we have to
			self.op = Id
			if pt == [] or r < 0.1:
				if Type.is_scalar(outtype):
					self.exprs = [Value(outtype)] # random literal
				elif type(outtype) == tuple: # tuple literal
					self.exprs = [tuple(Expr(params, t, depth+1) for t in self.outtype)]
				else: # list literal
					self.exprs = [[Expr(params, t, depth+1) for t in self.outtype]]
			else:
				# random parameter
				#print('outtype=',outtype,'pt=',pt)
				self.exprs = [random.choice(pt)]
		else:
			# only choose operations whose output matches our input and whose input
			# we can possibly supply with our parameters
			paramtypes = Type.make_set(params.values())
			availableTypes = OpOuttypes | paramtypes
			# treat
			# FIXME: this should take functions' output into account, if() isn't being chosen because we don't
			# have any explicitly bool vars, but plenty of functions produce them
			# TODO: this will have to change to accomodate TypeVars
			okops = [o for o in opt if o.inTypesMatch(availableTypes)]
			if okops == []:
				print('availableTypes=',availableTypes)
				assert False
			self.op = deepcopy(random.choice(okops))
			tvtypes = self.enforceTypeVars(outtype)
			#print('self.op=',self.op, 'outtype=',outtype,'tvtypes=',tvtypes)
			self.exprs = [Expr(params, it, depth+1) for it in self.op.intype]

	def __repr__(self):
		return self.op.repr(*self.exprs)
	def __lt__(self, other):
		return 1

	# once an op is chosen, we must choose specific types for any TypeVars present (based on params)
	# also, we must respect the outtype if it is a TypeVar
	# NOTE: only replaces TypeVars with scalar types
	def enforceTypeVars(self, outtype):
		# if we're a lambda then our input and output types are already dictated
		if type(self.op.intype[0]) == tuple and self.op.intype[0][0] == Type.FUN:
			tvtypes = {}
			if type(self.op.outtype) == list and Type.is_typevar(self.op.outtype[0]):
				tvtypes[self.op.outtype[0]] = outtype[0]
				tvtypes[self.op.intype[1][0]] = outtype[0]
		else:
			#paramtypelist = Expr.scalar_param_types(self.params) #if self.op != Type.FUN else Expr.fun_param_types(self.params)
			paramtypelist = list(self.params.values()) #if self.op != Type.FUN else Expr.fun_param_types(self.params)
			tvs = Type.typevars((self.op.intype, self.op.outtype))
			tvtypes = dict([(tv,None) for tv in tvs])
			# select random type for each, based on paramtypes
			for tv in tvtypes.keys():
				tvtypes[tv] = outtype if tv == self.op.outtype else random.choice(paramtypelist)
		# replace inputtype TypeVar instances with translations
		intypes = Type.typevar_replace(self.op.intype, tvtypes)
		if type(self.op.intype) == tuple:
			intypes = tuple(intypes)
		self.op.intype = intypes
		self.op.outtype = Type.typevar_replace(self.op.outtype, tvtypes)
		#print('outtype=%s intype=%s paramtypelist=%s' % (Type.repr(self.op.outtype),Type.repr(self.op.intype), paramtypelist))
		return tvtypes

	# given a set of parameters, do we
	@staticmethod
	def paramlist_match_types(paramtypes, intypes):
		pass

	# return a list of parameter keys (strings) of parameters matching type 't'
	# FIXME: there must be a cleaner way
	@staticmethod
	def params_by_type(params, t):
		p = []
		for k,v in params.items():
			if Type.match(t, v):
				p.append(k)
			elif type(v) == tuple:
				# one level deep in tuples
				for i in range(0, len(v)):
					if Type.match(t, v[i]):
						p.append('%s[%d]' % (k,i))
		return p

	# FUNs can take non-scalar parameters; but we have to strip off the [list] wrapping
	# TODO: technically we only need to 
	@staticmethod
	def fun_param_types(params):
		return []

	#
	# Expr scoring methods
	#

	# count the number of total nodes
	@staticmethod
	def size(e):
		if e.op is Id:
			return 1
		else:
			return sum([Expr.size(x) for x in e.exprs])

	# count the number of random literals
	@staticmethod
	def magic_numbers(e):
		if e.op is Id:
			return int(type(e.exprs[0]) == Value)
		else:
			return sum([Expr.magic_numbers(x) for x in e.exprs])

# Given an existing Expr, mutate a section of it
class Mutant(Expr):
	def __init__(self, parent, sym, outtype, depth=1, maxdepth=5, mutation=0.3):
		pass

def test_params_by_type():
	assert unittest(Expr.params_by_type,
			[([],				({},				Type.NUM)),
			 (['x'],			({'x':Type.NUM},		Type.NUM)),
			 (['x'],			({'x':Type.NUM,'y':Type.BOOL},	Type.NUM)),
			 (list({'x':0,'y':0}.keys()),	({'x':Type.NUM,'y':Type.NUM},	Type.NUM)),
			 (['x[0]'],			({'x':(Type.NUM,)},		Type.NUM)),
			 (['x[0]','x[1]'],		({'x':(Type.NUM, Type.NUM)},	Type.NUM)),
			])

def test_type_describe():
	assert unittest(Type.describe,
			[(Type.BOOL,			(True,)),
			 (Type.BOOL,			(False,)),
			 (Type.NUM,			(0,)),
			 (Type.NUM,			(1.,)),
			 ((Type.NUM,Type.NUM),		((0,1.),)),
			 ([(Type.NUM,)],		([(0,)],)),
			])

def test():
	test_params_by_type()
	test_type_describe()
	tv = Type.typevars(((Type.FUN, Type.B, (Type.A,)), [Type.A]))
	assert tv == list(set([1,0]))

"""
our true goal is to be able to pass in a list of tuples/lists:
	in = [ (x0,y0,z0),(x1,y1,z1),..,(xn,yn,zn) ]
	out = scalar

we'll also need custom datatype:Date and methods
	Date(year, month=0, day=0, hour=0, min=0, sec=0)
	==, >, <, >=, <=
	Date-Date
	Date.weekday

for the Netflix challenge it would be even more challenging...
"""

WorstScore = float('inf')

import sys
import traceback

# run Expr e(data), score the result
def run_score(p, data, fscore):
	try:
		score = 0
		for d in data:
			foo = d # FIXME: tied to sym{} in evolve()
			res = eval(str(p)) # should read 'foo' from current binding, messy
			score += fscore(d, res)
	except:
		#print(str(p))
		#traceback.print_tb(sys.exc_info())
		# whoops, blew up. shouldn't happen, but hey.
		# give it the worst possible score and keep going
		score = WorstScore
	#print('score=',score)
	return score

# run each candidate against the data, score the results, keep the least-awful scoring functions
def evaluate(population, data, fscore):
	keep = []
	for p in population:
		score = run_score(p, data, fscore)
		if score != WorstScore:
			# retain 3 scores. lower is always better, and sorted() works that way too
			keep.append((score, Expr.size(p), Expr.magic_numbers(p), p))
	return sorted(keep)

def evolve(data, score, types=None, popsize=10000, maxdepth=10, popkeep=2, mutation=0.7, deadend=0):
	# sanity check types and ranges
	assert type(data[0]) == tuple
	assert type(score) == type(lambda _:_)
	assert 2 <= maxdepth < len(Log)
	assert 100 <= popsize <= 1e6
	assert 1 <= popkeep
	# initialize defaults
	if types == None:
		intype,outtype = Type.describe(data[0][0])
	else:
		intype,outtype = types
	sym = {'foo':intype} # FIXME: tied to run_score()
	print('sym=',sym)
	pop = []
	gencnt = 0
	# find at least one func that doesn't totally suck
	while pop == [] or pop[0][0] > 0 or pop[0][2] > 1:
		population = [Expr(sym, outtype, maxdepth=maxdepth) for _ in range(0, popsize)]
		keep = evaluate(population, data, score)[:popkeep]
		pop = sorted(pop + keep)[:popkeep]
		print(pop)
		print('gen %d score=%.0f %s' % \
			(gencnt, pop[0][0] if pop != [] else float('inf'), str(pop[0][3]) if pop != [] else None))
		gencnt += 1

	print('done', pop[0])
	return pop[0]

if __name__ == '__main__':
	test()
	sym = {'a':[(Type.NUM,Type.NUM,Type.NUM)]}
	a = [(1,2,3),(4,5,6)]
	e = [Expr(sym, Type.NUM) for _ in range(0, 10)]
	# NOTE: it would be cleaner to wrap everything in a lambda() so we could pass params in directly
	
	evolve(
		[
			# input     expected
			# FIXME: it can't handle [(...)] for some reason...
			((0,0,0), 0),
			((0,1,2), 2),
			((2,3,4), 4),
			((3,4,100), 100),
		],
		# scoring function run on each 
		lambda data,res: abs(max(data[0]) - res),
		# in type                        # output type
		((Type.NUM,Type.NUM,Type.NUM), Type.NUM),
		popsize=3000,
		maxdepth=10,
		popkeep=5
	)

