#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
design genetic algorithm framework

purely functional, immutable variables
lists are assumed to have homogenous members
tuples are assumed to have heterogenous members
support lambda, higher-order functions, TypeVars

TODO: all Expr.exprs should be wrapped in Value()

slowest features:
	lots of deepcopy()s for mutations
	Type.match() called a lot

"""

import random
from test import unittest
from copy import copy,deepcopy
import math
import time

class Type:
	A     = 0
	B     = 1
	BOOL  = 3
	NUM   = 4
	FUN   = 5
	def __init__(self, type):
		self.type = type
	@staticmethod
	def is_scalar(type):
		return type in (Type.BOOL, Type.NUM)
	@staticmethod
	def is_typevar(t):
		return t in (Type.A, Type.B)
	@staticmethod
	def match(spec, t):
		#print('match(spec=',spec,'t=',t,')')
		return (spec == t or Type.is_typevar(spec) or
		# recursively match non-scalar types
		(type(spec) == type(t) and not Type.is_scalar(spec) and len(spec) == len(t) and all([Type.match(x,y) for x,y in zip(spec,t)])))
	@staticmethod
	def repr(t):
		if t == Type.A:
			return 'A'
		elif t == Type.B:
			return 'B'
		elif t == Type.BOOL:
			return 'Bool'
		elif t == Type.NUM:
			return 'Num'
		elif type(t) == tuple:
			return '(' + ','.join([Type.repr(x) for x in t]) + ')'
		elif type(t) == list:
			return '[' + (Type.repr(t[0]) if t != [] else '') + ']'
		elif t == Type.FUN:
			return 'Fun'
		else:
			return '??'

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
		#print('typevar_replace typesig=',typesig,'tvs=',tvs)
		if type(typesig) in (tuple,list):
			x = [Type.typevar_replace(t, tvs) for t in typesig]
			if type(typesig) == tuple:
				x = tuple(x)
			return x
		elif Type.is_typevar(typesig):
			return tvs[typesig]
		else:
			return typesig

	def encode_hashable_lists(foo):
		if type(foo) == list:
			return ('list', tuple(Type.encode_hashable_lists(f) for f in foo))
		elif type(foo) == tuple:
			return tuple(Type.encode_hashable_lists(f) for f in foo)
		else:
			return foo

	# return a set() of all non-TypeVar types used
	# i need to distinguish between list and tuples explicitly, and python's set() cannot
	# handle lists. encode them specially.
	@staticmethod
	def make_set(typelist):
		s = []
		for t in typelist:
			if type(t) == list:
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

class Value:
	def __init__(self, type_, val=None):
		self.type = type_
		self.invariant = \
			(val == None) \
			or (type(val) in (bool,int,float)) \
			or (type(val) == tuple and val == ()) \
			or (type(val) == list and val == [])
		if val == None:
			val = self.randomval(type_)
		self.val = val
	@staticmethod
	def randomval(type, val=None):
		if type == Type.NUM:
			return random.randint(1,5)
		elif type == Type.BOOL:
			return random.randint(0,1) == 0
		else:
			return val
	def __repr__(self):
		return str(self.val)
	def mutate(self, _):
		self.val = Value.randomval(self.type, self.val)
	def is_invariant(self):
		return self.invariant
	def dump(self):
		return 'Value(type=%s val=%s invariant=%s)' % (Type.repr(self.type), self.val, self.invariant) 

class Variable(Value):
	def __init__(self, type_, val, index=[]):
		self.type = type_
		self.invariant = False
		self.val = val
		self.index = index
	def mutate(self, _):
		pass
	def __repr__(self):
		return '%s%s' % (self.val, '' if self.index == [] else '['+(']['.join(str(i) for i in self.index))+']')
	def dump(self):
		return 'Variable(type=%s val=%s)' % (Type.repr(self.type), self.val) 

class Op:
	def __init__(self, name, outtype, intype, repr):
		self.name = name
		self.type = outtype
		self.intype = intype
		self.repr = repr
		# TODO: we can greatly simplify Expr() by pre-calculating a bunch of stuff here, also globally about Ops
	def __repr__(self):
		return '%s %s%s' % (Type.repr(self.type), self.name, Type.repr(self.intype))
	# given a set of all possible available types from parameters and other function's output types, see if we match
	def inTypesMatch(self, availableTypes):
		#print(self.name,'inTypesMatch(intype=',self.intype,',availableTypes=',availableTypes,')')
		return any(Type.match(a, self.intype) for a in availableTypes)

Id = Op('id', Type.A, (Type.A,), lambda x: str(x))
# NOTE: at the moment all these functions actually appear to work, I'm just testing various aspects of them
Ops = (
	#Op('not', Type.BOOL,	(Type.BOOL,),			lambda x:    '(not %s)' % (x,)),
	#Op('or',  Type.BOOL,	(Type.BOOL, Type.BOOL),		lambda x,y:  '(%s or %s)' % (x,y)),
	#Op('and', Type.BOOL,	(Type.BOOL, Type.BOOL),		lambda x,y:  '(%s and %s)' % (x,y)),
	#Op('if',  Type.A,	(Type.BOOL, Type.A, Type.A),	lambda x,y,z:'(%s if %s else %s)' % (y,x,z)),
	Op('eq',  Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s == %s)' % (x,y)),
	Op('gt',  Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s > %s)' % (x,y)),
	Op('gte', Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s >= %s)' % (x,y)),
	Op('add', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s + %s)' % (x,y)),
	#Op('sub', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s - %s)' % (x,y)),
	Op('mul', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s * %s)' % (x,y)),
	Op('div', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s / %s)' % (x,y)),
	Op('sqrt', Type.NUM,	(Type.NUM, ),			lambda x:    'math.sqrt(%s)' % (x,)),
	#Op('log', Type.NUM,	(Type.NUM, ),			lambda x:    'math.log(%s)' % (x,)),
	#Op('mod', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s %% %s)' % (x,y)),
	#Op('min', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  'min(%s,%s)' % (x,y)),
	#Op('max', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  'max(%s,%s)' % (x,y)),
	Op('sum', Type.NUM,	([Type.NUM],),			lambda x:    'sum(%s)' % (x,)),
	Op('map', [Type.B],	((Type.FUN,Type.B,(Type.A,)), [Type.A]),	lambda x,y: '[%s for %s in %s]' % (x,','.join(x.op.paramkeys),y)),
	#Op('filter', [Type.A],	((Type.FUN,Type.BOOL,(Type.A,)), [Type.A]),
		#lambda x,y: '[%s for %s in %s if %s]' % (','.join(x.op.paramkeys),','.join(x.op.paramkeys),y,x)),
	Op('len', Type.NUM,	([Type.A],),				lambda x:    'len(%s)' % (x,)),

	# date/time-related operations
	# these must be implemented for real analysis
	#Op('year', Type.NUM,	(Type.DATE,),				lambda x:    '%s.year' % (x,)),
	#Op('month', Type.NUM,	(Type.DATE,),				lambda x:    '%s.month' % (x,)),
	#Op('mday', Type.NUM,	(Type.DATE,),				lambda x:    '%s.mday' % (x,)),
	#Op('hour', Type.NUM,	(Type.DATE,),				lambda x:    '%s.hour' % (x,)),
	#Op('wday', Type.NUM,	(Type.DATE,),				lambda x:    '%s.weekday()' % (x,)),
)

OpOuttypes = [Type.BOOL,Type.NUM,Type.A,[Type.A]]

OpOuttypeDict = {} # cache Op outtype lookup
def ops_by_outtype(outtype):
	hasht = Type.encode_hashable_lists(outtype)
	try:
		return OpOuttypeDict[hasht]
	except KeyError:
		v = tuple(o for o in Ops if Type.match(o.type, outtype))
		OpOuttypeDict[hasht] = v
		return v

class Lambda(Op):
	def __init__(self, outtype, intype, params):
		self.name = 'lambda'
		self.type = outtype
		self.intype = intype
		self.params = params
		self.paramkeys = [v.val for v in params]
	def repr(self, expr):
		return str(expr)
	def dump(self):
		return 'Lambda()'

# pre-calculate logarithm
Log = tuple([0, math.log(2)] + [math.log(n) for n in range(2, 100)])

# Expression is a value that applies a function to parameters to arrive at its value
class Expr(Value):

	# generate a random expression that generates a value of type 'outtype'
	# expression may be arbitrarily complex, but may only reference parameters, pre-defined Ops and random literals
	# @params tuple(Variable)
	# @outtype is a realized Type.X type, not a TypeVar.
	def __init__(self, params, outtype, depth=1, maxdepth=5):
		#print('Expr(params=',params,'outtype=',outtype,')')
		self.depth = depth
		self.params = copy(params)
		self.type = copy(outtype)
		self.exprs = []

		# special case for lambdas
		if type(outtype) == tuple and outtype[0] == Type.FUN:
			_,outp,inp = outtype
			# if we're generating a list-processing lambda, strip the list type off the input/output types
			if type(outp) == list:
				outp = outp[0]
			#print('created lambda inp=%s outp=%s' % (inp, outp))
			# reduce parameters to those being passed specifically, and rename for use within the function
			self.params = tuple(Variable(v,k) for k,v in zip(['x','y','z'], inp))
			self.op = Lambda(outp, inp, self.params)
			self.exprs = [Expr(self.params, outp, depth+1)]
			return

		opt = ops_by_outtype(outtype)
		#print('opt=',opt)
		r = random.random()
		if opt == () or depth == maxdepth or r < Log[depth] / Log[maxdepth]:
			pt = Expr.params_by_type(params, outtype)
			#print('pt=',pt)
			# generate a literal or variable, out of chance or because we have to
			self.op = Id
			if pt == () or (outtype != Type.BOOL and r < Log[depth]/Log[maxdepth]/10):
				if Type.is_scalar(outtype):
					self.exprs = [Value(outtype)] # random literal
				elif type(outtype) == tuple: # tuple literal
					self.exprs = [tuple(Expr(params, t, depth+1) for t in self.type)]
				else: # list literal
					# FIXME: do not wrap in a list if it's already a list....
					x = [Expr(params, t, depth+1) for t in self.type]
					if len(x) == 1 and type(x[0].type) == list:
						x = x[0] # unwrap
					self.exprs = [x]
			else:
				# random parameter
				#print('outtype=',outtype,'pt=',pt)
				self.exprs = [random.choice(pt)]
		else:
			# only choose operations whose output matches our input and whose input
			# we can possibly supply with our parameters
			paramtypes = [x.type for x in Expr.params_by_type(params, Type.A)]
			availableTypes = OpOuttypes + paramtypes
			okops = [o for o in opt if o.inTypesMatch(availableTypes)]
			if okops == []:
				print('outtype=',outtype,'opt=',opt,'params=',params)
				print('paramtypes=',paramtypes,'OpOuttypes=',OpOuttypes,'availableTypes=',availableTypes)
				assert False
			self.op = deepcopy(random.choice(okops))
			tvtypes = self.enforceTypeVars(outtype)
			#print('self.op=',self.op, 'outtype=',outtype,'tvtypes=',tvtypes)
			self.exprs = [Expr(params, it, depth+1) for it in self.op.intype]

	# randomly mutate myself or one of my child expressions
	# TODO: modify mutate() to allow it to maybe use existing expr as part of new expr, i.e. 1+2 -> (1+2)+3
	# this would allow expressions to be built up iteratively
	def mutate(self, mutation=0.5):
		r = random.random()
		if r < mutation: # mutate self
			e = Expr(self.params, self.type, self.depth)
			if r < mutation * (1/2):
				# preserve self as parameter to e
				i = random.randint(0, len(e.exprs)-1)
				if (hasattr(e.exprs[i],'type') and e.exprs[i].type == self.type) or type(e.exprs[i]) == self.type:
					e.exprs[i] = deepcopy(self)
			return e
		else: # maybe mutate child
			mutatable = tuple(e for e in self.exprs if hasattr(e,'mutate'))
			if mutatable != ():
				random.choice(mutatable).mutate(mutation)
		return self

	def is_invariant(self):
		ei = [(not hasattr(e,'is_invariant') or e.is_invariant()) for e in self.exprs]
		if self.op.name == 'map':
			return str(self.exprs[0]) == str(self.exprs[0].op.paramkeys[0])
		elif self.op.name in ('if','filter'):
			return ei[0]
		else:
			return all(ei)

	def invariant_val(self):
		if type(self.exprs[0]) == Value:
			return self.exprs[0].val
		elif hasattr(self.exprs[0], 'invariant_val'):
			return self.exprs[0].invariant_val()
		else:
			return self.exprs[0]

	def dump(self):
		return 'Expr(op=%s outtype=%s invariant=%s exprs=[%s])' % \
			(self.op.name, Type.repr(self.type), self.is_invariant(), \
			','.join([e.dump() if hasattr(e,'dump') else '(type='+str(type(e))+' '+str(e)+')' for e in self.exprs]))

	# reduce expressions to their simplified, canonical form
	def canonicalize(self):
		self.exprs = [e.canonicalize() if hasattr(e,'canonicalize') else e for e in self.exprs]
		if self.op is Id or self.op.name in ('add','sub','mul','div'):
			try:
				e = eval(str(self))
				# if it doesn't blow up, it's been canonicalized...
				self.exprs = [Value(self.type, e)]
				self.op = Id
			except:
				pass
		elif self.op.name in ('gt','lt'):
			if str(self.exprs[0]) == str(self.exprs[1]):
				# foo > foo -> False
				self.op = Id
				self.exprs = [Value(Type.BOOL, False)]
		elif self.op.name in ('eq','lte','gte'):
			if str(self.exprs[0]) == str(self.exprs[1]):
				# x == x -> True
				self.op = Id
				self.exprs = [Value(Type.BOOL, True)]
		elif self.op.name == 'if':
			v = self.exprs[0].invariant_val()
			if v == True:
				self = self.exprs[1]
			elif v == False:
				self = self.exprs[2]
		elif self.is_invariant():
			if self.op.name == 'map':
				# [x for x in y] -> y
				self = self.exprs[1]
			elif self.op.name == 'filter':
				v = self.exprs[0].invariant_val()
				if v == True:
					# filter(True, x) -> x
					self = self.exprs[1]
				elif v == False:
					# filter(False, x) -> []
					self.exprs = [Value(self.exprs[1].type, [])]
					self.op = Id
		return self

	def __repr__(self):
		return self.op.repr(*self.exprs)
	def __lt__(self, other):
		return 0
	def __gt__(self, other):
		return 1

	# once an op is chosen, we must choose specific types for any TypeVars present (based on params)
	# also, we must respect the outtype if it is a TypeVar
	# FIXME: we're not properly adjusting lambda's type from typevar, should be stripping list off
	def enforceTypeVars(self, outtype):
		# if we're a lambda then our input and output types are already dictated
		paramtypelist = [x.type for x in self.params]
		tvs = Type.typevars((self.op.intype, self.op.type))
		tvtypes = dict([(tv,None) for tv in tvs])
		if type(self.op.intype[0]) == tuple and self.op.intype[0][0] == Type.FUN:
			if type(self.op.type) == list and Type.is_typevar(self.op.type[0]):
				tvtypes[self.op.type[0]] = outtype[0]
				# FIXME: this is the contentious line... without [0] we get garbage, with [0] we finish quickly like we should, but with the wrong answer
				x = random.choice(paramtypelist)
				if type(x) == list:
					x = x[0]
				tvtypes[self.op.intype[1][0]] = x
		else:
			# select random type for each, based on paramtypes
			for tv in tvtypes.keys():
				tvtypes[tv] = outtype if tv == self.op.type else random.choice(paramtypelist)
		# replace inputtype TypeVar instances with translations

		#print('op.name=%s outtype=%s self.op.intype=%s paramtypelist=%s' % (self.op.name, Type.repr(outtype), Type.repr(self.op.intype), paramtypelist))

		intypes = Type.typevar_replace(self.op.intype, tvtypes)
		if type(self.op.intype) == tuple:
			intypes = tuple(intypes)
		self.op.intype = intypes
		self.op.type = Type.typevar_replace(self.op.type, tvtypes)

		#if type(self.op.intype[0]) == tuple and self.op.intype[0][0] == Type.FUN:
			#print('op.name=%s type=%s op.type=%s op.intype=%s paramtypelist=%s' % (self.op.name, Type.repr(outtype), Type.repr(self.op.type),Type.repr(self.op.intype), paramtypelist))
			#assert type(self.op.type) != list
		return tvtypes

	# given a set of parameters, do we
	@staticmethod
	def paramlist_match_types(paramtypes, intypes):
		pass

	@staticmethod
	def params_by_type(params, t):
		#print('params_by_type params=',params)
		pt = []
		for p in params:
			if Type.match(t, p.type):
				pt.append(p)
			elif type(p.type) == tuple:
				# one level deep in tuples
				pt += [Variable(x, p.val, [i]) for i,x in enumerate(p.type) if Type.match(t, x)]
		return tuple(pt)

	# count the number of total nodes
	@staticmethod
	def size(e):
		return 1 + sum([Expr.size(e) for e in e.exprs]) if hasattr(e,'exprs') else 0

	# count the number of random literals
	@staticmethod
	def magic_numbers(e):
		if type(e) != Expr:
			return int(type(e) == Value)
		elif e.op is Id:
			return int(type(e.exprs[0]) == Value)
		else:
			return sum([Expr.magic_numbers(x) for x in e.exprs])

def test_type_describe():
	assert unittest(Type.describe,
			[(Type.BOOL,			(True,)),
			 (Type.BOOL,			(False,)),
			 (Type.NUM,			(0,)),
			 (Type.NUM,			(1.,)),
			 ((Type.NUM,Type.NUM),		((0,1.),)),
			 ([(Type.NUM,)],		([(0,)],)),
			])

def test_expr_invariant():
	v = Value(Type.BOOL, True)
	assert v.is_invariant()
	e = Expr((Variable(Type.BOOL,'a'),), Type.BOOL)
	e.exprs = [v]
	assert e.is_invariant()

def test_enforceTypeVars():
	e = Expr((Variable([(Type.NUM,Type.NUM)],'foo'),),[Type.NUM])
	#print(e.enforceTypeVars(e.type))
	#print(e.type)
	#print('e=',e)

def test():
	test_type_describe()
	test_expr_invariant()
	tv = Type.typevars(((Type.FUN, Type.B, (Type.A,)), [Type.A]))
	assert tv == list(set([1,0]))
	test_enforceTypeVars()
	print('Tests passed.')

"""
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
			res = eval('lambda foo:'+str(p))(d[0])
			fs = fscore(d, res)
			#print('d=%s res=%s -> %s' %(d,res,fs))
			score += fs
	except:
		# whoops, blew up. shouldn't happen, but hey.
		# assign worst possible score, keep going
		score = WorstScore
	#print('score=',score)
	return score

class KeepScore:
	def __init__(self, p, score, gencnt):
		self.p = p
		self.score = score
		self.gencnt = gencnt
		self.size = Expr.size(p)
		self.magic_numbers = Expr.magic_numbers(p)
	def __repr__(self):
		return 'score=%u size=%u magic=%u gencnt=%u %s' % \
			(self.score, self.size, self.magic_numbers, self.gencnt, self.p)
	def __lt__(self, other):
		if self.score != other.score:
			return self.score < other.score	
		if self.size != other.size:
			return self.size < other.size
		if self.magic_numbers != other.magic_numbers:
			return self.magic_numbers < other.magic_numbers
		if self.gencnt != other.gencnt:
			return self.gencnt < other.gencnt
		return 0

# run each candidate against the data, score the results, keep the least-awful scoring functions
def evaluate(population, data, fscore, gencnt):
	keep = []
	for p in population:
		if not p.is_invariant():
			score = run_score(p, data, fscore)
			if score != WorstScore:
				# retain 3 scores. lower is always better, and sorted() works that way too
				p = p.canonicalize()
				if not p.is_invariant():
					keep.append(KeepScore(p, score, gencnt))
	return sorted(keep)

def evolve(data, score=lambda d,res:abs(d[1]-res), types=None, popsize=10000, maxdepth=10, popkeep=2, mutation=0.7, deadend=0):
	# sanity check types and ranges
	assert type(data[0]) == tuple
	assert type(score) == type(lambda _:_)
	assert 2 <= maxdepth < len(Log)
	assert 1 <= popsize
	assert 1 <= popkeep
	# initialize defaults
	if types == None:
		intype,outtype = Type.describe(data[0])
		print('evolve :: %s -> %s' % (Type.repr(intype),Type.repr(outtype)))
	else:
		intype,outtype = types
	sym = (Variable(intype, 'foo'),)
	pop = []
	gencnt = 0

	# find at least one func that doesn't totally suck
	while pop == []:
		population = (Expr(sym, outtype, maxdepth=maxdepth) for _ in range(0, popsize))
		keep = evaluate(population, data, score, gencnt)[:popkeep]
		pop = sorted(pop + keep)[:popkeep]
		print('gen %d' % (gencnt,))
		gencnt += 1

	# mutate those functions
	while pop[0].score > 0:
		population = (deepcopy(random.choice(pop).p).mutate(mutation=mutation) for _ in range(0, popsize))
		keep = evaluate(population, data, score, gencnt)[:popkeep]
		pop = sorted(pop + keep)[:popkeep]
		t = time.localtime()
		print('%04d-%02d-%02d-%02d:%02d:%02d gen %u %s %s' % \
			(t.tm_year, t.tm_mon, t.tm_mday, t.tm_hour, t.tm_min, t.tm_sec,
			 gencnt, '#' * round(math.log(pop[0].score+1)+0.5), str(pop[0])))
		assert not pop[0].p.is_invariant()
		gencnt += 1

	print('done', pop[0])
	return pop[0]

import profile

if __name__ == '__main__':
	test()


	evolve( [
			# expect: foo
			(10, 10),
			(1e6, 1e6),
		],
		popsize=1000)

	evolve( [
			# expect: ((foo+foo)+1) or ((foo*2)+1)
			# got:    ((1 + foo) + foo)
			#         (foo + (1 + foo))
			(10, 21),
			(1e6, 1e6*2+1),
		],
		popsize=2000)

	evolve( [
			# expect: sum([x[0] for x in foo])
			# got: sum([sum([x[0]]) for x in foo])
			([(10,1)], 10),
			([(20,1)], 20),
		],
		popsize=3000)

	evolve( [
			# expect: sum([(x[0]+x[1]+x[2]+x[3])/len(x) for x in foo])
			# or maybe: sum([x[0]/2 for x in foo])
			# GOT: (sum([x[0] for x in foo]) / 2)
			#      (0.5 * sum([x[0] for x in foo]))
			([(5,0,2,3)], 2.5),
			([(50,0,50,0)], 25),
			([(2,0,0,2)], 1),
		],
		popsize=5000)

	evolve( [
			# expect: sum([x[0]*x[1]+x[2] for x in foo])
			# GOT: (sum([x[2] for x in foo]) + sum([(x[1] * x[0]) for x in foo]))
			#      (sum([(x[1] * x[0]) for x in foo]) + sum([x[2] for x in foo]))
			([(10,3,5)], 10*3+5),
			([(3,3,1)], 3*3+1),
			([(2,1,0)], 2*1+0),
			([(1000,50,55)], 1000*50+55),
		])

	evolve( [
			# expect: sum([(x[0]+x[1]+x[2]+x[3])/4 for x in foo])
			# GOT: ((sum([x[3] for x in foo]) / 2) + (sum([x[1] for x in foo]) / sum([5])))
			([(0,5,2,3)], 2.5),
			([(0,0,50,50)], 25),
			([(2,0,0,2)], 1),
		],
		maxdepth=10, popkeep=5)

	################ Beyond this point stuff doesn't work

	# FIXME: this never works
	# ensure we can produce tuple results
	evolve( [
			# expect: (foo,)
			(100, (100,)),
			(1000, (1000,)),
		],
		score=lambda d,res:abs(d[1][0]-res[0]),
		maxdepth=3)

	evolve( [
			# FIXME: need this exact code to flatten list, but my code can't generate it!
			# expect: [y for y in x for x in foo]
			# GOT: 
			([[1,2,3]], [1,2,3]),
		],
		score=lambda d,res: sum([abs(x-y) for x,y in zip(d[1], res)]) + (1e6 * abs(len(d[1])-len(res))))

