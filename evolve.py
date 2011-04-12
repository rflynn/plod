#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
simple genetic algorithm framework

given data, evolve transformation
lists types assumed homogenous
tuple types assumed homogenous

TODO:
	* statistically analyze input beforehand to seed random values

		What I really want for Expr variables/values is to associate value
		distributions with them, to seed/influence random values

		datetime:foo
			num:foo.year (min=x max=y vals={...})
			num:foo.month (min=x max=y vals={...})
			num:foo.day (min=x max=y vals={...})
		then the question is how to use the associated distributions?
		currently there is no tracking of what i'm comparing

	* serialize Expr to sqlite3 database so as to persist complex calculations
	  between program invocations

	* allow human intervention. allow a human to retrieve, edit and propose a
	  mutation to an existing Expr. if better, integrate into the Expr's tree
"""

UsePool = True
Debug = False

import sys
import copy
import time
import random
import math
from math import sqrt,log
from test import unittest # custom
from functools import reduce
from datetime import datetime # we need a datetime type for real-world data
import os
import collections

class Type:
	A     = 0 # TypeVar
	B     = 1 # TypeVar
	BOOL  = 2
	NUM   = 3
	FUN   = 4
	DATE  = 5
	def __init__(self, type):
		self.type = type
	@staticmethod
	def is_scalar(type):
		return type in (Type.BOOL, Type.NUM, Type.DATE)
	@staticmethod
	def is_typevar(t):
		return t in (Type.A, Type.B)
	# can we generate a random literal for this type?
	@staticmethod
	def can_literal(t):
		if t in (Type.BOOL,Type.NUM):
			return True
		elif type(t) in (tuple,):
			return all([Type.can_literal(x) for x in t])
		return False

	@staticmethod
	def zero(t):
		if t == Type.NUM:
			return 0
		elif t == Type.BOOL:
			return False
		elif type(t) == tuple:
			return ()
		elif type(t) == list:
			return []
		elif type(t) == Lambda:
			return t
		else:
			return None

	@staticmethod
	def match(spec, t):
		#print('match(spec=',spec,'t=',t,')')
		return (spec == t or Type.is_typevar(spec) or
			# recursively match non-scalar types
			(type(spec) == type(t) and
			 type(spec) in (tuple,list) and
			 len(spec) == len(t) and
			 all([Type.match(x,y) for x,y in zip(spec,t)])))
	@staticmethod
	def repr(t):
		try:
			return ('A','B','Bool','Num','Fun','Date')[t]
		except IndexError:
			return '??'
		except TypeError:
			if type(t) == tuple:
				return '(' + ','.join([Type.repr(x) for x in t]) + ')'
			elif type(t) == list:
				return '[' + (Type.repr(t[0]) if t != [] else '') + ']'
			elif t is None:
				return 'None'
			elif type(t) == str:
				return 'Str'

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
	def typevar_replace(typesig, tvs, depth=0):
		#print('typevar_replace typesig=',typesig,'tvs=',tvs)
		if type(typesig) == list:
			return [Type.typevar_replace(t, tvs, depth+1) for t in typesig]
		elif type(typesig) == tuple:
			x = tuple(Type.typevar_replace(t, tvs) for t in typesig)
			#print('x=',x)
			return x
		elif Type.is_typevar(typesig):
			k = typesig
			if type(k) == list:
				k = tuple(k)
			x = tvs[k]
			while depth > 0 and type(x) == list:
				x = x[0]
				depth -= 1
			return x
		else:
			return typesig

	def encode_hashable_lists(x):
		if type(x) == list:
			return ('list', tuple(Type.encode_hashable_lists(f) for f in x))
		elif type(x) == tuple:
			return tuple(Type.encode_hashable_lists(f) for f in x)
		else:
			return x

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
		elif type(v) == datetime:
			return Type.DATE

	# return a set of non-TypeVar types included in the arbitrary type signature 't'
	@staticmethod
	def listreal(t):
		if Type.is_scalar(t):
			return [t]
		if Type.is_typevar(t):
			return []
		"""
		elif type(t) in (tuple,list) and t != () and t != [] and t[0] != Type.FUN:
			def iter_flatten(iterable):
				it = iter(iterable)
				for e in it:
					if isinstance(e, (list, tuple)):
						for f in iter_flatten(e):
							yield f
					else:
						yield e
			return set([i for i in iter_flatten(t) if Type.is_scalar(i)])
		return []
		"""
		pt = []
		for p in t:
			if Type.is_scalar(p):
				pt.append(p)
			elif type(p) == tuple:
				for i in range(0, len(p)):
					if not Type.is_typevar(p[i]):
						pt.append(p[i])
			elif type(p) == list:
				pt.append(p)
			elif type(p) == Type.DATE:
				pass # FIXME: TODO
		return pt

	# given a realized outtype, calculate the replacement that will transform the typevar into it
	# given ([4], [A]) i must calculate A=4
	@staticmethod
	def calculateReplacement(t, tv):
		if Type.is_typevar(tv):
			return t
		if type(t) != type(tv):
			print('%s != %s' % (Type.repr(t), Type.repr(tv)))
			assert False
		if type(tv) in (tuple,list):
			return Type.calculateReplacement(t[0], tv[0])

def test_type_calculateReplacement():
	assert unittest(Type.calculateReplacement,
			[(None,				(Type.BOOL,Type.BOOL)),
			 (Type.BOOL,			(Type.BOOL,Type.A)),
			 ((Type.BOOL,),			((Type.BOOL,),Type.A)),
			 ([Type.BOOL],			([Type.BOOL],Type.A)),
			 (Type.BOOL,			([Type.BOOL],[Type.A])),
			 ([Type.BOOL],			([[Type.BOOL]],[Type.A])),
			])

def test_type_listreal():
	assert unittest(Type.listreal,
			[([],				((Type.A,),)),
			 ([Type.BOOL],			((Type.BOOL,),)),
			 ([Type.NUM],			((Type.NUM,),)),
			 ([Type.NUM,Type.BOOL],		((Type.NUM,Type.BOOL),)),
			 ([[Type.NUM]],			(([Type.NUM],),)),
			 ([[[Type.NUM]]],		(([[Type.NUM]],),)),
			 ([Type.BOOL,Type.BOOL],	((Type.BOOL,Type.BOOL),)),
			])

"""
Distribution: Value x Data
Compile statistical information about our input so as to generate more useful Exprs
TODO: hmm, i could even condense into range()...
"""
class Dist:
	def __init__(self, l=[]):
		self.val, self.min, self.max = set(), None, None
		if l != [] and type(l[0]) != list:
			self.val = set(l)
			if len(self.val) != len(l):
				# one or more values appears more than once, use a dict
				self.val = collections.Counter(l)
				k = self.val.keys()
			self.min, self.max = min(self.val), max(self.val)
	def keys(self):
		if isinstance(self.val, dict):
			return self.val.keys()
		elif isinstance(self.val, set):
			return list(self.val)
	def random(self, type=None):
		if self.val:
			return random.choice(list(self.keys()))
		return Value.randomval(type)
	def __repr__(self):
		return 'Dist(min=%s max=%s keys=%s val=%s)' % \
			(self.min, self.max, list(self.keys()), self.val)

# un-named invariant type:value pair.
# only used directly for generating the occasional random scalar value
class Value:
	def __init__(self, type_, val=None):
		self.type = type_
		if val == None:
			val = self.randomval(type_)
		self.val = val
	def __repr__(self):
		return '%g' % (self.val,) if type(self.type) == float else str(self.val)
	def dump(self):
		return 'Value(type=%s val=%s)' % (Type.repr(self.type), self.val) 
	def is_invariant(self):
		return True
	@staticmethod
	def randomval(type, val=None):
		if type == Type.NUM:
			#return random.randint(1,2)
			return round(abs(random.gauss(0,10)))
		elif type == Type.BOOL:
			return random.randint(0,1) == 0
		else:
			return val
	def mutate(self, depth, maxdepth, dist=None):
		if self.type == Type.NUM and type(self.val) in (float,int):
			self.val = round(self.val + random.gauss(0,10), 1) # tweak by random amount
		else:
			self.val = Value.randomval(self.type, self.val)

	"""
	list all possible parameters and create a histogram of their values
	"""
	@staticmethod
	def analyze_params(params, data):
		h = dict()
		if type(data[0]) in (float,int,bool):
			h = Dist(data)
		elif type(data[0]) == datetime:
			h['year'] = Dist([d.year for d in data])
			h['month'] = Dist([d.month for d in data])
			h['day'] = Dist([d.day for d in data])
		elif type(data[0]) == tuple:
			h = tuple(Dist(d[i] for d in data) for i in range(0, len(data[0])))
		elif type(data[0]) == list:
			pass
		else:
			pass
		return h

	"""
	merge Dist()s by Type; less specific and useful, but easier to shoehorn into existing Expr generation
	"""
	@staticmethod
	def type_dist(data):
		h = [Dist()] * 6 # h[Type.XXX]
		if type(data[0]) == tuple:
			for i in range(0, len(data[0])):
				t = Type.describe(data[0][i])
				if Type.is_scalar(t):
					h[t] = Dist([d[i] for d in data])
				# FIXME: need to merge, currently we overwrite
		elif type(data[0]) == list:
			pass
		elif type(data[0]) == datetime:
			h[Type.NUM] = Dist([d.year for d in data]+[d.month for d in data]+[d.day for d in data])
		else:
			h[Type.describe(data[0])] = Dist(data)
		return h

# a name:type pair variable reference
# 'val' is actually variable name
# index is used for tuple fields, so index=[1] produces 'val[1]'
class Variable(Value):
	def __init__(self, type_, name, index=[]):
		self.type = type_
		self.invariant = False
		self.val = name
		self.index = index
	def __repr__(self):
		if type(self.index) == list:
			idx = '' if self.index == [] else '['+(']['.join(str(i) for i in self.index))+']'
		elif type(self.index) == str:
			idx = '.' + self.index
		return '%s%s' % (self.val, idx)
	def dump(self):
		return 'Variable(type=%s val=%s)' % (Type.repr(self.type), str(self)) 
	def mutate(self, depth, maxdepth, dist=None):
		pass
	def is_invariant(self):
		return False

def list_intersect(foo, bar):
	return [x for x in foo if x in bar]

# represents a transformation operation; a function
class Op:
	def __init__(self, name, outtype, intype, repr):
		self.name = name
		self.type = outtype
		self.intype = intype
		self.repr = repr
		self.is_tv = Type.typevars(intype) != []
		self.outset = Type.listreal(outtype)
		self.inset = Type.listreal(intype)
	def __repr__(self):
		return '%s %s%s' % (Type.repr(self.type), self.name, Type.repr(self.intype))
	# given a set of all possible available types from parameters and other function's output types, see if we match
	def inTypesMatch(self, availableTypes):
		# FIXME: i'm cheating to match any list-taking functions, since we know that map/filter can xform anything
		islist = any(type(a) == list for a in availableTypes)
		return (islist and self.name in OpListInputNames) or list_intersect(self.inset, availableTypes) == self.inset
	@staticmethod
	def copy(op):
		if op.is_tv:
			# these ops have TypeVars in their signatures which require them to be modified
			x = copy.copy(op)
			x.type = copy.deepcopy(x.type)
			x.intype = copy.deepcopy(x.intype)
			return x
		return op

def id_str(x):
	s = str(x)
	try:
		f = float(s)
		# reduce 'N.0' to 'N'
		if f == int(f):
			s = str(int(f))
	except:
		pass
	return s

def if_str(x,y,z):
	return '(%s if %s else %s)' % (y,x,z)
def gte_str(x,y):
	return '(%s >= %s)' % (x,y)
def add_str(x,y):
	return '(%s + %s)' % (x,y)
def sub_str(x,y):
	return '(%s - %s)' % (x,y)
def mul_str(x,y):
	return '(%s * %s)' % (x,y)
def div_str(x,y):
	return '(%s / %s)' % (x,y)
def sqrt_str(x):
	return 'sqrt(%s)' % (x,)
def log_str(x):
	return 'log(%s)' % (x,)
def min_str(x,y):
	return 'min(%s, %s)' % (x,y)
def max_str(x,y):
	return 'max(%s, %s)' % (x,y)
def len_str(x):
	return 'len(%s)' % (x,)
def sum_str(x):
	return 'sum(%s)' % (x,)
def map_str(x,y):
	return '[%s for %s in %s]' % (x,','.join(x.op.paramkeys),y)
def filter_str(x,y,z):
	return '[%s for %s in %s if %s]' % (z,','.join(z.op.paramkeys),y,x)
def reduce_str(x,y,z):
	return 'reduce(lambda %s: %s, %s, %s)' % (','.join(x.op.paramkeys),x,y,z)
def any_str(x):
	return 'any(%s)' % (x,)
def all_str(x):
	return 'all(%s)' % (x,)

# id(x) -> x. used to wrap a Value/Variable in an Expr
Id = Op('id', Type.A, (Type.A,), id_str)

# list of all possible operations
Ops = (
	#Op('not', Type.BOOL,	(Type.BOOL,),			lambda x:    '(not %s)' % (x,)),
	#Op('or',  Type.BOOL,	(Type.BOOL, Type.BOOL),		lambda x,y:  '(%s or %s)' % (x,y)),
	#Op('and', Type.BOOL,	(Type.BOOL, Type.BOOL),		lambda x,y:  '(%s and %s)' % (x,y)),
	Op('if',  Type.A,	(Type.BOOL, Type.A, Type.A),	if_str),
	#Op('eq',  Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s == %s)' % (x,y)),
	#Op('gt',  Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s > %s)' % (x,y)),
	Op('gte', Type.BOOL,	(Type.A,   Type.A),		gte_str),
	#Op('add', Type.NUM,	(Type.NUM, Type.NUM),		add_str),
	Op('sub', Type.NUM,	(Type.NUM, Type.NUM),		sub_str),
	Op('mul', Type.NUM,	(Type.NUM, Type.NUM),		mul_str),
	Op('div', Type.NUM,	(Type.NUM, Type.NUM),		div_str),
	# pow is a CPU sink. whereas all other functions produce output lte their parameters,
	# modest parameters can generate huge amounts of work, i.e. 
	#Op('pow', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s ** %s)' % (x,y)),
	Op('sqrt', Type.NUM,	(Type.NUM,),			sqrt_str),
	Op('log', Type.NUM,	(Type.NUM,),			log_str),
	#Op('mod', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s %% %s)' % (x,y)),
	#Op('abs', Type.NUM,	(Type.NUM,),			lambda x:    'abs(%s)' % (x,)),
	Op('min', Type.NUM,	(Type.NUM, Type.NUM),		min_str),
	Op('max', Type.NUM,	(Type.NUM, Type.NUM),		max_str),
	Op('len', Type.NUM,	([Type.A],),			len_str),
	Op('sum', Type.NUM,	([Type.NUM],),			sum_str),
	Op('map', [Type.B],	((Type.FUN,Type.B,(Type.A,)), [Type.A]),	map_str),
	#Op('filter', [Type.B],	((Type.FUN,Type.BOOL,(Type.A,)), [Type.A], (Type.FUN,Type.B,(Type.A,))),	filter_str),

	# reduce is a tricky function because it requires a list of len() >= 2
	# most of the code that is generated with it, as it is, is bogus
	# perhaps i should outlaw list literals?
	#Op('reduce', Type.B,	((Type.FUN,Type.B,(Type.B,Type.A)), [Type.A], Type.B),	reduce_str),

	#Op('map-flatten', [Type.B],	((Type.FUN,Type.B,(Type.A,)), [[Type.A]]),
		#lambda x,y: '[%s for %s in %s for %s in %s]' % (x,','.join(x.op.paramkeys),y,x,','.join(x.op.paramkeys))),
		#[item for sublist in l for item in sublist]

	#Op('any', Type.BOOL,	[Type.BOOL],	any_str),
	#Op('all', Type.BOOL,	[Type.BOOL],	all_str),

	# possibly....
	# this may help us build up ranges/sets; would need logic for list literals though
	#Op('in',  Type.BOOL,	(Type.A, [Type.A]),		lambda x,y:'(%s in %s)' % (x,y)),

	# common statistical functions
	#Op('mean', 	Type.NUM,	([Type.NUM],),		lambda x:    'mean(%s)' % (x,)),
	#Op('median', 	Type.NUM,	([Type.NUM],),		lambda x:    'median(%s)' % (x,)),
	#Op('mode', 	Type.NUM,	([Type.NUM],),		lambda x:    'mode(%s)' % (x,)),
	#Op('variance', Type.NUM,	([Type.NUM],),		lambda x:    'variance(%s)' % (x,)),
	#Op('stddev', 	Type.NUM,	([Type.NUM],),		lambda x:    'stddev(%s)' % (x,)),
)
OpOuttypes = [Type.BOOL,Type.NUM]#,[Type.A],[Type.B]]#,Type.B]

OpListInput = tuple(o for o in Ops if any(type(p) == list for p in o.intype))
OpListInputNames = tuple(o.name for o in OpListInput)

OpOuttypeDict = {} # cache Op outtype lookup
def ops_by_outtype(outtype):
	hasht = Type.encode_hashable_lists(outtype)
	try:
		return OpOuttypeDict[hasht]
	except KeyError:
		v = tuple(o for o in Ops if Type.match(o.type, outtype))
		OpOuttypeDict[hasht] = v
		return v

def mean(l):
	return sum(l) / max(1, len(l))

def median(l):
	v, e = sorted(l), len(l)
	return float(v[int((e-1)/2)] + v[e//2]) / 2

def mode(l):
	d = {}
	for x in l:
		try:
			d[x] += 1
		except KeyError:
			d[x] = 1
	return sorted(d.items(), key=lambda x:x[1])[-1][0]

def variance(l):
	m = mean(l)
	v = sum([(n-m)**2 for n in l]) / max(1, len(l))
	return v

def stddev(l):
	return sqrt(variance(l))

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
Log = tuple([0, log(2)] + [log(n) for n in range(2, 100)])

# Expression is a value that applies a function to parameters to arrive at its value
class Expr(Value):

	# generate a random expression that generates a value of type 'outtype'
	# expression may be arbitrarily complex, but may only reference parameters, pre-defined Ops and random literals
	# @params tuple(Variable)
	# @outtype is a realized Type.X type, not a TypeVar.

	def __init__(self, params, outtype, maxdepth=5, depth=1, dist=None):
		if Debug:
			print('Expr(params=',[p.dump() for p in params],'outtype=',Type.repr(outtype),'depth=',depth,')')
		self.params = params
		self.type = copy.copy(outtype)
		self.exprs = []

		# special case for lambdas
		if type(outtype) == tuple and outtype[0] == Type.FUN:
			# TODO: break this block out
			_,outp,inp = outtype
			# reduce parameters to those being passed specifically, and rename for use within the function
			lparams = tuple(Variable(v,k) for k,v in zip(['x','y','z'], inp))
			#print('Lambda inp=%s outp=%s lparams=%s' % \
				#(Type.repr(inp), Type.repr(outp), [p.dump() for p in lparams]))
			self.op = Lambda(outp, inp, lparams)
			self.exprs = [Expr(lparams, outp, maxdepth, depth+1)]
			return

		"""
		The model we really want is a graph data structure
		Nodes would represent sources of data (functions and parameters)
		Paths would represent the ability to use those functions
		This model would solve several existing problems at once. How to most-easily construct it?
		"""

		opt = ops_by_outtype(outtype)
		#print('  outtype=',Type.repr(outtype),'opt=',opt)

		paramtypes = [x.type for x in Expr.params_by_type(params, Type.A)]
		# at the top level only honor parameter types; this reduces the chance of generating useless invariant Exprs
		availableTypes = paramtypes + (OpOuttypes if depth > 1 and depth < maxdepth else [])
		if Debug:
			print(' availableTypes=',availableTypes)
		# this is the problem: we dig down into complex types to their scalar components. we don't want to go
		# that deep. we should only look one level deep to match 'params_by_type'
		availableTypelist = Type.listreal(availableTypes)
		if Debug:
			print(' availableTypelist=',availableTypelist)

		"""
		FIXME: given a complex list param type i want sum([NUM]) to match; however it has to be indirect:
		foo:[(Num,Num)] -> [Num] map([(Num,Num)]) -> sum([Num])
		this indirect matching is going to require a more complex graph-based approach
		"""
		okops = tuple(o for o in opt if o.inTypesMatch(availableTypelist))
		if Debug:
			print('  outtype=',Type.repr(outtype),'params=',[p.dump() for p in params],'okops=',okops)

		r = random.random()
		if depth + 1 >= maxdepth or okops == () or r < depth / maxdepth and (outtype in paramtypes or Type.can_literal(outtype)):
			# generate a terminal (literal or variable) out of chance or because we have to
			# TODO: break this block out
			pt = Expr.params_by_type(params, outtype)
			#if outtype == Type.DATE:
				#print('outtype=',Type.repr(outtype),'params=',[p.dump() for p in params],'pt=',pt)
			self.op = Id
			if (pt == () or r < depth / maxdepth / 10) and Type.can_literal(outtype):
				if Type.is_scalar(outtype):
					if dist:
						self.exprs = [Value(outtype, dist[outtype].random(outtype))]
					else:
						self.exprs = [Value(outtype)] # random literal
				elif type(outtype) == tuple: # tuple literal
					self.exprs = [tuple(Expr(params, t, maxdepth, depth+1, dist=dist) for t in outtype)]
				elif type(outtype) == list: # list literal
					self.exprs = [[Expr(params, t, maxdepth, depth+1, dist=dist) for t in outtype]]
				else:
					print('not expecting outtype=',Type.repr(outtype))
					assert False
			else: # random parameter
				# FIXME: when we need a Date terminal we end up here argh
				if pt == ():
					pt = (None,)
				self.exprs = [random.choice(pt)]
		else:
			# select a non-terminal, i.e. expr/function call
			# TODO: break this block out
			# only choose operations whose output matches our input and whose input
			# we can possibly supply with our parameters

			self.op = Op.copy(random.choice(okops))

			if self.op.is_tv:
				if Debug:
					print('  before self.op=',self.op,'outtype=',Type.repr(outtype))
				tvtypes = self.enforceTypeVars(outtype, availableTypes)
				if Debug:
					print('  after self.op=',self.op,'outtype=',Type.repr(outtype),'tvtypes=',tvtypes)
				assert self.op.type == outtype
			self.exprs = [Expr(params, it, maxdepth, depth+1, dist=dist) for it in self.op.intype]

	# randomly mutate Expr and/or sub-expressions
	# it is important to potentially preserve existing Exprs because only high-scoring Exprs get mutated, so what we have
	# isn't too bad in the first place. we must be able to move Expr between levels, replacing operations with their parameters
	# and vice versa, replacing random invariants
	def mutate(self, maxdepth, depth=1, dist=None):
		mutation = 0.8
		r = random.random()
		if r < mutation: # mutate self
			if r < mutation * 0.01:
				# swap parameters, a boring mutation
				if len(self.exprs) > 1:
					if self.exprs[0].type == self.exprs[1].type:
						self.exprs[:2] = self.exprs[1], self.exprs[0]
					elif len(self.exprs) > 2 and self.exprs[1].type == self.exprs[2].type:
						self.exprs[1:3] = self.exprs[2], self.exprs[1]
				else:
					self = Expr(self.params, self.type, maxdepth, depth, dist=dist)
			elif r < mutation * 0.25:
				# preserve self as parameter to random new Expr 
				# x+(y+z) -> e+(x+z) | e+(y+x)
				e = Expr(self.params, self.type, maxdepth, depth, dist=dist)
				x = tuple(i for i,e in enumerate(e.exprs) if isinstance(e, Value) and e.type == self.type)
				if x != ():
					e.exprs[random.choice(x)] = Expr.adjdepth(self, depth+1, maxdepth) # trim too-deep self.exprs
				return e
			elif r < mutation * 0.5:
				# replace self with parameter
				# x+(y+z) -> y | z
				y = random.choice(self.exprs)
				if type(y) == Expr and y.type == self.type:
					self = y
				else:
					self = Expr(self.params, self.type, maxdepth, depth, dist=dist)
			else:
				# replace self with completely random new Expr
				self = Expr(self.params, self.type, maxdepth, depth, dist=dist)
		else: # maybe mutate child
			mutatable = tuple(e for e in self.exprs if hasattr(e,'mutate'))
			if mutatable != ():
				random.choice(mutatable).mutate(maxdepth, depth+1, dist=dist)
			else:
				self = Expr(self.params, self.type, maxdepth, depth, dist=dist)
		return self

	# our depth has changed; trim any sub-Exprs that violate maxdepth
	@staticmethod
	def adjdepth(e, depth, maxdepth):
		if depth >= maxdepth:
			e.op, e.exprs = Id, [Value(e.type, Type.zero(e.type))]
		return e

	# recursively co-dependent on instance method is_invariant()
	@staticmethod
	def is_invariant(x):
		if type(x) in (Expr,tuple,list):
			return all(Expr.is_invariant(y) for y in x)
		elif type(x) == Value:
			return True
		elif type(x) == Variable:
			return False
		else:
			print('not expecting type %s: %s' % (type(x), x))
			assert False

	# Is this Expr invariant? That is, does it contain references to variables? Co-dependent with Expr.is_invariant
	# FIXME: is_invariant() is a complete clusterfuck. I do not understand why I have to implement it like this
	# but can't get it to work any other way. Why don't Value and Variable retain their own methods?!
	def is_invariant(self):
		if self is None:
			# FIXME: why the fuck does Expr.is_invariant(None) get here?!
			return True 
		if type(self) in (Expr,):
			return all(Expr.is_invariant(x) for x in self.exprs)
		elif type(self) == Value:
			return True
		elif type(self) == Variable:
			return False

	def invariant_val(self):
		try:
			return self.exprs[0].invariant_val()
		except:
			if type(self.exprs[0]) == Value:
				return self.exprs[0].val
			else:
				return self.exprs[0]

	def dump(self):
		return 'Expr(op=%s outtype=%s invariant=%s exprs=[%s])' % \
			(self.op.name, Type.repr(self.type), self.is_invariant(), \
			','.join([e.dump() if hasattr(e,'dump') else '(type='+str(type(e))+' '+str(e)+')' for e in self.exprs]))

	@staticmethod
	def canonicalize(x):
		if type(x) == Expr:
			return x.canonical()
		elif type(x) == tuple:
			return tuple(Expr.canonicalize(y) for y in x)
		elif type(x) == list:
			return [Expr.canonicalize(y) for y in x]
		else:
			return x

	@staticmethod
	def visit(e):
		try:
			for x in e:
				Expr.visit(x)
		except:
			pass
		yield e

	# reduce expressions to their simplified, canonical form
	# relatively expensive, only use to clean up decent candidates
	# NOTE: this may seem like trivial aesthetics but reducing complexity
	# appears to speed solution
	def canonical(self):
		# recurse downwards, 
		self.exprs = [Expr.canonicalize(e) for e in self.exprs]
		if self.op.name == 'map':
			# TODO: [10 for x in foo]
			try:
				x = eval(str(self))
				# reduce invariant mapping, i.e. [2 for x in [0]] -> [2]
				self.op, self.exprs = Id, [Value(self.type, x)]
			except:
				# [x for x in y] -> y
				if str(self.exprs[0]) == ','.join(self.exprs[0].op.paramkeys):
					self = self.exprs[1]
		elif self.op.name == 'filter':
			# TODO: [x for x in y if True >= False] -> y
			#print('filter exprs[0]=%s' % (self.exprs[0],))
			v = str(self.exprs[0])
			if v == 'True':
				# filter(True, x) -> x
				self = self.exprs[1]
			elif v == 'False':
				# filter(False, x) -> []
				self.op, self.exprs = Id, [Value(self.exprs[1].type, [])]
			else:
				# [x for x in [] if ...] -> []
				e1 = self.exprs[1]
				if type(e1) == Expr and e1.op is Id:
					if type(e1.exprs[0]) == Expr and e1.exprs[0] == []:
						self = e1
					elif type(e1.exprs[0]) == Value and e1.exprs[0].val == []:
						self = e1
		elif self.op.name in ('add','sub','mul','div','mod'):
			try:
				# try to reduce numerical expressions
				x = eval(str(self))
				if x == round(x):
					# only keep integers; prefer expressions to mysterious floating point literals
					self.op, self.exprs = Id, [Value(self.type, x)]
			except:
				e0, e1 = str(self.exprs[0]), str(self.exprs[1])
				p = None # which parameter to reduce to? take action iff in (0,1)
				if self.op.name == 'add':
					if e0 == '0':
						p = 0
					elif e1 == '0':
						p = 1
				elif self.op.name == 'sub':
					if e1 == '0':
						p = 0
					elif e0 == e1:
						self.op, self.exprs = Id, [Value(self.type, 0)]
				elif self.op.name == 'mul':
					# TODO: x * (1 / y) -> x / y
					if e0 == '1':
						p = 0
					elif e1 == '1':
						p = 1
					elif '0' in (e0,e1):
						self.op, self.exprs = Id, [Value(self.type, 0)]
				elif self.op.name == 'div':
					if e1 == '1': # x/1 -> x
						p = 0
					elif e0 == '0': # 0/x -> 0
						p = 0
					elif e0 == e1: # x/x -> 1
						self.op, self.exprs = Id, [Value(self.type, 1)]
				elif self.op.name == 'mod':
					if e0 == e1 or e1 == '1':
						self.op, self.exprs = Id, [Value(self.type, 0)]
				if p is not None:
					self.op, self.exprs = Id, [Value(self.type, self.exprs[p])]
				elif self.op.name in ('add','mul'):
					# move single invariants in commutative binary operations to the right
					# 2 + x -> x + 2
					# 5 * x -> x * 5
					if self.exprs[0].is_invariant() and not self.exprs[1].is_invariant():
						self.exprs[0], self.exprs[1] = self.exprs[1], self.exprs[0]
					elif e1 < e0:
						# sort parameters alphabetically
						self.exprs[0], self.exprs[1] = self.exprs[1], self.exprs[0]
		elif self.op.name in ('eq','gte'):
			# x == x -> True
			# x <= x -> True
			# x >= x -> True
			if str(self.exprs[0]) == str(self.exprs[1]):
				self.op, self.exprs = Id, [Value(Type.BOOL, True)]
			# TODO: ((50 + len(foo)) >= 53)
		elif self.op.name in ('gt','lt'):
			# x < x -> False
			# x > x -> False
			if str(self.exprs[0]) == str(self.exprs[1]):
				self.op, self.exprs = Id, [Value(Type.BOOL, False)]
		elif self.op.name == 'if':
			# if(True,x,y) -> x
			# if(False,x,y) -> y
			v = str(self.exprs[0])
			if v == 'True':
				self = self.exprs[1]
			elif v == 'False':
				self = self.exprs[2]
			else:
				# if(x,True,False) -> x
				if str(self.exprs[1]) == 'True' and str(self.exprs[2]) == 'False':
					self = self.exprs[0]
		elif self.op.name in ('or','and'):
			# x or x -> x
			# x and x -> x
			e0, e1 = str(self.exprs[0]), str(self.exprs[1])
			if e0 == e1:
				self = self.exprs[0]
			elif self.op.name == 'or':
				if 'True' in (e0,e1):
					self = self.exprs[0]
				elif e0 == 'False':
					self = self.exprs[1]
				elif e1 == 'False':
					self = self.exprs[0]
			elif self.op.name == 'and':
				if e0 == 'False':
					self = self.exprs[0]
				elif e1 == 'False':
					self = self.exprs[1]
				elif e0 == 'True':
					self = self.exprs[1]
				elif e1 == 'True':
					self = self.exprs[0]
		elif self.op.name in ('sqrt','log'):
			try:
				n = eval(str(self))
				if n == round(n):
					self.op, self.exprs = Id, [Value(Type.NUM, n)]
			except:
				pass
		elif self.op.name == 'abs' and self.is_invariant():
			# abs(positive_invariant) -> positive_invariant
			try:
				n = float(eval(str(self.exprs[0])))
				# if we don't blow up...
				if n >= 0.0:
					self = self.exprs[0]
			except:
				pass
		elif self.op.name == 'len':
			# realize len([...])
			e0 = self.exprs[0]
			if type(e0) == Expr and e0.op is Id:
				if type(e0.exprs[0]) == Expr:
					self = e0.exprs[0][0]
					self.op, self.exprs = Id, [Value(Type.NUM, len(e0.exprs[0]))]
				elif type(e0.exprs[0]) == Value:
					self.op, self.exprs = Id, [Value(Type.NUM, len(e0.exprs[0].val))]
		elif self.op.name in ('min','max'):
			# min(x,x) | max(x,x) -> x
			try:
				n = eval(str(self))
				self.op, self.exprs = Id, [Value(Type.NUM, n)]
			except:
				if str(self.exprs[0]) == str(self.exprs[1]):
					self = self.exprs[0]
		elif self.op.name == 'sum':
			# sum([x]) == x
			e0 = self.exprs[0]
			if type(e0) == Expr and e0.op is Id:
				if type(e0.exprs[0]) == Expr:
					self = e0.exprs[0][0]
				elif type(e0.exprs[0]) == Value:
					self.op, self.exprs = Id, [Value(Type.NUM, sum(e0.exprs[0].val))]
			# TODO:...
			# sum(x[y] for x in foo) + sum(x[z] for x in foo) -> sum(x[y]+x[z] for y in foo)
		elif self.op.name == 'reduce':
			# reduce(x, [], y) -> y
			if type(self.exprs[1]) == list and len(self.exprs[1]) == 0:
				self = self.expr[2]
			elif type(self.exprs[1]) == Expr and self.exprs[1].op is Id and self.exprs[1].exprs[0] == []:
				self = self.expr[2]
		return self

	def __repr__(self):
		return self.op.repr(*self.exprs)
	def __lt__(self, other):
		return 0
	def __gt__(self, other):
		return 1
	def __hash__(self):
		return str(self).__hash__()

	# given a Op, fill in any TypeVariables with actual types
	# TODO: it is possible, when operating on a Date type data, to produce a randomize
	# lambda that does not take Date data parameters but is thus possibly still used in expressions
	def enforceTypeVars(self, outtype, ptypes):
		tvs = Type.typevars((self.op.intype, self.op.type))
		tvtypes = dict([(tv,None) for tv in tvs])

		# FIXME: this shit is all hard-coded to very specific higher-order function signatures...
		if type(self.op.intype[0]) == tuple and self.op.intype[0][0] == Type.FUN:
			# if we're a lambda then set output type
			if Type.is_typevar(self.op.type) or (type(self.op.type) == list and Type.is_typevar(self.op.type[0])):
				k = self.op.type[0] if type(self.op.type) == list else self.op.type
				tvtypes[k] = outtype[0] if type(outtype) == list else outtype
				k = self.op.intype[1][0]
				#while type(k) == list:
				#	k = k[0]
				x = random.choice(ptypes)
				if type(x) == list:
					x = x[0]
				tvtypes[k] = x
				# FIXME: ok, so reduce() is broken because sometimes we choose it to return a list, but it never really does.
				# either we need to fix it so it doesn't get chosen, or fix it so it can return a list...
				if Debug:
					print('    lambda tvtypes=',tvtypes)
		else:
			# select random type for each, based on paramtypes
			for tv in tvtypes.keys():
				tvtypes[tv] = outtype if tv == self.op.type else random.choice(ptypes)

		if Debug:
			print('    calculatedReplacement outtype=',outtype,'self.op.type=',self.op.type)
		# enforce consistent outtype
		# FIXME: does this negate the above special-case code for FUNs?
		x = Type.calculateReplacement(outtype, self.op.type)
		if x != None:
			y = Type.typevars(self.op.type)[0]
			tvtypes[y] = x

		intypes = Type.typevar_replace(self.op.intype, tvtypes)
		if type(self.op.intype) == tuple:
			intypes = tuple(intypes)
		self.op.intype = intypes
		self.op.type = Type.typevar_replace(self.op.type, tvtypes)
		if Debug:
			print('    op.name=%s self.op.type=%s self.op.intype=%s ptypes=%s tvtypes=%s' % (self.op.name, Type.repr(self.op.type), Type.repr(self.op.intype), ptypes, tvtypes))
		#if type(self.op.intype[0]) == tuple and self.op.intype[0][0] == Type.FUN:
			#print('op.name=%s type=%s op.type=%s op.intype=%s ptypes=%s' % \
				# % (self.op.name, Type.repr(outtype), Type.repr(self.op.type),Type.repr(self.op.intype), ptypes))
			#assert type(self.op.type) != list
		return tvtypes

	# list all possible type:val source from parameters
	@staticmethod
	def params_by_type(params, t):
		#print('params_by_type params=',params)
		pt = []
		for p in params:
			if type(p.type) == tuple:
				# one level deep in tuples
				pt += [Variable(x, p.val, [i]) for i,x in enumerate(p.type) if Type.match(t, x)]
			elif Type.match(t, p.type):
				pt.append(p)
			elif p.type == Type.DATE:
				if Type.match(t, Type.NUM):
					pt += [Variable(Type.NUM, p.val, 'year'),
					       Variable(Type.NUM, p.val, 'month'),
					       Variable(Type.NUM, p.val, 'day')]
					       #Variable(Type.NUM, p.val, 'isoweekday()')]
		return tuple(pt)

	# count the number of total nodes
	@staticmethod
	def size(e):
		try:
			return int(e.op is not Id) + sum([Expr.size(e) for e in e.exprs])
		except:
			try:
				return sum([Expr.size(e) for e in e])
			except:
				return 1

	# count the number of random invariants present
	@staticmethod
	def invariant_count(e):
		try:
			return sum([Expr.invariant_count(e) for e in e.exprs])
		except:
			try:
				return sum([Expr.invariant_count(e) for e in e])
			except:
				try:
					return e.is_invariant()
				except:
					return 1

def test_type_describe():
	assert unittest(Type.describe,
			[(Type.BOOL,			(True,)),
			 (Type.BOOL,			(False,)),
			 (Type.NUM,			(0,)),
			 (Type.NUM,			(1.,)),
			 ((Type.NUM,Type.NUM),		((0,1.),)),
			 ([(Type.NUM,)],		([(0,)],)),
			])

def test_type_can_literal():
	assert not Type.can_literal(Type.DATE)
	assert Type.can_literal((Type.NUM,Type.BOOL))

def test_expr_invariant():
	assert Expr.is_invariant(None)
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

def test_expr2str():
	e = tuple(Expr((Variable(Type.NUM,'a'),),(Type.NUM,), maxdepth=1) for _ in range(0, 50))

def test_canonicalize():
	e = tuple(Expr.canonicalize(Expr((Variable([Type.NUM],'a'),),(Type.NUM,), maxdepth=1)) for _ in range(0, 1000))
	esf = [e for e in e if 'if True' in str(e) or 'if False' in str(e)]# or ('x for x in' in str(e) and not 'x for x in a' in str(e))]
	if esf != []:
		print('non-canonicalized=',esf[0],esf[0].dump())
		assert esf == []

def test_map_flatten():
	e = tuple(Expr.canonicalize(Expr((Variable([[Type.NUM]],'a'),),[Type.NUM], maxdepth=4)) for _ in range(0, 10))
	#print('map-flatten=',e)

def test():
	test_type_describe()
	test_type_listreal()
	test_type_can_literal()
	test_type_calculateReplacement()
	test_expr_invariant()
	tv = Type.typevars(((Type.FUN, Type.B, (Type.A,)), [Type.A]))
	assert tv == list(set([1,0]))
	test_enforceTypeVars()
	test_expr2str()
	test_canonicalize()
	test_map_flatten()
	print('Tests passed.')

import multiprocessing as mp
import hashlib
import sqlite3

WorstScore = float('inf')

# default fitness function
# d=(in, out)
# res=candidate result
def fit(d,res):
	return abs(d[1]-res)

Data = []

# run Expr e(data), score the result
def run_score(params):
	estr, fitness, worstscore, p = params
	#print(estr)
	fn = eval('lambda x:' + estr)
	try:
		score = 0
		for d in globals()['Data']:
			res = fn(d[0])
			fs = fitness(d, res)
			score += fs
			if score >= worstscore:
				break # short-circuit upon poor score, speeds up large data
	except (ZeroDivisionError, ValueError):
		# ZeroDiv: /0 or %0
		# ValueError: log(0)
		score = WorstScore
	except (TypeError,AttributeError) as e:
		#print('%s: %s' % (e, estr))
		# FIXME: these indicate errors in code generation
		# FIXME: reduce() produces TypeErrors
		# FIXME: Date type produces AttributeErrors
		score = WorstScore
	except:
		print(estr)
		sys.stdout.flush()
		sys.exit(1)
		# assign worst possible score, keep going
		score = WorstScore
	return (estr, p, score)

# Expr p × population rankings
class KeepScore:
	def __init__(self, expr, score, gencnt):
		self.expr = expr
		self.score = score
		self.gencnt = gencnt
		self.size = Expr.size(expr)
		self.invarcnt = Expr.invariant_count(expr)
		self.str = str(expr)
	def __repr__(self):
		return 'score=%g size=%u invarcnt=%u %s' % \
			(self.score, self.size, self.invarcnt, self.expr)
	# custom comparison for sorting
	def __lt__(self, other):
		if self.score != other.score: # favor better score...
			return self.score < other.score	
		if self.size != other.size: # then smaller size...
			return self.size < other.size
		if self.invarcnt != other.invarcnt: # then fewer invariants...
			# TODO: perhaps favor simpler/lower invariants over larger ones?
			return self.invarcnt < other.invarcnt
		if len(self.str) != len(other.str):
			return len(self.str) < len(other.str)
		if self.gencnt != other.gencnt: # then older over newer...
			return self.gencnt < other.gencnt
		return False
	# how much better is my score than someone else's?
	# used to implement a larger epsilon for comparing Expr scores
	# to hinder the accumulation of meaningless invariant terms
	def pct_improvement(self, other):
		if self.score == 0:
			return float('inf')
		return ((float(other.score) / self.score) - 1.) * 100.

# KeepScore × Multi-generational logic
class FamilyMember:
	def __init__(self, ks, parent):
		self.ks = ks 
		self.parent = parent
		if parent:
			parent.children[str(ks.expr)] = self
		self.children = {}
	def __lt__(self, other):
		return self.ks < other.ks
	def __repr__(self):
		return str(self.ks)
	def __eq__(self, other):
		return str(self.ks.expr) == str(other.ks.expr)

# Stdout × evolve()
# show progress, but fold useless output
class Reporter:
	def __init__(self):
		self.msg = ''
		self.scores = [WorstScore]
		self.lastgencnt = 0
		self.reversecnt = 0
	def show(self, pop, gencnt, gentotal):
		self.reversecnt = min(len(self.scores)-1, self.reversecnt + int(gencnt < self.lastgencnt))
		self.lastgencnt = gencnt
		if pop != [] and pop[0].ks.score != self.scores[-1]:
			self.scores.append(pop[0].ks.score)
			if gentotal != 0:
				sys.stdout.write('\n')
		else: # otherwise, remove previous line
			sys.stdout.write('\b' * len(self.msg))
			#sys.stdout.write('\n')
		if gentotal == 0:
			print('date                 gen brch progress expr')
		t = time.localtime()
		self.msg = '%04d-%02d-%02d-%02d:%02d:%02d %4u %2u %s %s %s' % \
			(t.tm_year, t.tm_mon, t.tm_mday, t.tm_hour, t.tm_min, t.tm_sec,
			gentotal, gencnt, '.' * (0 if pop == [] else Reporter.parentcnt(pop[0])),
			'' if pop == [] else '#' * int(Reporter.scale(pop[0].ks.score)),
			'' if pop == [] else pop[0].ks)
		sys.stdout.write(self.msg)
		sys.stdout.flush()
	@staticmethod
	def parentcnt(ft):
		cnt = 0
		while ft.parent:
			ft = ft.parent
			cnt += 1
		return cnt
	# scale score 'n' to display value progress bar in most useful way
	@staticmethod
	def scale(n, maximum=80):
		if n < 10:
			return n
		elif n <= 10000:
			return min(maximum, 10 + math.sqrt(n-10))
		else:
			return min(maximum, 10 + math.sqrt(9990) + math.log(n-10000))

# run each candidate against the data, score the results, keep the least-awful scoring functions
def evaluate(pool, population, pop, fitness, gencnt):
	# only even consider keeping someone if it scores better than the worst we've already kept
	worstscore = pop[-1].ks.score if pop != [] else WorstScore
	keep = []
	uniq = dict((str(e), e) for e in population if not e.is_invariant())
	# TODO: figure out how to avoid copying data; it will always be the same
	if UsePool:
		scored = pool.map(run_score, ((estr, fitness, worstscore, p) for estr,p in uniq.items()))
	else:
		scored = [run_score((estr, fitness, worstscore, p)) for estr,p in uniq.items()]
	for estr,p,score in scored:
		if score < worstscore:
			p = Expr.canonical(p)
			try:
				if not p.is_invariant():
					keep.append(KeepScore(p, score, gencnt))
			except AttributeError:
				pass
	return sorted(keep)

# given an existing Expr e, generate a random mutation
def mutate_expr(params):
	e, maxdepth, dist = params
	return e.mutate(maxdepth, dist=dist)

def mutate_pop(pool, parent, popsize, maxdepth, dist):
	if UsePool:
		population = pool.map(mutate_expr, [(parent, maxdepth, dist) for _ in range(0, popsize)])
	else:
		p = pickle.dumps(parent)
		population = [mutate_expr((pickle.loads(p), maxdepth, dist)) for _ in range(0, popsize)]
	return population

def random_expr(params):
	sym, outtype, maxdepth, dist = params
	return Expr(sym, outtype, maxdepth, dist=dist)

def random_pop(pool, popsize, sym, outtype, maxdepth, dist):
	if UsePool:
		population = pool.map(random_expr, [(sym, outtype, maxdepth, dist) for _ in range(0, popsize)])
	else:
		population = [random_expr((sym, outtype, maxdepth, dist)) for _ in range(0, popsize)]
	return population

def fit_tuple1(d, res):
	return abs(d[1][0]-res[0])

def fit_list1(d, res):
	return sum([abs(x-y) for x,y in zip(d[1], res)]) + abs(sum(d[1])-sum(res))

import pickle

class Evolve:
	"""
	"""
	def __init__(self, name=None):
		self.name = name
		self.data = None
		self.fitness = fit # default

	"""
	data = [(from, to),...] list of transformations
	"""
	def setData(self, data, types=None):
		assert type(data) == list
		assert type(data[0]) == tuple
		assert len(data[0]) == 2
		if types == None:
			self.intype,self.outtype = Type.describe(data[0])
		else:
			self.intype,self.outtype = types
		self.sym = (Variable(self.intype, 'x'),)
		self.data = data
		print(Value.type_dist([d[0] for d in self.data]))

	def setFitness(self, fitness):
		self.fitness = fitness

	"""
	given a set of typed data transforms and a bunch of parameters, try to evolve a solution with score=0
	"""
	def solve(self, db='evolve.db', resume=True, popsize=10000, maxdepth=5, popkeep=1, deadend=20, maxsize=50):
		# sanity check types and ranges
		assert 1 <= maxdepth < len(Log)
		assert popsize >= 1
		assert popkeep >= 1
		print('evolve :: %s -> %s' % (Type.repr(self.intype),Type.repr(self.outtype)))
		self.db = db
		self.popsize = popsize
		self.maxdepth = maxdepth
		self.popkeep = popkeep
		self.deadend = deadend
		self.maxsize = maxsize
		if resume:
			self._loadTree()
		self._evolve()

	
	def _scale_maxdepth(self, gentotal=0):
		maxd = min(self.maxdepth, int(2 + log(gentotal+1)))
		return maxd

	def _evolve(self):
		# initialize defaults
		gentotal = 0
		gencnt = 0
		pop = []
		r = Reporter()
		globals()['Data'] = self.data # set to global
		assert len(Data) == len(self.data)
		pool = None
		if UsePool:
			pool = mp.Pool(mp.cpu_count())
		dist = Value.type_dist([d[0] for d in self.data])

		while pop == []:
			population = random_pop(pool, self.popsize, self.sym, self.outtype, self._scale_maxdepth(gentotal), dist)
			keep = evaluate(pool, population, pop, self.fitness, gencnt)[:self.popkeep]
			pop = [FamilyMember(ks, None) for ks in keep]
			r.show(pop, gencnt, gentotal)
			gencnt += 1
			gentotal += 1

		# go until we find score=0, then spend at least a few generations trying to simplify
		# TODO: i think i should iterate from [1..maxdepth] to isolate the most important factor for each depth.
		while pop[0].ks.score > 0 or (pop[0].ks.invarcnt > 0 and gencnt <= pop[0].ks.gencnt + pop[0].ks.size + pop[0].ks.invarcnt):
			parent = random.choice(pop)
			population = mutate_pop(pool, parent.ks.expr, self.popsize, self._scale_maxdepth(gentotal), dist)
			keep = evaluate(pool, population, pop, self.fitness, gencnt)[:self.popkeep]
			pop, gencnt = self._postGen(pop, keep, parent, gencnt)
			r.show(pop, gencnt, gentotal)
			gencnt += 1
			gentotal += 1
		print('\ndone', pop[0])
		if UsePool:
			pool.close()
		self._saveExpr(pop[0])
		return pop[0]

	"""
	after a new generation has been run, decide what to do with it. do we keep the new one? do we roll back to the parent?
	"""
	def _postGen(self, pop, keep, parent, gencnt):
		if (keep != [] and (keep[0] < pop[0].ks and keep[0].pct_improvement(pop[0].ks) >= 1.0 and keep[0].size < self.maxsize)) and str(keep[0]) not in parent.children:
			# never-before-seen reasonable improvement...
			# NOTE: this allows duplicates, but never from the same parent
			pop = [FamilyMember(ks, parent) for ks in keep]
			self._saveExpr(pop[0])
		elif pop[0].ks.score > 0 and parent.parent:
			# calculate how much better we are than our parent; better results take longer to deadend
			if keep == []:
				improve = 1
			else:
				improve = (parent.ks.score / keep[0].score) * (parent.ks.size / keep[0].size)
			if gencnt - parent.ks.gencnt >= max(1, log(improve)) * self.deadend:
				# stuck in a deadend...
				# roll parent back to grandparent
				#print('\nrolling back to %s %s%s' % (id(parent.parent), parent.parent.ks.expr, ('.' * 100)))
				pop = [parent.parent]
				gencnt = parent.parent.ks.gencnt # reset gencnt, otherwise our rollback cascades all the way back
		return (pop, gencnt)

	"""
	given an existing solution with score=0, attempt to reduce size and/or invariant count
	"""
	def simplify(self):
		pass

	"""
	based on name and data checksum, locate and load our previous working tree from the database
	"""
	def _loadTree(self):
		pass

	"""
	when we evolve a better Expr, save it to the database
	"""
	def _saveExpr(self, ft):
		#print('saveExpr(%s)' % (pickle.dumps(ft.ks.expr)))
		pass

	"""
	cleanup
	"""
	def __del__(self):
		pass

# set our processes' priority as low as possible so we don't hog the CPU
def lower_priority():
	if os.name == 'posix':
		os.system('renice +20 %d' % (os.getpid(),))

if __name__ == '__main__':
	test()
	lower_priority()

	"""
	e = Evolve()
	e.setData([
			# expect: foo
			(10, 10),
			(1e6, 1e6),
		])
	e.solve(popsize=400)
	"""

	e = Evolve()
	e.setData([	# ensure we handle (Num,[(Num,Num,Num)])
			# expect: foo[0]*sum([x[0]+x[1]+x[2] for x in foo[1]])
			((5,[(0,0,0),(0,0,0)]), 0),
			((2,[(1,1,1),(0,0,0)]), 6),
			((1,[(1,2,3),(1,2,3)]), 12),
			((2,[(3,1,2),(3,2,1)]), 24),
			((3,[(0,5,0),(3,4,3)]), 45),
			((5,[(0,0,0),(3,4,3)]), 50),
		])
	e.solve(maxdepth=7)

	e = Evolve()
	e.setData([	# ensure we handle ([(Num,Num,Num)])
			# expect: sum([x[0]+x[1]+x[2] for x in foo[0]])
			(([(0,0,0),(0,0,0)],), 0),
			(([(1,1,1),(0,0,0)],), 3),
			(([(1,2,3),(1,2,3)],), 12),
			(([(3,1,2),(3,2,1)],), 12),
			(([(0,5,0),(3,4,3)],), 15),
			(([(0,0,0),(3,4,3)],), 10),
		])
	e.solve(maxdepth=7)

	e = Evolve()
	e.setData([	# ensure we can produce tuple results
			# expect: (foo,)
			(100, (100,)),
			(1000, (1000,)),
		])
	e.setFitness(fit_tuple1)
	e.solve(popsize=1000, maxdepth=3)

	e = Evolve()
	e.setData([
			# use datetime
			# expect: foo.year >= 2000
			(datetime(1900,1,1), False),
			(datetime(1995,1,1), False),
			(datetime(1996,1,1), False),
			(datetime(1997,1,1), False),
			(datetime(1998,1,1), False),
			(datetime(1999,1,1), False),
			(datetime(2001,1,1), True),
			(datetime(2002,1,1), True),
			(datetime(2003,1,1), True),
			(datetime(2004,1,1), True),
			(datetime(2005,1,1), True),
			(datetime(2006,1,1), True),
		])
	#e.setFitness(func)
	e.solve(deadend=50) #even if we're in the database, start a new tree
	#e.continue(db='evolve.db', popsize=10000, maxdepth=5) # try to load from database or start fresh
	#e.simplify(Limit('10 hours')) # evolve, but only to simpler forms, for 10 wallclock hours

	e = Evolve()
	e.setData( [
			# use len()
			# expect: len(foo) >= 3
			([1], False),
			([1,0], False),
			([0,0], False),
			([], False),
			([1,0,0,0], True),
			([0,0,0], True),
			([1,1,1], True),
		])
	e.solve(popsize=2000)

	e = Evolve()
	e.setData([
			# use reduce()
			# expect: reduce(lambda x,y: x*y, foo, 1)
			([1,1,1], 1),
			([2,2,2], 8),
			([1,2,3], 6),
			([3,3,3], 27),
			([10,10,10], 1000),
		])
	e.solve(popsize=1000)

	e = Evolve()
	e.setData([
			# basic filter
			# expect: [x for x in foo if (x >= 4)]
			([1,2,3,4,5], [4,5]),
			([0,10,1e6,2,3], [10,1e6]),
			([0,0,0,0,0,0,1,2,3], []),
		])
	e.setFitness(fit_list1)
	e.solve(popsize=1000)

	e = Evolve()
	e.setData([
			# expect: sum([x[0] for x in foo])
			# got: sum([sum([x[0]]) for x in foo])
			([(10,1)], 10),
			([(2000,1)], 2000),
			([(-2000,1)], -2000),
		])
	e.solve(popsize=1000)

	e = Evolve()
	e.setData([
			# expect: ((foo+foo)+1) or ((foo*2)+1)
			# got:    ((1 + foo) + foo)
			#         (foo + (1 + foo))
			(10, 21),
			(1e6, 1e6*2+1),
		])
	e.solve(popsize=1000)

	e = Evolve()
	e.setData([
			# expect: sum([x[0]*x[1]+x[2] for x in foo])
			# GOT: (sum([x[2] for x in foo]) + sum([(x[1] * x[0]) for x in foo]))
			#      (sum([(x[1] * x[0]) for x in foo]) + sum([x[2] for x in foo]))
			([(10,3,5)], 10*3+5),
			([(3,3,1)], 3*3+1),
			([(2,1,0)], 2*1+0),
			([(1000,50,55)], 1000*50+55),
			([(50,1000,55)], 1000*50+55),
			([(0,0,1000)], 1000),
		])
	e.solve(maxdepth=6)

	e = Evolve()
	e.setData([
			# expect: sum([(x[0]+x[1]+x[2]+x[3])/len(x) for x in foo])
			# or maybe: sum([x[0]/2 for x in foo])
			# GOT: (sum([x[0] for x in foo]) / 2)
			#      (0.5 * sum([x[0] for x in foo]))
			([(5,0,2,3)], 2.5),
			([(50,0,50,0)], 25),
			([(100,100,0,0)], 50),
			([(2,0,0,2)], 1),
		])
	e.solve(maxdepth=6, popsize=5000)

	e = Evolve()
	e.setData([
			# use or
			# expect: foo[0] or foo[1]
			([(True,True)], True),
			([(True,False)], True),
			([(False,True)], True),
			([(False,False)], False),
		])
	e.solve(maxdepth=6, popsize=5000)

	"""
	evolve( [
			# expect: sum([(x[0]+x[1]+x[2]+x[3])/4 for x in foo])
			# GOT: ((sum([x[3] for x in foo]) / 2) + (sum([x[1] for x in foo]) / 5))
			#      (sum(reduce(lambda x,y: x, foo)) / 4)
			#      (reduce(lambda x,y: x, reduce(lambda x,y: x, foo)) / 2)
			([(0,5,2,3)], 2.5),
			([(0,0,50,50)], 25),
			([(2,0,0,2)], 1),
		])
	"""

	e = Evolve()
	e.setData([
			# combine reduce() and min()
			# expect: reduce(lambda x,y:min(x,y), foo, 1)
			# got: reduce(lambda x,y: min(x,y), foo, 5)
			([1,2,3], 1),
			([3,2,1], 1),
			([2,3,1], 1),
			([2,1,3], 1),
			([100,10,5], 5),
		])
	e.solve(popsize=1000)

	################ Beyond this point stuff doesn't work

	# FIXME: broken?
	e = Evolve()
	e.setFitness(fit_list1)
	e.setData([ # extract tuple members and re-wrap them
			# expect: (foo[0]+1, foo[0]+foo[0]+2)
			# got: ((foo[0] + 1), (2 + (foo[0] + foo[0])))
			((100,), (101,202)),
			((1000,), (1001,2002)),
		])
	e.solve()#, fitness=lambda d,res:sum(abs(x-y) for x,y in zip(d[1],res)))

	"""
	evolve( [
			# FIXME: need this exact code to flatten list, but my code can't generate it!
			# expect: [y for y in x for x in foo]
			# GOT: 
			([[1,2,3]], [1,2,3]),
		], popsize=1000, fitness=lambda d,res: sum([abs(x-y) for x,y in zip(d[1], res)]) + (1e6 * abs(len(d[1]) - len(res))))
	"""

