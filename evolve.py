#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
simple genetic algorithm framework

given data, evolve transformation
lists types assumed homogenous
tuple types assumed homogenous
"""

import sys
import copy
import time
import random
import math
from math import sqrt,log
from test import unittest # custom

class Type:
	A     = 0 # TypeVar
	B     = 1 # TypeVar
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
			(type(spec) == type(t) and
			 type(spec) in (tuple,list) and
			 len(spec) == len(t) and
			 all([Type.match(x,y) for x,y in zip(spec,t)])))
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
		if type(typesig) == list:
			return [Type.typevar_replace(t, tvs) for t in typesig]
		elif type(typesig) == tuple:
			x = tuple(Type.typevar_replace(t, tvs) for t in typesig)
			#print('x=',x)
			return x
		elif Type.is_typevar(typesig):
			k = typesig
			if type(k) == list:
				k = tuple(k)
			return tvs[k]
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

	# return a set of non-TypeVar types included in the arbitrary type signature 't'
	@staticmethod
	def setreal(t):
		if Type.is_scalar(t):
			return [t]
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

	# given a realized outtype, calculate the replacement that will transform the typevar into it
	# given ([4], [A]) i must calculate A=4
	@staticmethod
	def calculateReplacement(t, tv):
		if Type.is_typevar(tv):
			return t
		assert type(t) == type(tv)
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

def test_type_setreal():
	assert unittest(Type.setreal,
			[(set(),			((Type.A,),)),
			 ({Type.BOOL},			((Type.BOOL,),)),
			 ({Type.NUM},			((Type.NUM,),)),
			 ({Type.BOOL,Type.NUM},		((Type.NUM,Type.BOOL),)),
			 ({Type.NUM},			(([Type.NUM],),)),
			 ({Type.NUM},			(([[Type.NUM]],),)),
			 ({Type.BOOL},			((Type.BOOL,Type.BOOL),)),
			])

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
			return random.randint(1,2)
		elif type == Type.BOOL:
			return random.randint(0,1) == 0
		else:
			return val
	def mutate(self, depth, maxdepth):
		self.val = Value.randomval(self.type, self.val)

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
		return '%s%s' % (self.val, '' if self.index == [] else '['+(']['.join(str(i) for i in self.index))+']')
	def dump(self):
		return 'Variable(type=%s val=%s)' % (Type.repr(self.type), self.val) 
	def mutate(self, depth, maxdepth):
		pass
	def is_invariant(self):
		return False

# represents a transformation operation; a function
class Op:
	def __init__(self, name, outtype, intype, repr):
		self.name = name
		self.type = outtype
		self.intype = intype
		self.repr = repr
		# TODO: we can greatly simplify Expr() by pre-calculating a bunch of stuff here, also globally about Ops
		self.outset = Type.setreal(outtype)
		self.inset = Type.setreal(intype)
	def __repr__(self):
		return '%s %s%s' % (Type.repr(self.type), self.name, Type.repr(self.intype))
	# given a set of all possible available types from parameters and other function's output types, see if we match
	def inTypesMatch(self, availableTypes):
		#return any(all(Type.match(a, i) for i in self.intype) for a in availableTypes)
		availset = Type.setreal(availableTypes)
		#print(self.name,'inTypesMatch(inset=',self.inset,',availableTypes=',availableTypes,'availset=',availset,'&=',self.inset & availset,')')
		return (self.inset & availset) == self.inset

# id(x) -> x. used to wrap a Value/Variable in an Expr
Id = Op('id', Type.A, (Type.A,), lambda x: str(x))

# list of all possible operations
Ops = (
	#Op('not', Type.BOOL,	(Type.BOOL,),			lambda x:    '(not %s)' % (x,)),
	#Op('or',  Type.BOOL,	(Type.BOOL, Type.BOOL),		lambda x,y:  '(%s or %s)' % (x,y)),
	#Op('and', Type.BOOL,	(Type.BOOL, Type.BOOL),		lambda x,y:  '(%s and %s)' % (x,y)),
	#Op('if',  Type.A,	(Type.BOOL, Type.A, Type.A),	lambda x,y,z:'(%s if %s else %s)' % (y,x,z)),
	#Op('eq',  Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s == %s)' % (x,y)),
	#Op('gt',  Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s > %s)' % (x,y)),
	Op('gte', Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s >= %s)' % (x,y)),
	Op('add', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s + %s)' % (x,y)),
	#Op('sub', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s - %s)' % (x,y)),
	Op('mul', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s * %s)' % (x,y)),
	Op('div', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s / %s)' % (x,y)),
	# pow is a CPU sink. whereas all other functions produce output lte their parameters,
	# modest parameters can generate huge amounts of work, i.e. 
	#Op('pow', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s ** %s)' % (x,y)),
	#Op('sqrt', Type.NUM,	(Type.NUM,),			lambda x:    'sqrt(%s)' % (x,)),
	#Op('log', Type.NUM,	(Type.NUM,),			lambda x:    'log(%s)' % (x,)),
	#Op('mod', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s %% %s)' % (x,y)),
	#Op('abs', Type.NUM,	(Type.NUM,),			lambda x:    'abs(%s)' % (x,)),
	#Op('min', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  'min(%s,%s)' % (x,y)),
	Op('max', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  'max(%s,%s)' % (x,y)),
	#Op('len', Type.NUM,	([Type.A],),			lambda x:    'len(%s)' % (x,)),
	Op('sum', Type.NUM,	([Type.NUM],),			lambda x:    'sum(%s)' % (x,)),
	Op('map', [Type.B],	((Type.FUN,Type.B,(Type.A,)), [Type.A]),	lambda x,y: '[%s for %s in %s]' % (x,','.join(x.op.paramkeys),y)),
	Op('filter', [Type.A],	((Type.FUN,Type.BOOL,(Type.A,)), [Type.A]),
		lambda x,y: '[%s for %s in %s if %s]' % (','.join(x.op.paramkeys),','.join(x.op.paramkeys),y,x)),
	#Op('map-flatten', [Type.B],	((Type.FUN,Type.B,(Type.A,)), [[Type.A]]),
		#lambda x,y: '[%s for %s in %s for %s in %s]' % (x,','.join(x.op.paramkeys),y,x,','.join(x.op.paramkeys))),
		#[item for sublist in l for item in sublist]

	# date/time-related operations
	# these must be implemented for real analysis
	#Op('year', Type.NUM,	(Type.DATE,),				lambda x:    '%s.year' % (x,)),
	#Op('month', Type.NUM,	(Type.DATE,),				lambda x:    '%s.month' % (x,)),
	#Op('mday', Type.NUM,	(Type.DATE,),				lambda x:    '%s.mday' % (x,)),
	#Op('hour', Type.NUM,	(Type.DATE,),				lambda x:    '%s.hour' % (x,)),
	#Op('wday', Type.NUM,	(Type.DATE,),				lambda x:    '%s.weekday()' % (x,)),
)

OpOuttypes = [Type.BOOL,Type.NUM,[Type.A],[Type.B]]

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
Log = tuple([0, log(2)] + [log(n) for n in range(2, 100)])

# Expression is a value that applies a function to parameters to arrive at its value
class Expr(Value):

	# generate a random expression that generates a value of type 'outtype'
	# expression may be arbitrarily complex, but may only reference parameters, pre-defined Ops and random literals
	# @params tuple(Variable)
	# @outtype is a realized Type.X type, not a TypeVar.
	
	def __init__(self, params, outtype, depth=1, maxdepth=5):
		#print('Expr(params=',params,'outtype=',outtype,')')
		self.params = params
		self.type = copy.copy(outtype)
		self.exprs = []

		# special case for lambdas
		if type(outtype) == tuple and outtype[0] == Type.FUN:
			# TODO: break this block out
			_,outp,inp = outtype
			#print('created lambda inp=%s outp=%s' % (inp, outp))
			# reduce parameters to those being passed specifically, and rename for use within the function
			lparams = tuple(Variable(v,k) for k,v in zip(['x','y','z'], inp))
			self.op = Lambda(outp, inp, lparams)
			self.exprs = [Expr(lparams, outp, depth+1, maxdepth)]
			return

		opt = ops_by_outtype(outtype)
		#print('outtype=',Type.repr(outtype),'params=',params,'opt=',opt)
		r = random.random()
		if depth >= maxdepth or r < depth / maxdepth or opt == ():
			# generate a terminal (literal or variable) out of chance or because we have to
			# TODO: break this block out
			pt = Expr.params_by_type(params, outtype)
			#print('outtype=',Type.repr(outtype),'params=',[p.dump() for p in params],'pt=',pt)
			self.op = Id
			if pt == () or r < depth / maxdepth / 2:
				if Type.is_scalar(outtype):
					self.exprs = [Value(outtype)] # random literal
				elif type(outtype) == tuple: # tuple literal
					self.exprs = [tuple(Expr(params, t, depth+1, maxdepth) for t in self.type)]
				elif type(outtype) == list: # list literal
					# FIXME: do not wrap in a list if it's already a list....
					#print('self.type=',self.type)
					x = [Expr(params, t, depth+1, maxdepth) for t in outtype]
					self.exprs = [x]
				else:
					print('not expecting outtype=',outtype)
					assert False
			else: # random parameter
				self.exprs = [random.choice(pt)]
		else:
			# TODO: break this block out
			# only choose operations whose output matches our input and whose input
			# we can possibly supply with our parameters

			paramtypes = [x.type for x in Expr.params_by_type(params, Type.A)]
			availableTypes = OpOuttypes + paramtypes
			okops = [o for o in opt if o.inTypesMatch(availableTypes)]
			#print('okops=',okops)
			if okops == []:
				print('outtype=',Type.repr(outtype),'opt=',opt,'params=',[p.dump() for p in params])
				print('paramtypes=',Type.repr(paramtypes),'OpOuttypes=',[Type.repr(o) for o in OpOuttypes],'availableTypes=',[Type.repr(a) for a in availableTypes])
				assert False
			self.op = copy.deepcopy(random.choice(okops))
			#print('before self.op=',self.op,'outtype=',Type.repr(outtype))
			tvtypes = self.enforceTypeVars(outtype, params)
			#print('  after self.op=',self.op,'outtype=',Type.repr(outtype),'tvtypes=',tvtypes)
			assert self.op.type == outtype
			self.exprs = [Expr(params, it, depth+1, maxdepth) for it in self.op.intype]

	# randomly mutate Expr and/or sub-expressions
	# it is important to potentially preserve existing Exprs because only high-scoring Exprs get mutated, so what we have
	# isn't too bad in the first place. we must be able to move Expr between levels, replacing operations with their parameters
	# and vice versa, replacing random invariants
	# FIXME: somehow mutate() is unable to ever generate correct mutations concerning list types. i have no idea why.
	def mutate(self, depth, maxdepth):
		mutation = 0.90
		r = random.random()
		if r < mutation: # mutate self
			if r < mutation * 0.01:
				# swap parameters, a boring mutation
				if len(self.exprs) > 1:
					if self.exprs[0].type == self.exprs[1].type:
						self.exprs[:2] = self.exprs[1], self.exprs[0]
					elif len(self.exprs) > 2 and self.exprs[1].type == self.exprs[2].type:
						self.exprs[1:3] = self.exprs[2], self.exprs[1]
			elif r < mutation * 0.25:
				# preserve self as parameter to random new Expr 
				# x+(y+z) -> e+(x+z) | e+(y+x)
				e = Expr(self.params, self.type, depth, maxdepth)
				i = random.randint(0, len(e.exprs)-1)
				try:
					if e.exprs[i].type == self.type:
						e.exprs[i] = self
				except:
					pass
				return e
			elif r < mutation * 0.5:
				# replace self with parameter
				# x+(y+z) -> y | z
				y = random.choice(self.exprs)
				if type(y) == Expr and y.type == self.type:
					self = y
					return y
			else:
				# replace self with completely random new Expr
				self = Expr(self.params, self.type, depth, maxdepth)

		else: # maybe mutate child
			mutatable = tuple(e for e in self.exprs if hasattr(e,'mutate'))
			if mutatable != ():
				random.choice(mutatable).mutate(depth+1, maxdepth)
		return self

	# recursively co-dependent on instance method is_invariant()
	@staticmethod
	def is_invariant(x):
		if hasattr(e,'is_invariant'):
			if not x.is_invariant():
				return False
		elif type(x) in (tuple,list):
			return all(Expr.is_invariant(y) for y in x)
		else:
			return True

	# Is this Expr invariant? That is, does it contain references to variables? Co-dependent with Expr.is_invariant
	def is_invariant(self):
		ei = [(not hasattr(e,'is_invariant') or e.is_invariant()) if type(e) not in (tuple,list) else (all(Expr.is_invariant(f) for f in e)) for e in self.exprs]
		if self.op.name == 'map':
			return str(self.exprs[0]) == ','.join(self.exprs[0].op.paramkeys)
		elif self.op.name in ('if','filter'):
			return ei[0]
		else:
			return all(ei)

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

	# reduce expressions to their simplified, canonical form
	# relatively expensive, only use to clean up decent candidates
	# NOTE: this may seem like trivial aesthetics but reducing complexity
	# appears to speed solution
	# FIXME: appears to be returning list types instead of numbers sometimes, wtf
	def canonical(self):
		# recurse downwards, 
		self.exprs = [Expr.canonicalize(e) for e in self.exprs]
		if self.op.name == 'map':
			# [x for x in y] -> y
			if str(self.exprs[0]) == ','.join(self.exprs[0].op.paramkeys):
				self = self.exprs[1]
			# TODO: [2 for x in [0]]
		elif self.op.name == 'filter':
			#print('filter exprs[0]=%s' % (self.exprs[0],))
			v = str(self.exprs[0])
			if v == 'True':
				# filter(True, x) -> x
				self = self.exprs[1]
			elif v == 'False':
				# filter(False, x) -> []
				self.op, self.exprs = Id, [Value(self.exprs[1].type, [])]
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
					if e1 == '1':
						p = 0
					elif e0 == e1:
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

		elif self.op.name in ('eq','gte','gte'):
			# x == x -> True
			# x <= x -> True
			# x >= x -> True
			if str(self.exprs[0]) == str(self.exprs[1]):
				self.op, self.exprs = Id, [Value(Type.BOOL, True)]
		elif self.op.name in ('gt','lt'):
			# x < x -> False
			# x > x -> False
			if str(self.exprs[0]) == str(self.exprs[1]):
				self.op, self.exprs = Id, [Value(Type.BOOL, False)]
		elif self.op.name == 'if':
			# if(True,x,y) -> x
			# if(False,x,y) -> y
			v = self.exprs[0].invariant_val()
			if v == True:
				self = self.exprs[1]
			elif v == False:
				self = self.exprs[2]
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
		elif self.op.name == 'sqrt':
			# sqrt(0|1) -> 0|1
			if str(self.exprs[0]) in ('0','1'):
				self = self.exprs[0]
		elif self.op.name == 'log':
			# log(1) -> 0
			if str(self.exprs[0]) == '1':
				self.op, self.exprs = Id, [Value(Type.NUM, 0)]
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
			if type(e0) == Expr and e0.op is Id and type(e0.exprs[0]) == list:
				self.op, self.exprs = Id, [Value(Type.NUM, len(e0.exprs[0]))]
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
			if type(e0) == Expr and e0.op is Id and type(e0.exprs[0]) == list:
				if len(e0.exprs[0]) == 1:
					self = self.exprs[0].exprs[0][0]
				elif len(e0.exprs[0]) == 0:
					self.op, self.exprs = Id, [Value(Type.NUM, 0)]
			# TODO:...
			# sum(x[y] for x in foo) + sum(x[z] for x in foo) -> sum(x[y]+x[z] for y in foo)
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
	def enforceTypeVars(self, outtype, params):
		tvs = Type.typevars((self.op.intype, self.op.type))
		tvtypes = dict([(tv,None) for tv in tvs])
		ptypes = tuple(x.type for x in params)

		if type(self.op.intype[0]) == tuple and self.op.intype[0][0] == Type.FUN:
			# if we're a lambda then set output type
			if type(self.op.type) == list and Type.is_typevar(self.op.type[0]):
				tvtypes[self.op.type[0]] = outtype[0]
				k = self.op.intype[1][0]
				while type(k) == list:
					k = k[0]
				x = random.choice(ptypes)
				if type(x) == list:
					x = x[0]
				tvtypes[k] = x
		else:
			# select random type for each, based on paramtypes
			for tv in tvtypes.keys():
				tvtypes[tv] = outtype if tv == self.op.type else random.choice(ptypes)

		# enforce consistent outtype
		# FIXME: does this negate the above special-case code for FUNs?
		x = Type.calculateReplacement(outtype, self.op.type)
		if x != None:
			y = Type.typevars(self.op.type)[0]
			tvtypes[y] = x

		#print('op.name=%s outtype=%s self.op.intype=%s ptypes=%s' % (self.op.name, Type.repr(outtype), Type.repr(self.op.intype), ptypes))
		intypes = Type.typevar_replace(self.op.intype, tvtypes)
		if type(self.op.intype) == tuple:
			intypes = tuple(intypes)
		self.op.intype = intypes
		self.op.type = Type.typevar_replace(self.op.type, tvtypes)
		#if type(self.op.intype[0]) == tuple and self.op.intype[0][0] == Type.FUN:
			#print('op.name=%s type=%s op.type=%s op.intype=%s ptypes=%s' % (self.op.name, Type.repr(outtype), Type.repr(self.op.type),Type.repr(self.op.intype), ptypes))
			#assert type(self.op.type) != list
		return tvtypes

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

	# count the number of random invariants present
	@staticmethod
	def invariant_count(e):
		if type(e) != Expr:
			return int(type(e) == Value)
		elif e.op is Id:
			return int(type(e.exprs[0]) == Value)
		else:
			return sum([Expr.invariant_count(x) for x in e.exprs])

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
	test_type_setreal()
	test_type_calculateReplacement()
	test_expr_invariant()
	tv = Type.typevars(((Type.FUN, Type.B, (Type.A,)), [Type.A]))
	assert tv == list(set([1,0]))
	test_enforceTypeVars()
	test_expr2str()
	test_canonicalize()
	test_map_flatten()
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

# run Expr e(data), score the result
def run_score(estr, data, fscore):
	try:
		score = 0
		for d in data:
			res = eval('lambda foo:'+estr)(d[0])
			fs = fscore(d, res)
			score += fs
	except (ZeroDivisionError, ValueError):
		# ZeroDiv: /0 or %0
		# ValueError: log(0)
		score = WorstScore
	except:
		print(estr)
		sys.stdout.flush()
		sys.exit(1)
		# assign worst possible score, keep going
		score = WorstScore
	return score

# Expr p × population rankings
class KeepScore:
	def __init__(self, expr, score, gencnt):
		self.expr = expr
		self.score = score
		self.gencnt = gencnt
		self.size = Expr.size(expr)
		self.invarcnt = Expr.invariant_count(expr)
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
			return self.invarcnt < other.invarcnt
		if self.gencnt != other.gencnt: # then older over newer...
			return self.gencnt < other.gencnt
		return 0

# run each candidate against the data, score the results, keep the least-awful scoring functions
def evaluate(population, data, fscore, gencnt):
	keep = []
	uniq = dict((str(e), e) for e in population if not e.is_invariant())
	for estr,p in uniq.items():
		score = run_score(estr, data, fscore)
		if score != WorstScore:
			p = Expr.canonical(p)
			try:
				if not p.is_invariant():
					keep.append(KeepScore(p, score, gencnt))
			except AttributeError:
				pass
	return sorted(keep)

# KeepScore × Multi-generational logic
class FamilyMember:
	def __init__(self, ks, parent):
		self.ks = ks 
		self.parent = parent
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
		self.scores = [WorstScore] # NOTE: sorted() apparently isn't stable, so we need to keep track of score, not just gencnt
		self.lastgencnt = 0
		self.reversecnt = 0
	def show(self, pop, gencnt):
		self.reversecnt = min(len(self.scores)-1, self.reversecnt + int(gencnt < self.lastgencnt))
		self.lastgencnt = gencnt
		if pop != [] and pop[0].ks.score < self.scores[-1]:
			self.scores.append(pop[0].ks.score)
			if gencnt != 0:
				sys.stdout.write('\n')
		else: # otherwise, remove previous line
			sys.stdout.write('\b' * len(self.msg))
			#sys.stdout.write('\n')
		t = time.localtime()
		self.msg = '%04d-%02d-%02d-%02d:%02d:%02d gen %4u %s %s %s' % \
			(t.tm_year, t.tm_mon, t.tm_mday, t.tm_hour, t.tm_min, t.tm_sec,
			gencnt, '.' * (len(self.scores) - self.reversecnt),
			'' if pop == [] else '#' * int(Reporter.scale(pop[0].ks.score)),
			'' if pop == [] else pop[0].ks)
		sys.stdout.write(self.msg)
		sys.stdout.flush()
	# scale score 'n' to display value progress bar in most useful way
	@staticmethod
	def scale(n, maximum=80):
		if n < 10:
			return n
		elif n <= 10000:
			return min(maximum, 10 + math.sqrt(n-10))
		else:
			return min(maximum, 10 + math.sqrt(9990) + math.log(n-10000))

# where the magic happens. given some data to transform, some types and a scoring function, evolve code to 
# transform data[n][0] -> data[n][1]
# NOTE: currently deadend is set to a fixed generational count; it may make more sense instead to also incorporate
# score; it makes less sense to rewind as quickly to an ancestor with a much worse score
def evolve(data, score=lambda d,res:abs(d[1]-res), types=None, popsize=10000, maxdepth=5, popkeep=2, deadend=10):
	# sanity check types and ranges
	assert type(data[0]) == tuple
	assert type(score) == type(lambda _:_)
	assert 1 <= maxdepth < len(Log)
	assert popsize >= 1
	assert popkeep >= 1
	# initialize defaults
	if types == None:
		intype,outtype = Type.describe(data[0])
		print('evolve :: %s -> %s' % (Type.repr(intype),Type.repr(outtype)))
	else:
		intype,outtype = types
	assert intype != ()
	sym = (Variable(intype, 'foo'),)
	pop = []
	gencnt = 0
	r = Reporter()

	# generate/mutate functions, test them, keep the best ones

	while pop == []:
		population = (Expr(sym, outtype, 1, maxdepth) for _ in range(0, popsize))
		keep = evaluate(population, data, score, gencnt)[:popkeep]
		pop = [FamilyMember(ks, None) for ks in keep[:popkeep]]
		r.show(pop, gencnt)
		gencnt += 1

	# go until we find score=0, then spend at least a few generations trying to simplify
	while pop[0].ks.score > 0 or (gencnt <= pop[0].ks.gencnt + pop[0].ks.size + pop[0].ks.invarcnt):
		#print('pop=',[p.ks.expr for p in pop])
		parent = random.choice(pop)
		population = (copy.deepcopy(parent.ks.expr).mutate(1, maxdepth) for _ in range(0, popsize))
		keep = evaluate(population, data, score, gencnt)[:popkeep]
		if keep != [] and keep[0] < pop[0].ks: # improved generation
			pop = [FamilyMember(ks, parent) for ks in keep]
		else: # nothing better
			if (keep == [] or keep[0].score > 0) and gencnt - parent.ks.gencnt >= deadend: # we're stuck
				if parent.parent: # we're not at roots yet...
					# roll parent back to grandparent
					#print('\nrolling back to %s %s%s' % (id(parent.parent), parent.parent.ks.expr, ('.' * 100)))
					pop = [parent.parent] # FIXME: how to get grandparents' siblings?
					gencnt = parent.parent.ks.gencnt # reset gencnt, otherwise our rollback cascades all the way back
		r.show(pop, gencnt)
		gencnt += 1

	print('\ndone', pop[0])
	return pop[0]

if __name__ == '__main__':
	test()

	evolve( [
			# basic filter
			# expect: [x for x in foo if (x >= 4)]
			([1,2,3,4,5], [4,5]),
			([0,10,1e6,2,3], [10,1e6]),
			([0,0,0,0,0,0,1,2,3], []),
		], popsize=1000, score=lambda d,res: sum([abs(x-y) for x,y in zip(d[1], res)]) + abs(sum(d[1])-sum(res)))

	evolve( [
			# expect: sum([x[0] for x in foo])
			# got: sum([sum([x[0]]) for x in foo])
			([(10,1)], 10),
			([(2000,1)], 2000),
			([(-2000,1)], -2000),
		], maxdepth=3, popsize=100)

	evolve( [
			# expect: ((foo+foo)+1) or ((foo*2)+1)
			# got:    ((1 + foo) + foo)
			#         (foo + (1 + foo))
			(10, 21),
			(1e6, 1e6*2+1),
		], popsize=1000)

	evolve( [
			# expect: foo
			(10, 10),
			(1e6, 1e6),
		], popsize=400)

	evolve( [ # ensure we can produce tuple results
			# expect: (foo,)
			(100, (100,)),
			(1000, (1000,)),
		], popsize=1000, maxdepth=3, score=lambda d,res:abs(d[1][0]-res[0]))

	evolve( [
			# expect: sum([(x[0]+x[1]+x[2]+x[3])/len(x) for x in foo])
			# or maybe: sum([x[0]/2 for x in foo])
			# GOT: (sum([x[0] for x in foo]) / 2)
			#      (0.5 * sum([x[0] for x in foo]))
			([(5,0,2,3)], 2.5),
			([(50,0,50,0)], 25),
			([(100,100,0,0)], 50),
			([(2,0,0,2)], 1),
		], popsize=5000)

	evolve( [ # extract tuple members and re-wrap them
			# expect: (foo[0]+1, foo[0]+foo[0]+2)
			# got: ((foo[0] + 1), (2 + (foo[0] + foo[0])))
			((100,), (101,202)),
			((1000,), (1001,2002)),
		], score=lambda d,res:sum(abs(x-y) for x,y in zip(d[1],res)))

	evolve( [
			# expect: sum([x[0]*x[1]+x[2] for x in foo])
			# GOT: (sum([x[2] for x in foo]) + sum([(x[1] * x[0]) for x in foo]))
			#      (sum([(x[1] * x[0]) for x in foo]) + sum([x[2] for x in foo]))
			([(10,3,5)], 10*3+5),
			([(3,3,1)], 3*3+1),
			([(2,1,0)], 2*1+0),
			([(1000,50,55)], 1000*50+55),
		], maxdepth=6, popsize=3000)

	evolve( [
			# expect: sum([(x[0]+x[1]+x[2]+x[3])/4 for x in foo])
			# GOT: ((sum([x[3] for x in foo]) / 2) + (sum([x[1] for x in foo]) / sum([5])))
			#      ((sum([x[3] for x in foo]) / 2) + (sum([x[1] for x in foo]) / 5))
			([(0,5,2,3)], 2.5),
			([(0,0,50,50)], 25),
			([(2,0,0,2)], 1),
		], maxdepth=8)

	################ Beyond this point stuff doesn't work

	"""
	evolve( [
			# FIXME: need this exact code to flatten list, but my code can't generate it!
			# expect: [y for y in x for x in foo]
			# GOT: 
			([[1,2,3]], [1,2,3]),
		], popsize=1000, score=lambda d,res: sum([abs(x-y) for x,y in zip(d[1], res)]) + (1e6 * abs(len(d[1]) - len(res))))
	"""
