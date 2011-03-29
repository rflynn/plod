#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
design genetic algorithm framework

purely functional, immutable variables
lists are assumed to have homogenous members
tuples are assumed to have heterogenous members
support lambda, higher-order functions, TypeVars

slowest features:
	lots of deepcopy()s for mutations
	Type.match() called a lot

"""

import random
from test import unittest
from copy import copy,deepcopy
import math
from math import sqrt,log
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
		(type(spec) == type(t) and type(spec) in (tuple,list) and len(spec) == len(t) and all([Type.match(x,y) for x,y in zip(spec,t)])))
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
			return random.randint(1,5)
		elif type == Type.BOOL:
			return random.randint(0,1) == 0
		else:
			return val
	def mutate(self):
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
	def mutate(self):
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
	#Op('pow', Type.NUM,	(Type.NUM, Type.NUM),		lambda x:    '(%s ** %s)' % (x,)),
	Op('sqrt', Type.NUM,	(Type.NUM, ),			lambda x:    'sqrt(%s)' % (x,)),
	#Op('log', Type.NUM,	(Type.NUM, ),			lambda x:    'log(%s)' % (x,)),
	#Op('mod', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s %% %s)' % (x,y)),
	#Op('abs', Type.NUM,	(Type.NUM,),			lambda x:    'abs(%s)' % (x,)),
	#Op('min', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  'min(%s,%s)' % (x,y)),
	#Op('max', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  'max(%s,%s)' % (x,y)),
	Op('len', Type.NUM,	([Type.A],),			lambda x:    'len(%s)' % (x,)),
	Op('sum', Type.NUM,	([Type.NUM],),			lambda x:    'sum(%s)' % (x,)),
	Op('map', [Type.B],	((Type.FUN,Type.B,(Type.A,)), [Type.A]),	lambda x,y: '[%s for %s in %s]' % (x,','.join(x.op.paramkeys),y)),
	Op('map-flatten', [Type.B],	((Type.FUN,Type.B,(Type.A,)), [[Type.A]]),
		lambda x,y: '[%s for %s in %s for %s in %s]' % (x,','.join(x.op.paramkeys),y,x,','.join(x.op.paramkeys))),
		#[item for sublist in l for item in sublist]
	Op('filter', [Type.A],	((Type.FUN,Type.BOOL,(Type.A,)), [Type.A]),
		lambda x,y: '[%s for %s in %s if %s]' % (','.join(x.op.paramkeys),','.join(x.op.paramkeys),y,x)),

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
Log = tuple([0, log(2)] + [log(n) for n in range(2, 100)])

# Expression is a value that applies a function to parameters to arrive at its value
class Expr(Value):

	# generate a random expression that generates a value of type 'outtype'
	# expression may be arbitrarily complex, but may only reference parameters, pre-defined Ops and random literals
	# @params tuple(Variable)
	# @outtype is a realized Type.X type, not a TypeVar.
	def __init__(self, params, outtype, depth=1, maxdepth=5):
		#print('Expr(params=',params,'outtype=',outtype,')')
		self.depth = depth
		self.maxdepth = maxdepth
		self.params = copy(params)
		self.type = copy(outtype)
		self.exprs = []

		# special case for lambdas
		if type(outtype) == tuple and outtype[0] == Type.FUN:
			# TODO: break this block out
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
		#print('outtype=',outtype,'params=',params,'opt=',opt)
		r = random.random()
		if opt == () or depth >= maxdepth or r < Log[depth] / Log[maxdepth]:
			# TODO: break this block out
			# generate a literal or variable, out of chance or because we have to
			pt = Expr.params_by_type(params, outtype)
			#print('pt=',pt)
			self.op = Id
			if pt == () or (r < Log[depth]/Log[maxdepth]/10 and outtype != Type.BOOL):
				if Type.is_scalar(outtype):
					self.exprs = [Value(outtype)] # random literal
				elif type(outtype) == tuple: # tuple literal
					self.exprs = [tuple(Expr(params, t, depth+1) for t in self.type)]
				elif type(outtype) == list: # list literal
					# FIXME: do not wrap in a list if it's already a list....
					#print('self.type=',self.type)
					x = [Expr(params, t, depth+1) for t in self.type]
					if len(x) == 1 and type(x[0].type) == list:
						x = x[0] # unwrap
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
	def mutate(self):
		mutation = Log[self.depth] / Log[self.maxdepth]
		r = random.random()
		if r < mutation: # mutate self
			e = Expr(self.params, self.type, self.depth)
			if r < mutation * (1/3):
				# preserve self as parameter to e
				# x(y,z) -> e(x,a)
				i = random.randint(0, len(e.exprs)-1)
				if (hasattr(e.exprs[i],'type') and e.exprs[i].type == self.type) or type(e.exprs[i]) == self.type:
					e.exprs[i] = deepcopy(self)
			elif r < mutation * (2/3):
				# replace self with parameter
				# x(y,z) -> y
				y = random.choice(self.exprs)
				if type(y) == Expr and y.type == self.type:
					e = y
			return e
		else: # maybe mutate child
			mutatable = tuple(e for e in self.exprs if hasattr(e,'mutate'))
			if mutatable != ():
				random.choice(mutatable).mutate()
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
	def canonical(self):
		# recurse downwards, 
		self.exprs = [Expr.canonicalize(e) for e in self.exprs]

		if self.op.name == 'map':
			# [x for x in y] -> y
			#print('map exprs[0]=%s paramkeys=%s list=%s' % (self.exprs[0],','.join(self.exprs[0].op.paramkeys), self.exprs[1]))
			if str(self.exprs[0]) == ','.join(self.exprs[0].op.paramkeys):
				#print('self=',self.exprs[1])
				# FIXME: logic is correct but this doesn't work. why not?
				self = self.exprs[1]

		elif self.op.name == 'filter':
			#print('filter exprs[0]=%s' % (self.exprs[0],))
			v = str(self.exprs[0])
			if v == 'True':
				# filter(True, x) -> x
				# FIXME: logic is correct but this doesn't work. why not?
				#self = self.exprs[1]
				return self.exprs[1]
			elif v == 'False':
				# filter(False, x) -> []
				# FIXME: logic is correct but this doesn't work. why not?
				self.op, self.exprs = Id, [Value(self.exprs[1].type, [])]

		elif self.op.name in ('add','sub','mul','div'):
			try:
				# try to reduce numerical expressions
				x = eval(str(self))
				if x == round(x):
					# only keep integers; prefer expressions to mysterious floating point literals
					self.op, self.exprs = Id, [Value(self.type, x)]
			except:
				e0, e1 = str(self.exprs[0]), str(self.exprs[1])
				p = None # which parameter to reduce to? take action only iff 0,1
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
					if p is not None:
						self.op, self.exprs = Id, [Value(self.type, self.exprs[p])]
		elif self.op.name in ('gt','lt'):
			# x < x -> False
			# x > x -> False
			if str(self.exprs[0]) == str(self.exprs[1]):
				self.op, self.exprs = Id, [Value(Type.BOOL, False)]
		elif self.op.name in ('eq','lte','gte'):
			# x == x -> True
			# x <= x -> True
			# x >= x -> True
			if str(self.exprs[0]) == str(self.exprs[1]):
				self.op, self.exprs = Id, [Value(Type.BOOL, True)]
		elif self.op.name == 'if':
			# if(True,x,y) -> x
			# if(False,x,y) -> y
			v = self.exprs[0].invariant_val()
			if v == True:
				self = self.exprs[1]
			elif v == False:
				self = self.exprs[2]
		elif self.op.name == 'sqrt':
			# sqrt(0) -> 0
			# sqrt(1) -> 1
			if str(self.exprs[0]) in ('0','1'):
				self = self.exprs[0]
		elif self.op.name == 'log':
			# log(1) -> 0
			if str(self.exprs[0]) == '1':
				self.op, self.exprs = Id, [Value(Type.NUM, 0)]
		elif self.op.name == 'len':
			# realize len([...])
			e0 = self.exprs[0]
			if type(e0) == Expr and e0.op is Id and type(e0.exprs[0]) == list:
				self.op, self.exprs = Id, [Value(Type.NUM, len(e0.exprs[0]))]
		elif self.op.name == 'sum':
			# sum([x]) == x
			e0 = self.exprs[0]
			if type(e0) == Expr and e0.op is Id and type(e0.exprs[0]) == list:
				if len(e0.exprs[0]) == 1:
					self = self.exprs[0].exprs[0][0]
				elif len(e0.exprs[0]) == 0:
					self.op, self.exprs = Id, [Value(Type.NUM, 0)]
			# TODO:...
			# sum(y[m] for y in foo) + sum(y[n] for y in foo) -> sum(y[m]+y[n] for y in foo)
		return self

	def __repr__(self):
		return self.op.repr(*self.exprs)
	def __lt__(self, other):
		return 0
	def __gt__(self, other):
		return 1

	# given a Op, fill in any TypeVariables with actual types
	def enforceTypeVars(self, outtype):
		tvs = Type.typevars((self.op.intype, self.op.type))
		tvtypes = dict([(tv,None) for tv in tvs])
		ptypes = tuple(x.type for x in self.params)
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

def test_expr2str():
	e = tuple(Expr((Variable(Type.NUM,'a'),),(Type.NUM,), maxdepth=1) for _ in range(0, 50))

def test_canonicalize():
	e = tuple(Expr.canonicalize(Expr((Variable([Type.NUM],'a'),),(Type.NUM,), maxdepth=1)) for _ in range(0, 1000))
	esf = [e for e in e if 'True' in str(e) or 'False' in str(e)]# or ('x for x in' in str(e) and not 'x for x in a' in str(e))]
	if esf != []:
		print('non-canonicalized=',esf[0],esf[0].dump())
		assert esf == []

def test_map_flatten():
	e = tuple(Expr.canonicalize(Expr((Variable([[Type.NUM]],'a'),),[Type.NUM], maxdepth=4)) for _ in range(0, 10))
	print('map-flatten=',e)

def test():
	test_type_describe()
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
		return 'score=%g size=%u magic=%u gencnt=%u %s' % \
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
				p = Expr.canonical(p)
				try:
					if not p.is_invariant():
						keep.append(KeepScore(p, score, gencnt))
				except:
					pass
	return sorted(keep)

def evolve(data, score=lambda d,res:abs(d[1]-res), types=None, popsize=10000, maxdepth=10, popkeep=2, deadend=0):
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
	assert intype != ()
	sym = (Variable(intype, 'foo'),)
	pop = []
	gencnt = 0

	# generate/mutate functions, test them, keep the best ones
	while pop == [] or pop[0].score > 0:
		if pop == []:
			population = (Expr(sym, outtype, maxdepth=maxdepth) for _ in range(0, popsize))
		else:
			population = (deepcopy(random.choice(pop).p).mutate() for _ in range(0, popsize))
		keep = evaluate(population, data, score, gencnt)[:popkeep]
		pop = sorted(pop + keep)[:popkeep]
		if pop != [] and pop[0].gencnt == gencnt:
			t = time.localtime()
			print('%04d-%02d-%02d-%02d:%02d:%02d gen %2u %s %s' % \
				(t.tm_year, t.tm_mon, t.tm_mday, t.tm_hour, t.tm_min, t.tm_sec,
			 	gencnt, '' if pop == [] else '#' * round(math.log(pop[0].score+1)+0.5), '' if pop == [] else pop[0]))
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
		], popsize=1000)

	evolve( [
			# expect: ((foo+foo)+1) or ((foo*2)+1)
			# got:    ((1 + foo) + foo)
			#         (foo + (1 + foo))
			(10, 21),
			(1e6, 1e6*2+1),
		], popsize=2000)

	evolve( [ # ensure we can produce tuple results
			# expect: (foo,)
			(100, (100,)),
			(1000, (1000,)),
		], maxdepth=3, score=lambda d,res:abs(d[1][0]-res[0]))

	evolve( [ # extract tuple members and re-wrap them
			# expect: (foo[0]+1, foo[0]+foo[0]+2)
			# got: ((foo[0] + 1), (2 + (foo[0] + foo[0])))
			((100,), (101,202)),
			((1000,), (1001,2002)),
		], maxdepth=3, score=lambda d,res:sum(abs(x-y) for x,y in zip(d[1],res)))

	evolve( [
			# basic filter
			# expect: [x for x in foo if (x > 3)]
			([1,2,3,4,5], [4,5]),
		], score=lambda d,res: sum([abs(x-y) for x,y in zip(d[1], res)]) + (1e6 * abs(len(d[1])-len(res))))

	evolve( [
			# expect: sum([x[0] for x in foo])
			# got: sum([sum([x[0]]) for x in foo])
			([(10,1)], 10),
			([(20,1)], 20),
		], popsize=3000)

	evolve( [
			# expect: sum([(x[0]+x[1]+x[2]+x[3])/len(x) for x in foo])
			# or maybe: sum([x[0]/2 for x in foo])
			# GOT: (sum([x[0] for x in foo]) / 2)
			#      (0.5 * sum([x[0] for x in foo]))
			([(5,0,2,3)], 2.5),
			([(50,0,50,0)], 25),
			([(2,0,0,2)], 1),
		], popsize=5000)

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
			#      ((sum([x[3] for x in foo]) / 2) + (sum([x[1] for x in foo]) / 5))
			([(0,5,2,3)], 2.5),
			([(0,0,50,50)], 25),
			([(2,0,0,2)], 1),
		], maxdepth=10, popkeep=5)

	################ Beyond this point stuff doesn't work

	evolve( [
			# FIXME: need this exact code to flatten list, but my code can't generate it!
			# expect: [y for y in x for x in foo]
			# GOT: 
			([[1,2,3]], [1,2,3]),
		], score=lambda d,res: sum([abs(x-y) for x,y in zip(d[1], res)]) + (1e6 * abs(len(d[1]) - len(res))))

