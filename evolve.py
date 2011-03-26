#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
design genetic algorithm framework

purely functional, immutable variables
lists are assumed to have homogenous members
tuples are assumed to have heterogenous members
support lambda, higher-order functions, TypeVars

TODO: all Expr.exprs should be wrapped in Value()

"""

import random
from test import unittest
from copy import copy,deepcopy
import math

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
		return '%s' % (self.val,)
	def mutate(self, _):
		self.val = Value.randomval(self.type, self.val)
	def is_invariant(self):
		return self.invariant
	def dump(self):
		return 'Value(type=%s val=%s invariant=%s)' % (Type.repr(self.type), self.val, self.invariant) 

class Op:
	def __init__(self, name, outtype, intype, repr):
		self.name = name
		self.outtype = outtype
		self.intype = intype
		self.repr = repr
		# TODO: we can greatly simplify Expr() by pre-calculating a bunch of stuff here, also globally about Ops
	def __repr__(self):
		return '%s %s%s' % (Type.repr(self.outtype), self.name, Type.repr(self.intype))
	# given a set of all possible available types from parameters and other function's output types, see if we match
	def inTypesMatch(self, availableTypes):
		# FIXME: this is overly simplistic regarding lambda/FUNs
		#print(self.name,'inTypesMatch(intype=',self.intype,',availableTypes=',availableTypes,')')
		return any(Type.match(a, self.intype) for a in availableTypes)

Id = Op('id', Type.A, (Type.A,), lambda x: str(x))
# NOTE: at the moment all these functions actually appear to work, I'm just testing various aspects of them
Ops = (
	Op('not', Type.BOOL,	(Type.BOOL,),			lambda x:    '(not %s)' % (x,)),
	Op('or',  Type.BOOL,	(Type.BOOL, Type.BOOL),		lambda x,y:  '(%s or %s)' % (x,y)),
	Op('and', Type.BOOL,	(Type.BOOL, Type.BOOL),		lambda x,y:  '(%s and %s)' % (x,y)),
	Op('if',  Type.A,	(Type.BOOL, Type.A, Type.A),	lambda x,y,z:'(%s if %s else %s)' % (y,x,z)),
	Op('eq',  Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s == %s)' % (x,y)),
	Op('gt',  Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s > %s)' % (x,y)),
	Op('gte', Type.BOOL,	(Type.A,   Type.A),		lambda x,y:  '(%s >= %s)' % (x,y)),
	Op('add', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s + %s)' % (x,y)),
	#Op('sub', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s - %s)' % (x,y)),
	Op('mul', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s * %s)' % (x,y)),
	Op('div', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s / %s)' % (x,y)),
	#Op('mod', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  '(%s %% %s)' % (x,y)),
	#Op('min', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  'min(%s,%s)' % (x,y)),
	#Op('max', Type.NUM,	(Type.NUM, Type.NUM),		lambda x,y:  'max(%s,%s)' % (x,y)),
	Op('sum', Type.NUM,	([Type.NUM],),			lambda x:    'sum(%s)' % (x,)),
	Op('map', [Type.B],	((Type.FUN,Type.B,(Type.A,)), [Type.A]),	lambda x,y: '[%s for %s in %s]' % (x,','.join(x.op.paramkeys),y)),
	Op('filter', [Type.A],	((Type.FUN,Type.BOOL,(Type.A,)), [Type.A]),
		lambda x,y: '[%s for %s in %s if %s]' % (','.join(x.op.paramkeys),','.join(x.op.paramkeys),y,x)),
	Op('len', Type.NUM,	([Type.A],),				lambda x:    'len(%s)' % (x,)),
)

OpOuttypes = [Type.BOOL,Type.NUM,Type.A,[Type.A]]

def ops_by_outtype(outtype):
	return [o for o in Ops if Type.match(o.outtype, outtype)]

# [y for y in expr]
# [y for y in expr if y]

class Lambda(Op):
	def __init__(self, outtype, intype, params):
		self.name = 'lambda'
		self.outtype = outtype
		self.intype = intype
		self.params = params
		self.paramkeys = sorted(params.keys())
	def repr(self, expr):
		#return 'lambda %s:%s' % (','.join(sorted(self.params.keys())), expr)
		return str(expr)
	def dump(self):
		return 'Lambda()'

# pre-calculate logarithm
Log = tuple([0, math.log(2)] + [math.log(n) for n in range(2, 100)])

# Expression is a value that applies a function to parameters to arrive at its value
class Expr(Value):

	# generate a random expression that generates a value of type 'outtype'
	# expression may be arbitrarily complex, but may only reference parameters, pre-defined Ops and random literals
	# @params dict{varname : type}
	# @outtype is a realized Type.X type, not a TypeVar.
	def __init__(self, params, outtype, depth=1, maxdepth=5):
		#print('Expr(params=',params,'outtype=',outtype,')')
		self.depth = depth
		self.params = copy(params)
		self.outtype = copy(outtype)
		self.exprs = []

		# special case for lambdas
		if type(outtype) == tuple and outtype[0] == Type.FUN:
			_,outp,inp = outtype
			# if we're generating a list-processing lambda, strip the list type off the input/output types
			if type(outp) == list:
				#inp = (inp[0][0],)
				outp = outp[0]
			#print('created lambda inp=%s outp=%s' % (inp, outp))
			# reduce parameters to those being passed specifically, and rename for use within the function
			self.params = dict(zip(['x','y','z'], inp))
			self.op = Lambda(outp, inp, self.params)
			self.exprs = [Expr(self.params, outp, depth+1)]
			return

		opt = ops_by_outtype(outtype)
		#print('opt=',opt)
		r = random.random()
		if opt == [] or depth == maxdepth or r < Log[depth] / Log[maxdepth]:
			pt = Expr.params_by_type(params, outtype)
			#print('pt=',pt)
			# generate a literal or variable, out of chance or because we have to
			self.op = Id
			if pt == [] or (r < 0.05 and outtype != Type.BOOL):
				if Type.is_scalar(outtype):
					self.exprs = [Value(outtype)] # random literal
				elif type(outtype) == tuple: # tuple literal
					self.exprs = [tuple(Expr(params, t, depth+1) for t in self.outtype)]
				else: # list literal
					# FIXME: do not wrap in a list if it's already a list....
					x = [Expr(params, t, depth+1) for t in self.outtype]
					if len(x) == 1 and type(x[0].outtype) == list:
						x = x[0] # unwrap
					self.exprs = [x]
			else:
				# random parameter
				#print('outtype=',outtype,'pt=',pt)
				self.exprs = [Value(outtype, random.choice(pt))]
		else:
			# only choose operations whose output matches our input and whose input
			# we can possibly supply with our parameters
			paramtypes = list(params.values())
			availableTypes = OpOuttypes + paramtypes
			okops = [o for o in opt if o.inTypesMatch(availableTypes)]
			if okops == []:
				print('availableTypes=',availableTypes)
				assert False
			self.op = deepcopy(random.choice(okops))
			tvtypes = self.enforceTypeVars(outtype)
			#print('self.op=',self.op, 'outtype=',outtype,'tvtypes=',tvtypes)
			self.exprs = [Expr(params, it, depth+1) for it in self.op.intype]

	# randomly mutate myself or one of my child expressions
	def mutate(self, mutation=0.3):
		r = random.random()
		if r < mutation:
			self.__init__(self.params, self.outtype, self.depth)
		else:
			mutatable = [e for e in self.exprs if type(e) in (Expr,Value)]
			if mutatable != []:
				random.choice(mutatable).mutate(mutation)
		return self

	def is_invariant(self):
		ei = [(hasattr(e,'is_invariant') and e.is_invariant()) for e in self.exprs]
		if self.op.name == 'map':
			return str(self.exprs[0]) == str(self.exprs[0].op.paramkeys)
		elif self.op.name == 'filter':
			return ei[0]
		else:
			return all(ei)

	def invariant_val(self):
		if type(self.exprs[0]) == Value:
			return self.exprs[0].val
		elif type(self.exprs[0]) in (bool,int,float):
			return self.exprs[0]
		else:
			return self.exprs[0].invariant_val()

	def dump(self):
		return 'Expr(op=%s outtype=%s invariant=%s exprs=[%s])' % \
			(self.op.name, Type.repr(self.outtype), self.is_invariant(), \
			','.join([e.dump() if hasattr(e,'dump') else '(type='+str(type(e))+' '+str(e)+')' for e in self.exprs]))

	# reduce expressions 
	def canonicalize(self):
		self.exprs = [e.canonicalize() if hasattr(e,'canonicalize') else e for e in self.exprs]
		if self.op is Id or self.op.name in ('add','sub','mul','div'):
			try:
				e = eval(str(self))
				# if it doesn't blow up, it's been canonicalized...
				self.exprs = [Value(self.outtype, e)]
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
					self.exprs = [Value(self.exprs[1].outtype, [])]
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
		paramtypelist = list(self.params.values())
		tvs = Type.typevars((self.op.intype, self.op.outtype))
		tvtypes = dict([(tv,None) for tv in tvs])
		if type(self.op.intype[0]) == tuple and self.op.intype[0][0] == Type.FUN:
			if type(self.op.outtype) == list and Type.is_typevar(self.op.outtype[0]):
				tvtypes[self.op.outtype[0]] = outtype[0]
				# FIXME: this is the contentious line... without [0] we get garbage, with [0] we finish quickly like we should, but with the wrong answer
				x = random.choice(paramtypelist)
				if type(x) == list:
					x = x[0]
				tvtypes[self.op.intype[1][0]] = x
		else:
			# select random type for each, based on paramtypes
			for tv in tvtypes.keys():
				tvtypes[tv] = outtype if tv == self.op.outtype else random.choice(paramtypelist)
		# replace inputtype TypeVar instances with translations

		#print('op.name=%s outtype=%s self.op.intype=%s paramtypelist=%s' % (self.op.name, Type.repr(outtype), Type.repr(self.op.intype), paramtypelist))

		intypes = Type.typevar_replace(self.op.intype, tvtypes)
		if type(self.op.intype) == tuple:
			intypes = tuple(intypes)
		self.op.intype = intypes
		self.op.outtype = Type.typevar_replace(self.op.outtype, tvtypes)

		#if type(self.op.intype[0]) == tuple and self.op.intype[0][0] == Type.FUN:
			#print('op.name=%s outtype=%s op.outtype=%s op.intype=%s paramtypelist=%s' % (self.op.name, Type.repr(outtype), Type.repr(self.op.outtype),Type.repr(self.op.intype), paramtypelist))
			#assert type(self.op.outtype) != list
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
				p += ['%s[%d]' % (k,i) for i,x in enumerate(v) if Type.match(t, x)]
				#for i in range(0, len(v)):
					#if Type.match(t, v[i]):
						#p.append('%s[%d]' % (k,i))
		return p

	#
	# Expr scoring methods
	#

	# count the number of total nodes
	@staticmethod
	def size(e):
		if type(e) != Expr:
			return 1
		else:
			return 1 + sum([Expr.size(x) for x in e.exprs])

	# count the number of random literals
	@staticmethod
	def magic_numbers(e):
		if type(e) != Expr:
			return 1
		if e.op is Id:
			return int(type(e.exprs[0]) == Value)
		else:
			return sum([Expr.magic_numbers(x) for x in e.exprs])

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

def test_expr_invariant():
	v = Value(Type.BOOL, True)
	assert v.is_invariant()
	e = Expr({'a':Type.BOOL}, Type.BOOL)
	e.exprs = [v]
	assert e.is_invariant()

def test_enforceTypeVars():
	e = Expr({'foo':[(Type.NUM,Type.NUM)]},[Type.NUM])
	#print(e.enforceTypeVars(e.outtype))
	#print(e.outtype)
	#print('e=',e)

def test():
	test_params_by_type()
	test_type_describe()
	test_expr_invariant()
	tv = Type.typevars(((Type.FUN, Type.B, (Type.A,)), [Type.A]))
	assert tv == list(set([1,0]))
	test_enforceTypeVars()
	print('Tests passed.')

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
			res = eval('lambda foo:'+str(p))(d[0])
			fs = fscore(d, res)
			#print('d=%s res=%s -> %s' %(d,res,fs))
			score += fs
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
		if not p.is_invariant():
			score = run_score(p, data, fscore)
			if score != WorstScore:
				# retain 3 scores. lower is always better, and sorted() works that way too
				# FIXME: think this was fucking us up
				#p = p.canonicalize()
				keep.append(((score, Expr.size(p), Expr.magic_numbers(p)), p))
	return sorted(keep)

def evolve(data, score, types=None, popsize=10000, maxdepth=10, popkeep=2, mutation=0.7, deadend=0):
	# sanity check types and ranges
	assert type(data[0]) == tuple
	assert type(score) == type(lambda _:_)
	assert 2 <= maxdepth < len(Log)
	assert 1 <= popsize
	assert 1 <= popkeep
	# initialize defaults
	if types == None:
		intype,outtype = Type.describe(data[0])
		print('types %s -> %s' % (Type.repr(intype),Type.repr(outtype)))
	else:
		intype,outtype = types
	sym = {'foo':intype} # FIXME: tied to run_score()
	print('sym={%s}' % (','.join(['%s:%s' % (k,Type.repr(v)) for k,v in sym.items()])))
	pop = []
	gencnt = 0

	# find at least one func that doesn't totally suck
	while pop == []:
		population = [Expr(sym, outtype, maxdepth=maxdepth) for _ in range(0, popsize)]
		keep = evaluate(population, data, score)[:popkeep]
		pop = sorted(pop + keep)[:popkeep]
		print('gen %d' % (gencnt,))
		gencnt += 1

	# mutate those functions
	while pop[0][0][0] > 0 or pop[0][0][2] > 1:
		population = [deepcopy(random.choice(pop)[1]).mutate() for _ in range(0, popsize)]
		keep = evaluate(population, data, score)[:popkeep]
		#print('keep=',keep)
		pop = sorted(pop + keep)[:popkeep]
		bestscore,best = pop[0]
		print('gen %d score=%.0f %s (dump=%s)' % (gencnt, bestscore[0], str(best), best.dump()))
		assert not best.is_invariant()
		gencnt += 1

	print('done', pop[0])
	return pop[0]

if __name__ == '__main__':
	test()
	foo = [(1,2),(3,4)]
	sym = {'foo':Type.describe(foo)}
	e = [Expr(sym, Type.NUM, maxdepth=5) for _ in range(0, 10)]

	evolve(
		[
			# expect: sum([(x[0]+x[1]+x[2]+x[3])/len(x) for x in foo])
			# GOT: 
			([(0,5,2,3)], 2.5),
			([(0,0,50,50)], 25),
			([(2,0,0,2)], 1),
		],
		lambda data,res: abs(sum(data[0][0])/len(data[0][0]) - res),
		popsize=10000,
		maxdepth=20,
		popkeep=5
	)

	"""
	evolve(
		[
			# expect: sum([(x[0]+x[1]+x[2]+x[3])/len(x) for x in foo])
			# or maybe: sum([x[0]/2 for x in foo])
			# GOT: (sum([x[0] for x in foo]) / 2)
			([(5,0,2,3)], 2.5),
			([(50,0,50,0)], 25),
			([(2,0,0,2)], 1),
		],
		lambda data,res: abs(sum(data[0][0])/len(data[0][0]) - res),
		popsize=10000,
		maxdepth=20,
		popkeep=5
	)
	"""

	"""
	evolve(
		[
			# sum([x[0] for x in foo])
			# actually got: sum([sum([x[0]]) for x in foo])
			([(10,1)], 10),
			([(20,1)], 20),
		],
		lambda data,res: abs(data[0][0][0] - res),
		popsize=10000,
		maxdepth=20,
		popkeep=5
	)
	"""

"""

gen 3 score=20 sum([3 for x in foo])
	(dump=Expr(op=sum outtype=Num invariant=False
		exprs=[Expr(op=map outtype=[Num] invariant=False
			exprs=[Expr(op=lambda outtype=(Fun,Num,([(Num,Num)])) invariant=True
				exprs=[Expr(op=id outtype=Num invariant=True exprs=[Value(type=Num val=3 invariant=True)])]),
				Expr(op=id outtype=[[(Num,Num)]] invariant=False exprs=[Expr(op=id outtype=[(Num,Num)] invariant=False exprs=[Value(type=[(Num,Num)] val=foo invariant=False)])])])]))
"""
