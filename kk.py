# Solver for KenKen puzzles (version 3)
#
# We represent the set of possible values in a solution's cells as a string
# of integers; this approach only works for problems with N <= 9
import	string


# Return first non-false value, or False
def first(iterable):
	for i in iterable:
		if (i): return i
	return False

# Can we select exactly one member from each set s.t. the sum of all selected members is t?
d_sum_queries = {}
def can_make_sum_p(t, sets):
	if (len(sets) == 1): return (t in sets[0])
	r = d_sum_queries.get((t, sets))
	if (r == None):
		head = sets[0]; tail = sets[1:]
		r = any(can_make_sum_p(t-e, tail) for e in head if e <= t)
		d_sum_queries[(t, sets)] = r
	return r

# Can we select exactly one member from each set s.t. the difference of all selected members is t?
d_diff_queries = {}
def can_make_difference_p(t, sets):
	if (len(sets) == 1): return (t in sets[0])
	r = d_diff_queries.get((t, sets))
	if (r == None):
		head = sets[0]; tail = sets[1:]
		r = any(can_make_sum_p(e-t, tail) for e in head if e > t) or \
			any(can_make_difference_p(t+e, tail) for e in head)
		d_diff_queries[(t, sets)] = r
	return r

# Can we select exactly one member from each set s.t. the product of all selected members is t?
d_prod_queries = {}
def can_make_product_p(t, sets):
	if (len(sets) == 1): return (t in sets[0])
	r = d_prod_queries.get((t, sets))
	if (r == None):
		head = sets[0]; tail = sets[1:]
		r = any(can_make_product_p(t/e, tail) for e in head if not t%e)
		d_prod_queries[(t, sets)] = r
	return r

# Can we select exactly one member from each set s.t. the quotient of all selected members is t?
d_quot_queries = {}
def can_make_quotient_p(t, sets):
	if (len(sets) == 1): return (t in sets[0])
	r = d_quot_queries.get((t, sets))
	if (r == None):
		head = sets[0]; tail = sets[1:]
		r =	any(can_make_product_p(e/t, tail) for e in head if not e%t) or \
			any(can_make_quotient_p(t*e, tail) for e in head)
		d_quot_queries[(t, sets)] = r
	return r


def print_solution(s):
	if (not s):
		print s
		return
	rows	= list(set(k[0] for k in s.keys())); rows.sort()
	cols	= list(set(k[1] for k in s.keys())); cols.sort()
	max_len = max(map(len, s.values()))
	row_div = '\n' + '-+-'.join('-'*max_len for c in cols) + '\n'
	print row_div.join(' | '.join(string.center(s[r+c], max_len) for c in cols) for r in rows)


class Constraint(object):
	def __init__(self, value, *cells):
		self.cells	= set(cells)
		self.value	= int(value)
	def _test_component_sum(self, component, context):
		return (self.value>=component) and can_make_sum_p(self.value-component, context)
	def _test_component_diff(self, component, context):
		return ((component>self.value) and can_make_sum_p(component-self.value, context)) or \
			   can_make_difference_p(self.value+component, context)
	def _test_component_prod(self, component, context):
		return (not self.value%component) and can_make_product_p(self.value/component, context)
	def _test_component_div(self, component, context):
		return ((not component%self.value) and can_make_product_p(component/self.value, context)) or \
			   can_make_quotient_p(self.value*component, context)
	def _test_component(self, component, context):
		return True
	def apply(self, solution):
		l_sets = [(c, tuple(map(int, solution[c]))) for c in self.cells]; l_good = []
		for k,v in l_sets:
			others = tuple(ov for ok,ov in l_sets if ok != k)
			l_good.append((k, ''.join(str(e) for e in v if self._test_component(e, others))))
		return l_good

class Assert(Constraint):
	def apply(self, solution):
		v = str(self.value)
		return ((c, v) for c in self.cells)
	
class Sum(Constraint):
	_test_component = Constraint._test_component_sum;
	def __init__(self, value, *cells):
		Constraint.__init__(self, value, *cells)
		if (len(cells) < 2): raise Exception('Sum constraints must be applied to 2 or more cells')

class Diff(Constraint):
	_test_component = Constraint._test_component_diff;
	def __init__(self, value, *cells):
		Constraint.__init__(self, value, *cells)
		if (len(self.cells) < 2): raise Exception('Diff constraints must be applied to 2 or more cells')

class Prod(Constraint):
	_test_component = Constraint._test_component_prod;
	def __init__(self, value, *cells):
		Constraint.__init__(self, value, *cells)
		if (len(cells) < 2): raise Exception('Prod constraints must be applied to 2 or more cells')

class Div(Constraint):
	_test_component = Constraint._test_component_div;
	def __init__(self, value, *cells):
		Constraint.__init__(self, value, *cells)
		if (len(self.cells) < 2): raise Exception('Div constraints must be applied to 2 or more cells')

class Noop(Constraint):
	def __init__(self, value, *cells):
		Constraint.__init__(self, value, *cells)
		if (len(self.cells) < 2): raise Exception('Noop constraints must be applied to 2 or more cells')
	def _test_component(self, component, context):
		return self._test_component_sum(component, context)	or \
	               self._test_component_diff(component, context)	or \
		       self._test_component_prod(component, context)	or \
		       self._test_component_div(component, context)

class Set(Constraint):
	def _remove(self, l_good, cell, value):
		for p in l_good:
			if (p[0] == cell): continue
			if (value in p[1]):
				p[1] = p[1].replace(value, '')
				if (len(p[1]) == 1):
					self._remove(l_good, *p)
	def apply(self, solution):
		# For each cell:
		l_good = [[c, solution[c]] for c in self.cells]
		for c,v in l_good:
			# If a cell has only one possible value, remove that value from all other cells
			if (len(v) == 1): self._remove(l_good, c, v)
		return l_good


class Puzzle(object):
	lut = {'!':Assert, '+':Sum, '-':Diff, '*':Prod, '/':Div, '?':Noop}
	def __init__(self, fn):
		# Parse file
		lines = [l.split() for l in file(fn, 'rb').read().strip().split('\n')]
		if (lines[0][0] != '#'):
			raise Exception('Puzzle definitions must begin with a size ("#") line')
		self.size	= int(lines[0][1])
		self.cages	= [self.lut[l[0]](*l[1:]) for l in lines[1:]]


def solve(puzzle, exhaustive=False):
	# Derived from the problem size
	rows	= string.ascii_uppercase[:puzzle.size]
	cols	= string.digits[1:1+puzzle.size]
	sets	= [Set(0, *(r+c for c in cols)) for r in rows] + \
			  [Set(0, *(r+c for r in rows)) for c in cols]
	# Cell -> constraint mapping
	d_constraints = dict((r+c, set()) for r in rows for c in cols)
	for constraint in sets+puzzle.cages:
		for cell in constraint.cells:
			d_constraints[cell].add(constraint)
	# Helper: Given a partial solution, apply (potentially) unsatisfied constraints
	def constrain(solution, *constraints):
		queue = set(constraints)
		while (queue):
			constraint = queue.pop()
			for cell, values in constraint.apply(solution):
				if (not values):
					return False
				if (solution[cell] == values):
					continue
				solution[cell] = values
				queue.update(d_constraints[cell])
			queue.discard(constraint)
		return solution
	# Helper: Given a partial solution, force one of its cells to a given value
	def assign(solution, cell, value):
		solution[cell] = value
		return constrain(solution, *d_constraints[cell])
	# Helper: Recursively refine a solution with search and propogation
	def search(solution):
		# Check for trivial cases
		if ((not solution) or all(len(v)==1 for v in solution.values())):
			return solution
		# Find a most-constrained unsolved cell
		cell = min((len(v),k) for k,v in solution.items() if len(v)>1)[1]
		# Try solutions based upon exhaustive guesses of the cell's value
		return first(search(assign(solution.copy(), cell, h)) for h in solution[cell])
	# Helper: Recursively refine a solution with search and propogation
	def search_ex(solution):
		# Check for trivial cases
		if (not solution):
			return []
		if all(len(v)==1 for v in solution.values()):
			return [solution]
		# Find a most-constrained unsolved cell
		cell = min((len(v),k) for k,v in solution.items() if len(v)>1)[1]
		# Try solutions based upon exhaustive guesses of the cell's value
		rv = []
		for h in solution[cell]: rv.extend(search_ex(assign(solution.copy(), cell, h)))
		return rv
	# Solve
	d_sum_queries = {}
	d_diff_queries = {}
	d_prod_queries = {}
	d_quot_queries = {}
	symbols = string.digits[1:1+puzzle.size]
	if (exhaustive):
		fxn = search_ex
	else:
		fxn = search
	return fxn(constrain(dict((c,symbols) for c in d_constraints.keys()), *puzzle.cages))
