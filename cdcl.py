import sys
import random
from pprint import pprint
from dataclasses import dataclass
from typing import List, Set, Tuple, Optional, Iterator


# frozen to be hashable
@dataclass(frozen=True)
class Literal:

    variable: int
    negation: bool

    def __repr__(self):
        if self.negation:
            return '¬' + str(self.variable)
        else:
            return str(self.variable)

    def neg(self) -> 'Literal':
        """
        Return the negation of this literal.
        """
        return Literal(self.variable, not self.negation)


@dataclass
class Clause:
    literals: List[Literal]

    def __repr__(self):
        return '∨'.join(map(str, self.literals))

    def __iter__(self) -> Iterator[Literal]:
        return iter(self.literals)

    def __len__(self):
        return len(self.literals)


@dataclass
class Formula:
    clauses: List[Clause]
    __variables: Set[int]

    def __init__(self, clauses: List[Clause]):
        """
        Remove duplicate literals in clauses.
        """
        self.clauses = []
        self.__variables = set()
        for clause in clauses:
            self.clauses.append(Clause(list(set(clause))))
            for lit in clause:
                var = lit.variable
                self.__variables.add(var)

    def variables(self) -> Set[int]:
        """
        Return the set of variables contained in this formula.
        """
        return self.__variables

    def __repr__(self):
        return ' ∧ '.join(f'({clause})' for clause in self.clauses)

    def __iter__(self) -> Iterator[Clause]:
        return iter(self.clauses)

    def __len__(self):
        return len(self.clauses)


@dataclass
class Assignment:
    value: bool
    antecedent: Optional[Clause]
    dl: int  # decision level


class Assignments(dict):
    """
    The assignments, also stores the current decision level.
    """
    def __init__(self):
        super().__init__()

        # the decision level
        self.dl = 0

    def value(self, literal: Literal) -> bool:
        """
        Return the value of the literal with respect the current assignments.
        """
        if literal.negation:
            return not self[literal.variable].value
        else:
            return self[literal.variable].value

    def assign(self, variable: int, value: bool, antecedent: Optional[Clause]):
        self[variable] = Assignment(value, antecedent, self.dl)

    def unassign(self, variable: int):
        self.pop(variable)

    def satisfy(self, formula: Formula) -> bool:
        """
        Check whether the assignments actually satisfies the formula. 
        """
        for clause in formula:
            if True not in [self.value(lit) for lit in clause]:
                return False

        return True




def cdcl_solve(formula: Formula) -> Optional[Assignments]:
    """
    Solve the CNF formula.

    If SAT, return the assignments.
    If UNSAT, return None.
    """
    assignments = Assignments()
    
    # First, do unit propagation to assign the initial unit clauses 
    reason, clause = unit_propagation(formula, assignments)
    if reason == 'conflict':
        return None

    while not all_variables_assigned(formula, assignments):
        var, val = pick_branching_variable(formula, assignments)
        assignments.dl += 1
        assignments.assign(var, val, antecedent=None)
        while True:
            reason, clause = unit_propagation(formula, assignments)
            if reason != 'conflict':
                # no conflict after unit propagation, we back
                # to the decision (guessing) step
                break
                
            b, learnt_clause = conflict_analysis(clause, assignments)
            if b < 0:
                return None
            
            add_learnt_clause(formula, learnt_clause)
            backtrack(assignments, b)
            assignments.dl = b

            # The learnt clause must be a unit clause, so the
            # next step must again be unit progagation

    return assignments


def add_learnt_clause(formula: Formula, clause: Clause):
    formula.clauses.append(clause)


def all_variables_assigned(formula: Formula, assignments: Assignments) -> bool:
    return len(formula.variables()) == len(assignments)


def pick_branching_variable(formula: Formula, assignments: Assignments) -> Tuple[int, bool]:
    unassigned_vars = [var for var in formula.variables() if var not in assignments]
    var = random.choice(unassigned_vars)
    val = random.choice([True, False])
    return (var, val)


def backtrack(assignments: Assignments, b: int):
    to_remove = []
    for var, assignment in assignments.items():
        if assignment.dl > b:
            to_remove.append(var)

    for var in to_remove:
        assignments.unassign(var)


def clause_status(clause: Clause, assignments: Assignments) -> str:
    """
    Return the status of the clause with respect to the assignments.

    There are 4 possible status of a clause:
      1. Unit - All but one literal are assigned False
      2. Unsatisfied - All literals are assigned False
      3. Satisfied - All literals are assigned True
      4. Unresolved - Neither unit, satisfied nor unsatisfied
    """
    values = []
    for literal in clause:
        if literal.variable not in assignments:
            values.append(None)
        else:
            values.append(assignments.value(literal))

    if True in values:
        return 'satisfied'
    elif values.count(False) == len(values):
        return 'unsatisfied'
    elif values.count(False) == len(values) - 1:
        return 'unit'
    else:
        return 'unresolved'


def unit_propagation(formula: Formula, assignments: Assignments) -> Tuple[str, Optional[Clause]]:
    # finish is set to True if no unit and conflict clause found in one iteration
    finish = False
    while not finish:
        finish = True
        for clause in formula:
            status = clause_status(clause, assignments)
            if status == 'unresolved' or status == 'satisfied':
                continue
            elif status == 'unit':
                # select the literal to propagate
                literal = next(literal for literal in clause if literal.variable not in assignments)
                var = literal.variable
                val = not literal.negation

                # assign the variable according to unit rule
                assignments.assign(var, val, antecedent=clause)
                finish = False
            else:
                # conflict
                return ('conflict', clause)

    return ('unresolved', None)


def resolve(a: Clause, b: Clause, x: int) -> Clause:
    """
    The resolution operation
    """
    result = set(a.literals + b.literals) - {Literal(x, True), Literal(x, False)}
    result = list(result)
    return Clause(result)


def conflict_analysis(clause: Clause, assignments: Assignments) -> Tuple[int, Clause]:
    if assignments.dl == 0:
        return (-1, None)
 
    # literals with current decision level
    literals = [literal for literal in clause if assignments[literal.variable].dl == assignments.dl]
    while len(literals) != 1:
        # implied literals
        literals = filter(lambda lit: assignments[lit.variable].antecedent != None, literals)

        # select any literal that meets the criterion
        literal = next(literals)
        antecedent = assignments[literal.variable].antecedent
        clause = resolve(clause, antecedent, literal.variable)

        # literals with current decision level
        literals = [literal for literal in clause if assignments[literal.variable].dl == assignments.dl]

    # out of the loop, `clause` is now the new learnt clause
    # compute the backtrack level b (second largest decision level)
    decision_levels = sorted(set(assignments[literal.variable].dl for literal in clause))
    if len(decision_levels) <= 1:
        return 0, clause
    else:
        return decision_levels[-2], clause


def parse_dimacs_cnf(content: str) -> Formula:
    """
    parse the DIMACS cnf file format into corresponding Formula.
    """
    clauses = [Clause([])]
    for line in content.splitlines():
        tokens = line.split()
        if len(tokens) != 0 and tokens[0] not in ("p", "c"):
            for tok in tokens:
                lit = int(tok)
                if lit == 0:
                    clauses.append(Clause([]))
                else:
                    var = abs(lit)
                    neg = lit < 0
                    clauses[-1].literals.append(Literal(var, neg))

    if len(clauses[-1]) == 0:
        clauses.pop()

    return Formula(clauses)


if __name__ == '__main__':
    # you might comment it to get inconsistent execution time
    random.seed(5201314)

    if len(sys.argv) != 2:
        print('Provide one DIMACS cnf filename as argument.')
        sys.exit(1)
        
    dimacs_cnf = open(sys.argv[1]).read()
    formula = parse_dimacs_cnf(dimacs_cnf)
    result = cdcl_solve(formula)
    if result:
        assert result.satisfy(formula)
        print('Formula is SAT with assignments:')
        assignments = {var: assignment.value for var, assignment in result.items()}
        pprint(assignments)
    else:
        print('Formula is UNSAT.')
