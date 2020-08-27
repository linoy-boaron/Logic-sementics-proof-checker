# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulae to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    substitute_dict = {'->': Formula.parse('(~p|q)'), '+': Formula.parse('((~p&q)|(p&~q))'), '<->':
            Formula.parse('((p&q)|(~p&~q))'), '-&': Formula.parse('~(p&q)'), '-|': Formula.parse('~(p|q)'),
                       'F': Formula.parse('(p&~p)'), 'T': Formula.parse('(p|~p)')}
    return formula.substitute_operators(substitute_dict)

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    #  To create this dict, I took the dict from not_and_or and used De Morgans Law to get rid of the or operations
    #  Remember ~(p|q) = (~p&~q)
    substitute_dict = {'|': Formula.parse('~(~p&~q)'), '->': Formula.parse('~(p&~q)'), '+': Formula.parse('~(~(~p&q)&~(p&~q))'), '<->':
        Formula.parse('~(~(p&q)&~(~p&~q))'), '-&': Formula.parse('~(p&q)'), '-|': Formula.parse('(~p&~q)'),
                       'F': Formula.parse('(p&~p)'), 'T': Formula.parse('~(~p&p)')}
    return formula.substitute_operators(substitute_dict)

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # In this attempt use a reduction, first create formula from not_and_or and then use this dict
    # which has Nand implementations of not and or to create a new formula
    # NOT(A) = A NAND A
    # A AND B = (A NAND B) NAND (A NAND B)
    # A OR B = (A NAND A) NAND (B NAND B)
    substitute_dict = {'~': Formula.parse('(p-&p)'), '&': Formula.parse('((p-&q)-&(p-&q))'), '|': Formula.parse('((p-&p)-&(q-&q))')}
    and_or_not_formula = to_not_and_or(formula)
    return and_or_not_formula.substitute_operators(substitute_dict)

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # create a reduction yet again, create & and | operations, run through not_and_or
    # remember (p->q) = (~p|q) and work from there
    and_or_not_formula = to_not_and_or(formula)
    substitute_dict = {'&': Formula.parse('~(p->~q)'), '|': Formula.parse('(~p->q)')}
    return and_or_not_formula.substitute_operators(substitute_dict)

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Notice for any p, p->F is the same as ~p, once we have that we can use a reduction from implies not
    substitute_dict = {'~': Formula.parse('(p->F)')}
    and_or_not_formula = to_not_and_or(formula)
    implies_false_formula = to_implies_not(and_or_not_formula)
    return implies_false_formula.substitute_operators(substitute_dict)
