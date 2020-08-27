# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, List, Mapping

from propositions.syntax import *
from propositions.proofs import *
from itertools import product as iter_product
from tabulate import tabulate
from collections import defaultdict, OrderedDict

Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    """Checks if the given dictionary a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))

    # evaluating the truth value of a formula can be done recursively, base cases:
    cur_token = formula.root
    # Constants
    if is_constant(cur_token):
        return True if cur_token == 'T' else False

    # Variables
    if is_variable(formula.root):
        return model.get(cur_token)

    # Unary
    if is_unary(cur_token):
        return not (evaluate(formula.first, model))

    # Binary
    if is_binary(cur_token):
        if cur_token == '&':
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        elif cur_token == '|':
            return evaluate(formula.first, model) or evaluate(formula.second, model)
        elif cur_token == '->':
            # p->q is the same as (~p|q) logically speaking
            return not evaluate(formula.first, model) or evaluate(formula.second, model)
        elif cur_token == '+':  # checks for one truth and on false exclusively
            return (evaluate(formula.first, model) and not evaluate(formula.second, model)) or\
                   (not evaluate(formula.first, model) and evaluate(formula.second, model))
        elif cur_token == '-&':  # negate 'and'
            return not (evaluate(formula.first, model) and evaluate(formula.second, model))
        elif cur_token == '-|':  # negate 'or'
            return not (evaluate(formula.first, model) or evaluate(formula.second, model))
        elif cur_token == '<->':
            return (evaluate(formula.first, model) and evaluate(formula.second, model)) or \
                   (not evaluate(formula.first, model) and not evaluate(formula.second, model))



def all_models(variables: List[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: list of variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]
    """
    for v in variables:
        assert is_variable(v)
    if len(variables) == 0:
        return []  # return an empty list if the variables are empty.
    values = [False, True]
    ret_list = [{k: v for k, v in zip(variables, tup)} for tup in list(iter_product(values, repeat=len(variables)))]

    return ret_list


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.
    """
    if not any(models):  # if model is empty, formula must consist of constants only.
        return [evaluate(formula, dict())]
    ret_list = [evaluate(formula, model) for model in models]
    return ret_list



def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    to_print = '|'
    str_formula = str(formula)
    # print columns names first
    variables_truth = sorted(list(formula.variables()))
    for var in variables_truth:
        to_print += ' ' + var + ' |'
    to_print += ' ' + str_formula + ' |'
    to_print += '\n'
    to_print += '|'
    for var in variables_truth:
        to_print += '-'*(len(var) + 2) + '|'
    to_print += '-'*(len(str_formula) + 2) + '|'
    to_print += '\n'

    # printing truth values
    variables_table = all_models(sorted(formula.variables()))
    merged_table = merge_dicts(variables_table)
    key_list = merged_table.keys()
    t_values = list(truth_values(formula, variables_table))
    i = 0
    while(i < len(t_values)):
        for key in key_list:
            to_print += '| ' + merged_table[key][i] + ' ' * (len(key))
        if t_values[i]:
            cur_t_value = 'T'
        else:
            cur_t_value = 'F'
        to_print += '| ' + cur_t_value + ' ' * (len(str_formula)) + '|' + '\n'
        i += 1
    print(to_print, end='')


def merge_dicts(dictionaries):
    """
    helper function to merge dictionaries, also changes the bools to 'T' or 'F'
    :param dictionaries: array of dictionaries
    :return: merged dictionary with all bool values changed to 'T' or 'F' strings
    """
    dd = defaultdict(list)
    for d in dictionaries:
        for key, value in d.items():
            if value:
                dd[key].append('T')
            else:
                dd[key].append('F')
    return dd

def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """

    truth_vals = truth_values(formula, all_models(list(formula.variables())))
    for t_val in truth_vals:
        if not t_val:
            return False
    return True

def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """

    truth_vals = truth_values(formula, all_models(list(formula.variables())))
    for t_val in truth_vals:
        if t_val:
            return False
    return True

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    truth_vals = truth_values(formula, all_models(list(formula.variables())))
    for t_val in truth_vals:
        if t_val:
            return True
    return False

def synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single clause that
      evaluates to ``True`` in the given model, and to ``False`` in any other
      model over the same variables.

    Parameters:
        model: model in which the synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    variables = model.items()
    flag = True
    for variable in variables:
        var = variable[0]
        val = variable[1]
        if flag:  # for the first variable we create a singleton formula.
            if val:
                return_formula = Formula(var)
            else:
                return_formula = Formula('~', Formula(var))
            flag = False
            continue
        if val:
            return_formula = Formula('&', Formula(var), return_formula)
        else:
            return_formula = Formula('&', Formula('~', Formula(var)), return_formula)
    return return_formula

def synthesize(variables: List[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables, from
    the given specification of which value the formula should have on each
    possible model over these variables.

    Parameters:
        variables: the set of variables for the synthesize formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    models = all_models(variables)
    assert len(models) == len(values)

    flag = True
    if True not in values:
        return create_contradiction_dnf(variables)
    for model, value in zip(models, values):
        if value:
            clause = synthesize_for_model(model)
            if flag:
                return_formula = clause
                flag = False
            else:
                return_formula = Formula('|', clause, return_formula)
    return return_formula


def create_contradiction_dnf(variables: List[str]) -> Formula:
    """
    Helping function for Synthesize, if all truth values are false, we must create a contradiction clause
    :param variables: the variables
    :return: a contradiction clause, by choosing or between &s of all variables and their negation
    this will clearly be a contradiction as it is unsatisfiable. (each & clause is unsatisfiable)
    """

    flag = True
    for var in variables:
        if flag:
            ret_val = Formula('&', Formula(var), Formula('~', Formula(var)))
            flag = False
        else:
            ret_val = Formula('|', Formula('&', Formula(var), Formula('~', Formula(var))), ret_val)
    return ret_val

# Tasks for Chapter 4

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.
    """
    assert is_model(model)
    # Task 4.2
    if [evaluate(assumption, model) for assumption in rule.assumptions] == [True for i in range(len(rule.assumptions))]:
        if not evaluate(rule.conclusion, model):
            return False
        else:
            return True
    else:
        return True

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
    models = all_models(rule.variables())
    for model in models:
        if not evaluate_inference(rule, model):
            return False
    return True
