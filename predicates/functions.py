# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/functions.py

"""Syntactic conversion of first-order formulas to not use functions and
equality."""
import copy
from itertools import filterfalse
from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *

def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]

def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]

def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Return:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    # Task 8.1
    new_relation_meaning = dict(model.relation_meanings)
    for func,val in zip(model.function_meanings.keys(), model.function_meanings.values()):
        for funKey, funVal in zip(val.keys(),val.values()):
            if new_relation_meaning.get(function_name_to_relation_name(func)) != None:
                new_relation_meaning.update({function_name_to_relation_name(func): new_relation_meaning.get(function_name_to_relation_name(func)).union({tuple(funVal) + funKey})})
            else:
                new_relation_meaning.update({function_name_to_relation_name(func): {tuple(funVal) + funKey}})

    return Model(model.universe,model.constant_meanings,new_relation_meaning,dict())




def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_mosdel`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings
    # Task 8.2
    functions = {}
    relMean = {}
    for k,v in zip(model.relation_meanings.keys(),model.relation_meanings.values()):
        relMean.update({k:v})
    for function in original_functions:
        funModel = model.relation_meanings.get(function_name_to_relation_name(function))
        if funModel is None:
            return None
        funRel = {}
        for val in funModel:
            if model.universe.__len__() * (val.__len__()-1) > funModel.__len__():
                return None
            if funRel.get(val[1:]) is not None and funRel.get(val[1:]) != val[0]:
                return None
            funRel.update({val[1:] : val[0]})
        functions.update({function: funRel})
        del relMean[function_name_to_relation_name(function)]
    return Model(model.universe, model.constant_meanings, relMean,functions)


def compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and that
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)
    # Task 8.3
    return compile_term_helper(term,[])

def compile_term_helper(term: Term, funcs: List[Formula]) -> List[Formula]:
    res = []
    args = []
    if is_variable(term.root) or is_constant(term.root):
        res.append(term)
    elif is_function(term.root):
        args.append(term)
        for arg in term.arguments:
            if is_function(arg.root):
                # args.append(arg)
                res.extend(compile_term_helper(arg, funcs))
        fun = args[-1]
        for z in funcs:
            ar = []
            for a in fun.arguments:
                if a == z.arguments[1]:
                    ar.append(z.arguments[0])
                else:
                    ar.append(a)
            fun = Term(fun.root, ar)

        var = next(fresh_variable_name_generator)
        res.append(Formula("=", [Term(var), fun]))
        funcs.append(Formula("=", [Term(var), args[-1]]))
    return res

def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, that contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function,arity in formula.functions()}.intersection(
                    {relation for relation,arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4

    # case of relation, return a function free formula using relations only.
    def function_free_relation():
        """
        helper function which receives a formula of a relation and
        returns it without functions.
        :return:
        """
        args = formula.arguments
        root = formula.root
        formula_by_order = []
        new_args = []

        for arg in args:
            # split in to two cases.

            # case 1: arg is a function:
            if is_function(arg.root):
                func_terms = compile_term_helper(arg, [])
                new_args.append(func_terms[-1].arguments[0])
                formula_by_order += (func_terms)
            # case 2: arg must be a simple term
            else:
                new_args.append(arg)

        # create the formula according to the root
        if is_relation(root) or is_equality(root):
            new_formula = Formula(root, new_args)

        formula_by_order = reversed(formula_by_order)
        for term in formula_by_order:
            z = term.arguments[0]
            function = term.arguments[1]
            new_formula = Formula('A', z.root, Formula('->', Formula(function_name_to_relation_name(function.root), list([z]) + list(function.arguments)), new_formula))
        return new_formula

    # base case, formula is a relation or equality, use our helper function
    if is_relation(formula.root) or is_equality(formula.root):
        return function_free_relation()

    # unary case
    if is_unary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first))
    # binary case
    if is_binary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first), replace_functions_with_relations_in_formula(formula.second))
    # lastly a quantifier case
    if is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_functions_with_relations_in_formula(formula.predicate))


def replace_functions_with_relations_in_formulas(formulas:
                                                 AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, that contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas holds in a model `model` if and only if the
           returned formulas holds in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas holds in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function,arity in formula.functions()}
                           for formula in formulas]).intersection(
                               set.union(*[{relation for relation,arity in
                                            formula.relations()} for
                                           formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5
    func_free_formulae = set([replace_functions_with_relations_in_formula(formula) for formula in formulas])
    functions = set()
    for formula in formulas:
        functions = functions.union(formula.functions())
    # now that we have our functions we need to add two things to func_free_formulae

    for func in functions:

        # a -> for every z = f(x) create formula Ax[Ex[F(z,x)]] and add it
        relation_name = function_name_to_relation_name(func[0])
        # Reminder func[0] == func name, func[1] == amount of vars
        psuedo_func_terms = [Term(next(fresh_variable_name_generator)) for i in range(func[1])]
        var_a = Term(next(fresh_variable_name_generator))
        formula_a = Formula('E', var_a.root, Formula(relation_name, [var_a] + psuedo_func_terms))

        # b -> for every two variables if x in relation to z1 and z2 are the same this implies z1 = z2
        var_b_1 = Term(next(fresh_variable_name_generator))
        var_b_2 = Term(next(fresh_variable_name_generator))
        relation_conjunction = Formula('&', Formula(relation_name, [var_b_1] + psuedo_func_terms), Formula(relation_name, [var_b_2] + psuedo_func_terms))
        formula_b = Formula('->', relation_conjunction, Formula('=', [var_b_1, var_b_2]))

        conjunction_a_b = Formula('&', formula_a, formula_b)
        for term in psuedo_func_terms:
            conjunction_a_b = Formula('A', term.root, conjunction_a_b)
        func_free_formulae.add(conjunction_a_b)
    return func_free_formulae


def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation,arity in formula.relations()}
    # Task 8.6
    # define a recursive function which will take out the eqaulity
    def replace_equality(formula: Formula) -> Formula:
        """
        helper recursive function for replace_equality_with_same
        removes all equality with a same relation
        :param formula:
        :return:
        """
        # base case '='
        if is_equality(formula.root):
            return Formula('SAME', [formula.arguments[0], formula.arguments[1]])
        if is_unary(formula.root):
            return Formula('~', replace_equality(formula.first))
        if is_binary(formula.root):
            return Formula(formula.root, replace_equality(formula.first), replace_equality(formula.second))
        if is_quantifier(formula.root):
            return Formula(formula.root, formula.variable, replace_equality(formula.predicate))
        if is_relation(formula.root):
            return formula

    equality_free_formulas = set([replace_equality(formula) for formula in formulas])

    # first let us add ‘SAME(τ ,σ)’ implies that in every formula where we have τ
    # we can replace it by σ.

    relation_demands = set()
    max_args = 0
    relation_names = set()
    relations = set()

    for formula in formulas:
        relations = relations.union(formula.relations())
    for relation in relations:
        # find maximum number of arguments for dummy variables
        if max_args < relation[1]:
            max_args = relation[1]
        relation_names.add(relation[0])
    temp_terms = [Term(next(fresh_variable_name_generator)) for i in range(2*max_args)]

    for tup in relations:
        relation_name = tup[0]
        relation_arg_val = tup[1]

        if relation_arg_val:  # if the relation is not empty.
            # ‘∀x1[∀x2[∀y1[∀y2[((SAME(x1,y1)&SAME(x2,y2))→(R(x1,x2)→R(y1,y2)))]]]]’

            # this is the left hand side, conjunction of SAME
            temp_subset = temp_terms[:2*relation_arg_val]
            formula_start = Formula('SAME', [temp_subset[0], temp_subset[relation_arg_val]])
            for x in range(1, relation_arg_val):
                formula_start = Formula('&', formula_start, Formula('SAME', [temp_subset[x], temp_subset[x+relation_arg_val]]))

            # right hand side conclusion
            conclusion = Formula('->', Formula(relation_name, temp_subset[:relation_arg_val]), Formula(relation_name, temp_subset[relation_arg_val:]))
            # Now we can add the quantifiers

            quantifier_start = Formula('->', formula_start, conclusion)
            for term in temp_terms:
                quantifier_start = Formula('A', term.root, quantifier_start)
            relation_demands.add(quantifier_start)
    equality_free_formulas.update(relation_demands)

    # we now need to add formulas that ensure the next 3 properties
    temp_term_1, temp_term_2, temp_term_3 = (Term(next(fresh_variable_name_generator)) for i in range(3))
    reflexivity = Formula('A', temp_term_1.root, Formula('SAME', [temp_term_1, temp_term_1]))

    symmetry = Formula('->', Formula('SAME', [temp_term_1, temp_term_2]), Formula('SAME', [temp_term_2, temp_term_1]))
    symmetry_full = Formula('A', temp_term_1.root, Formula('A', temp_term_2.root, symmetry))

    transitivity = Formula('&', Formula('SAME', [temp_term_1, temp_term_2]), Formula('SAME', [temp_term_2, temp_term_3]))
    transitivity_full = Formula('A', temp_term_1.root, Formula('A', temp_term_2.root, Formula('A', temp_term_3.root,
                                            Formula('->', transitivity, Formula('SAME', [temp_term_1, temp_term_3])))))

    equality_free_formulas.update({reflexivity, symmetry_full, transitivity_full})

    return equality_free_formulas


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Return:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7

    new_relations = {k : i for k, i in model.relation_meanings.items()}
    new_relations['SAME'] = {(var, var) for var in model.universe}
    new_model = Model(model.universe, model.constant_meanings, new_relations, model.function_meanings)
    return new_model


def get_equivalence_classes(model: Model):
    """
    helper function, receives a model and outputs the equivalence classes of that model
    :return:
    """

    universe_copy = set()
    for term in model.universe:
        universe_copy.add(term)
    equivalence_dict = dict()
    while universe_copy:  # we'll pop items out of the universe once it is empty we'll have our different classes
        potential_rep = universe_copy.pop()
        class_of_rep = []
        # find all elements that are the SAME as our potential rep
        for term in universe_copy:
            if (potential_rep, term) in model.relation_meanings['SAME']:
                class_of_rep.append(term)
        equivalence_dict[potential_rep] = class_of_rep + [potential_rep]
        for term in class_of_rep:
            universe_copy.remove(term)
    return equivalence_dict


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
    # Task 8.8

    # first we must find equivalence classes and then extract their representatives
    equivalence_classes = get_equivalence_classes(model)
    representatives = []
    for class_arr in equivalence_classes:
        representatives.append(class_arr[0])
    # we can now create our new model
    new_const_meaning = dict()
    new_relation_meaning = dict()
    # create new constant meanings
    for key, val in model.constant_meanings.items():
        for rep, rep_class in equivalence_classes.items():
            if val in rep_class:
                new_const_meaning[key] = rep
    # create new relation meanings
    for key, val in model.relation_meanings.items():
        if key != 'SAME':
            new_relation_meaning[key] = set(filter(lambda tup: all([term in representatives for term in tup]), val))
    return Model(representatives, new_const_meaning, new_relation_meaning, model.function_meanings)


