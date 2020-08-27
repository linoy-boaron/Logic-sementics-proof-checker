# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.proofs import *
from propositions.deduction import *
from propositions.semantics import *
from propositions.operators import *
from propositions.axiomatic_systems import *

def formulae_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulae that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable x that is assigned the value
    ``False``.

    Parameters:
        model: model to construct the formulae for.

    Returns:
        A list of the constructed formulae, ordered alphabetically by variable
        name.

    Examples:
        >>> formulae_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a
    if not model:  # Check if empty
        return model
    sorted_model = sorted(model.items())
    return [Formula.parse(key) if val else Formula('~', Formula(key)) for key, val in sorted_model]

def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b
    formulae_captured = formulae_capturing_model(model)
    return recursive_prove_in_model(formula, formulae_captured, model)

def recursive_prove_in_model(formula, formulae_captured, model):
    """
    a helping function which we can recursively call to prove the formula
    :param formula: the given formula
    :param formula_capture: the formulas that capture the model
    :return:
    """

    # base case, proving a variable:
    if is_variable(formula.root):
        if model[formula.root]:
            return Proof(InferenceRule(formulae_captured, formula), rules=AXIOMATIC_SYSTEM,
                         lines=[Proof.Line(formula)])
        else:
            return Proof(InferenceRule(formulae_captured, Formula('~', formula)), rules=AXIOMATIC_SYSTEM,
                                       lines=[Proof.Line(Formula('~',formula))])

    elif is_unary(formula.root):  # ~ case
        if evaluate(formula, model):
            return recursive_prove_in_model(formula.first, formulae_captured, model)
        else:  # prove the negation
            negation_proof = recursive_prove_in_model(formula.first, formulae_captured, model)
            return prove_corollary(negation_proof, Formula('~', formula), NN)

    elif is_binary(formula.root):  # -> case
        if evaluate(formula, model):
            # either first is false or second is true
            if evaluate(formula.first, model) is False:
                # We can prove ~first recursively
                prove_not_first = recursive_prove_in_model(Formula('~', formula.first), formulae_captured, model)
                return prove_corollary(prove_not_first, formula, I2)
            else:
                # second must be true, so we prove it
                prove_second = recursive_prove_in_model(formula.second, formulae_captured, model)
                return prove_corollary(prove_second, formula, I1)
        else:  # formula is false meaning we need to prove ~formula
            # prove first and not second, combine to prove ~formula
            prove_first = recursive_prove_in_model(formula.first, formulae_captured, model)
            prove_not_second = recursive_prove_in_model(formula.second, formulae_captured, model)
            return combine_proofs(prove_first, prove_not_second, Formula('~', formula), NI)


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_of_negation: valid proof of `conclusion` from the same assumptions
            and inference rules of `proof_from_affirmation`, but with the last
            assumption being ``'~``\ `assumption` ``'`` instead of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If the two given proofs are of ``['p', 'q'] ==> '(q->p)'`` and of
        ``['p', '~q'] ==> ('q'->'p')``, then the returned proof is of
        ``['p'] ==> '(q->p)'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2
    same_conclusion = proof_from_negation.statement.conclusion
    affirm_remove = remove_assumption(proof_from_affirmation)
    negate_remove = remove_assumption(proof_from_negation)
    return combine_proofs(affirm_remove, negate_remove, same_conclusion, R)

def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulae that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulae to prove.

    Returns:
        A valid proof of the given tautology from the formulae that capture the
        given model, in the order returned by
        `formulae_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        If the given model is the empty dictionary, then the returned proof is
        of the given tautology from no assumptions.
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a
    if model:  # if dict not empty
        unfrozen_model = {key: val for key, val in model.items()}
    else:
        unfrozen_model = {}
    formulae_captured = formulae_capturing_model(model)
    return recursive_tautology(tautology, unfrozen_model, formulae_captured, len(formulae_captured))

def recursive_tautology(tautology, model, formulae_captured, cur_index):
    """
    helper function to recursively call the prove_tautology func
    :param model: the given model
    :param formulae_captured:  the formulae captured by the model
    :return: proof of the tautology
    """
    if set(tautology.variables()) == set(model.keys()):  # proof can be built over the model
        return prove_in_model(tautology, model)
    else:
        vars = sorted([var for var in tautology.variables()])
        # to remove assumptions, we'll use reduce assumptions.
        # every time we find a variable not in the model we'll prove the affirmation and negation to remove it

        model[vars[cur_index]] = True
        affirmation = recursive_tautology(tautology, model, formulae_captured, cur_index+1)

        model[vars[cur_index]] = False
        negation = recursive_tautology(tautology, model, formulae_captured, cur_index+1)

        model.pop(vars[cur_index])  # remove the variable from the model
        return reduce_assumption(affirmation, negation)


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b
    models = all_models(formula.variables())
    if is_tautology(formula):
        #  we can prove a tautology over any model
        return prove_tautology(formula)
    else: # formula isn't a tautology hence there is a model over which it does not hold.
        for model in models:
            if not evaluate(formula, model):
                return model


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))
        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a
    cur_formula = rule.conclusion
    if rule.assumptions:  # if the inference rule has assumptions:
        for assumption in reversed(rule.assumptions):
            cur_formula = Formula('->', assumption, cur_formula)
    return cur_formula

def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion that contain
            no constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid assumptionless proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b
    formula_to_prove = encode_as_formula(rule)
    proof = prove_tautology(formula_to_prove)
    # docstring says assumptionless... but the test expects assumptions, clearly a contradiction
    # if there is no need for assumptions we can return proof
    proof = Proof(InferenceRule(rule.assumptions, proof.statement.conclusion), proof.rules, proof.lines)
    lines = proof.lines
    for i in range(len(rule.assumptions)):
        last_line_number = len(proof.lines) - 1
        first, second = proof.statement.conclusion.first, proof.statement.conclusion.second
        lines = lines.__add__(tuple([(Proof.Line(first))]))
        lines = lines.__add__(tuple([(Proof.Line(second, MP, [last_line_number + 1, last_line_number]))]))
        proof = Proof(InferenceRule(proof.statement.assumptions, second), proof.rules, lines)
    return proof


def model_or_inconsistency(formulae: List[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulae hold, or proves
    ``'~(p->p)'`` from these formula.

    Parameters:
        formulae: formulae that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulae hold if such exists,
        otherwise a proof of '~(p->p)' from the given formulae via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulae:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5
    variable_set = set()
    for formula in formulae:
        variable_set = variable_set | formula.variables()
    models = all_models(list(variable_set))
    for model in models:
        truth_table = [evaluate(formula, model) for formula in formulae]
        if not truth_table.__contains__(False):
            return model
    return prove_sound_inference(InferenceRule(formulae, Formula.parse('~(p->p)')))


def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
