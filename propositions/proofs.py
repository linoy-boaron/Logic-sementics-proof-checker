# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/proofs.py

"""Proofs by deduction in propositional logic."""

from __future__ import annotations
from typing import AbstractSet, Iterable, FrozenSet, List, Mapping, Optional, \
    Set, Tuple, Union

from logic_utils import frozen

from propositions.syntax import *

SpecializationMap = Mapping[str, Formula]


@frozen
class InferenceRule:
    """An immutable inference rule in propositional logic, comprised by zero
    or more assumed propositional formulae, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Iterable[Formula], conclusion: Formula) -> \
            None:
        """Initialized an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return (isinstance(other, InferenceRule) and
                self.assumptions == other.assumptions and
                self.conclusion == other.conclusion)

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current inference
        rule.

        Returns:
            A set of all atomic propositions used in the assumptions and in the
            conclusion of the current inference rule.
        """
        # Task 4.1
        # remembering variables from the first task is a set, all we need is unions.
        ret_set = set()
        for assum in self.assumptions:  # Union for the variables in each assumption
            vars = assum.variables()
            ret_set = ret_set.union(vars)
        vars_conclusion = self.conclusion.variables()  # Union for the variables from the conclusion
        ret_set = ret_set.union(vars_conclusion)
        return ret_set

    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """
        for variable in specialization_map:
            assert is_variable(variable)
        # Task 4.4
        specialized_assumptions = [assump.substitute_variables(specialization_map) for assump in self.assumptions]
        specialized_conclusion = self.conclusion.substitute_variables(specialization_map)
        return InferenceRule(specialized_assumptions, specialized_conclusion)

    @staticmethod
    def merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps.

        Parameters:
            specialization_map1: first map to merge, or ``None``.
            specialization_map2: second map to merge, or ``None``.

        Returns:
            A single map containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)
        # Task 4.5a
        if specialization_map1 is None or specialization_map2 is None:
            return None
        specialization_map1_keys = specialization_map1.keys()
        specialization_map2_keys = specialization_map2.keys()
        if len(specialization_map2_keys) > 0:
            for key in specialization_map1_keys:
                val1 = specialization_map1[key]
                if key not in specialization_map2_keys:
                    continue
                val2 = specialization_map2[key]
                if val1 != val2:
                    return None
            # after the for loop we made sure we can merge the dictionaries
            return {**specialization_map1, **specialization_map2}  # This syntax is a union of dictionaries

        else:  # the case the first dict is empty we can just return the merge:
            return {**specialization_map1, **specialization_map2}  # This syntax is a union of dictionaries

    @staticmethod
    def formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        # Task 4.5b
        # we will recursively go down the general formula, and replace variables with a corresponding
        # formula in the specialization. if at any point the roots aren't identical we can return none
        # if the recursion succeeds we'll be left with maps which we will have to merge, if they ever return none
        # we're done.

        # base case
        if is_variable(general.root):
            return {str(general.root): specialization}

        # make sure the constants are the same, if so return an empty dict
        if is_constant(general.root):
            if specialization.root == general.root:
                return {}
            else:
                return None

        # Unary case:
        if is_unary(general.root):
            # make sure the roots are the same
            if specialization.root == general.root:
                return InferenceRule.formula_specialization_map(general.first, specialization.first)
            else:
                return None

        # Binary case:
        if is_binary(general.root):
            # make sure the roots are the same
            if specialization.root == general.root:
                # get the children maps and return their merger
                # merge_specialization makes sure we wont have variables mapped to different formulas.
                dict1_temp = InferenceRule.formula_specialization_map(general.first, specialization.first)
                dict2_temp = InferenceRule.formula_specialization_map(general.second, specialization.second)
                return InferenceRule.merge_specialization_maps(dict1_temp, dict2_temp)
            else:
                return None

    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        # Task 4.5c
        # Make sure the order of assumptions is the same
        if len(specialization.assumptions) != len(self.assumptions):
            return None
        special_map = {}
        # go over all the assumptions and make sure we can create maps for those pairs
        for assumption_1, assumption_2 in zip(self.assumptions, specialization.assumptions):
            # make sure all maps can be merged with other maps otherwise return None
            special_map = InferenceRule.merge_specialization_maps(special_map, InferenceRule.formula_specialization_map(assumption_1, assumption_2))
            if special_map is None:
                return None
        # after going over all assumptions, merge the conclusion's map
        special_map = InferenceRule.merge_specialization_maps(special_map, InferenceRule.formula_specialization_map(self.conclusion, specialization.conclusion))
        return special_map


    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None


@frozen
class Proof:
    """A frozen deductive proof, comprised of a statement in the form of an
    inference rule, a set of inference rules that may be used in the proof, and
    a proof in the form of a list of lines that prove the statement via these
    inference rules.

    Attributes:
        statement (`InferenceRule`): the statement of the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statment: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]

    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Iterable[Proof.Line]) -> None:
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement for the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula which
        is either justified as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule out
                of those allowed in the proof, a specialization of which
                concludes the formula, or ``None`` if the formula is justified
                as an assumption of the proof.
            assumptions
                (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): a tuple of zero
                or more indices of previous lines in the proof whose formulae
                are the respective assumptions of the specialization of the rule
                that concludes the formula, if the formula is not justified as
                an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Iterable[int]] = None) -> None:
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and indices of justifying previous lines.

            Parameters:
                formula: the formula to be justified by this line.
                rule: the inference rule out of those allowed in the proof, a
                    specialization of which concludes the formula, or ``None``
                    if the formula is to be justified as an assumption of the
                    proof.
                assumptions: an iterable over indices of previous lines in the
                    proof whose formulae are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current proof line.

            Returns:
                A string representation of the current proof line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                return str(self.formula) + ' Inference Rule ' + \
                       str(self.rule) + \
                       ((" on " + str(self.assumptions))
                        if len(self.assumptions) > 0 else '')

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None

    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof for ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += "Lines:\n"
        for i in range(len(self.lines)):
            r += ("%3d) " % i) + str(self.lines[i]) + '\n'
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulae justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: index of the line according to which to construct the
                inference rule.

        Returns:
            The constructed inference rule, with assumptions ordered in the
            order of their indices in the specified line, or ``None`` if the
            specified line is justified as an assumption.
        """
        assert line_number < len(self.lines)
        # Task 4.6a
        cur_line = self.lines[line_number]
        conclusion = cur_line.formula
        if cur_line.is_assumption():
            # Check if the line stands on its own
            return None
        else:
            # if not it is based on assumptions
            assumptions_tuple = cur_line.assumptions
            assumptions = [self.lines[line_num].formula for line_num in assumptions_tuple]

            ret_inference_rule =  InferenceRule(assumptions, conclusion)
            return ret_inference_rule

    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: index of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            then ``True`` if and only if all of the following hold:

            1. The rule specified for that line is one of the allowed inference
               rules in the current proof.
            2. Some specialization of the rule specified for that line has
               the formula justified by that line as its conclusion, and the
               formulae justified by the lines specified as the assumptions of
               that line (in the order of their indices in this line) as its
               assumptions.
        """
        assert line_number < len(self.lines)
        # Task 4.6b
        # check if the line is assumption:
        cur_line = self.lines[line_number]
        if cur_line.is_assumption():
            # check if this assumption is in self.assumptions
            if cur_line.formula in self.statement.assumptions:
                return True
            else:
                return False

        # otherwise check if inference rule is valid
        if cur_line.rule not in self.rules:
            return False

        # cannot use lines that come after the current line
        for assumption_line_num in cur_line.assumptions:
             if line_number <= assumption_line_num:
                 return False

        # now we check if our inference rule is a specialization of our line's inference rule
        line_inference_rule = self.rule_for_line(line_number)
        return line_inference_rule.is_specialization_of(cur_line.rule)


    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        # Task 4.6c
        # make sure all lines are valid
        for line_num in range(len(self.lines)):
            if not self.is_line_valid(line_num):
                return False

        # make sure conclusion of statement matches the formula of the last line
        if self.lines[-1].formula == self.statement.conclusion:
            return True
        else:
            return False


# Chapter 5 tasks

def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule into a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the conclusion of the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)
    # Task 5.1
    specialization_map = proof.statement.specialization_map(specialization)
    specialized_proof = proof.statement.specialize(specialization_map)
    # Create the substituted lines, make sure not to add assumptions unless the line is not an assumption
    specialized_lines = [Proof.Line(line.formula.substitute_variables(specialization_map), line.rule, line.assumptions if not line.is_assumption() else None) for line in proof.lines]
    return Proof(specialized_proof, proof.rules, specialized_lines)



def inline_proof_once(main_proof: Proof, line_number: int, lemma_proof: Proof) \
        -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line: index of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating line indices specified throughout the proof to maintain the
        validity of the proof. The set of allowed inference rules in the
        returned proof is the union of the rules allowed in the two given
        proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()
    # Task 5.2a

    # Lines are tuples of lines, work with __add__  function for tuples.
    lemma_proof = prove_specialization(lemma_proof, main_proof.rule_for_line(line_number))
    lines = main_proof.lines[0:line_number]
    origial_line = main_proof.lines[line_number]

    # From here the code must stick in the lines from lemma_proof we split it into the next cases:
    for line in lemma_proof.lines:
        # Case 1.1 check if line is statement, if so check if it is a statement in the proof, if so just copy
        if line.is_assumption():
            if line in main_proof.statement.assumptions:
                lines = lines.__add__(tuple([line]))
            # Case 1.2 line is a statement but not a statement in the main proof so we must justify the line
            # using previous lines!
            else:
                # We must find the line's on which this line is based on
                for i in origial_line.assumptions:
                    if main_proof.lines[i].formula == line.formula:
                        lines = lines.__add__(tuple([main_proof.lines[i]]))
                        break
        # Case 2 line is not an assumption!
        else:
            # We have added the lines iteratively, the only modification needed is to shift the tuple's numbers
            line_tuple = tuple([num + line_number for num in line.assumptions])
            new_line = Proof.Line(line.formula, line.rule, line_tuple)
            lines = lines.__add__(tuple([new_line]))

    # create union of the rules
    main_rules_reduction = main_proof.rules
    rules = main_rules_reduction.union(lemma_proof.rules)

    # check if the lemma wasn't the last line and shift their assumptions! (if not an assumption just add it!)
    if line_number < len(main_proof.lines):
        shifted_lines = []
        for line in main_proof.lines[line_number+1:]:
            if line.is_assumption():
                shifted_lines.append(line)
            else:
                shifted_tuple = tuple(x+len(lemma_proof.lines)-1 if x >= line_number else x for x in line.assumptions)
                shifted_lines.append(Proof.Line(line.formula, line.rule, shifted_tuple))
        lines = lines.__add__(tuple(shifted_lines))  # slice from lemma + 1
    return Proof(main_proof.statement, rules, lines)


def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specialization
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the rules
        allowed in the two given proofs but without the "lemma" rule proved by
        `lemma_proof`.
    """
    # Task 5.2b
    ret_proof = main_proof  # create copy of proof
    rule = lemma_proof.statement
    line_num = first_use_of_rule(ret_proof, rule)
    while line_num != -1:
        ret_proof = inline_proof_once(ret_proof, line_num, lemma_proof)
        line_num = first_use_of_rule(ret_proof, rule)
    # remove the rule from the ret_proof's rules
    new_rules = ret_proof.rules - frozenset([rule])
    ret_proof = Proof(ret_proof.statement, new_rules, ret_proof.lines)
    return ret_proof


    

def first_use_of_rule(proof, rule):
    """Returns the number of the first line in which the given proof uses the
    given rule. will return -1 if not found, func taken from test."""
    i=0
    for i in range(len(proof.lines)):
        if (not proof.lines[i].is_assumption()) and proof.lines[i].rule == rule:
            return i
    return -1