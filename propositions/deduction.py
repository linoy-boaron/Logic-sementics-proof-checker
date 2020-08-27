# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in propositional logic."""
import copy

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` into a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
    lines = tuple()
    lines_len = len(antecedent_proof.lines)
    # Add the lines from the antecedent proof
    if antecedent_proof.lines:
        lines = lines.__add__(antecedent_proof.lines)
    # Add the line antecedent_conclusion -> consequent based on the conditional rule
    lines = lines.__add__(tuple([Proof.Line(Formula('->', antecedent_proof.statement.conclusion, consequent),
                                            rule=conditional, assumptions=[])]))
    # Add the line consequent as a conclusion of MP based on the conclusion of antecedent and the last line
    lines = lines.__add__(tuple([Proof.Line(consequent, MP, [lines_len-1, lines_len])]))
    new_statement = InferenceRule(antecedent_proof.statement.assumptions, consequent)
    return Proof(new_statement, frozenset([conditional, MP]) | antecedent_proof.rules, lines)

def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulae `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``('``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b
    len_proof_one = len(antecedent1_proof.lines)
    len_proof_combined = len_proof_one + len(antecedent2_proof.lines)
    new_statement = InferenceRule(antecedent1_proof.statement.assumptions, conclusion=consequent)
    lines = tuple()
    if antecedent1_proof.lines:
        lines = lines.__add__(antecedent1_proof.lines)
    if antecedent2_proof.lines:
        # all this line does: if there are lines in the proof,
        # for each line adjust the index if the line has assumptions
        lines = lines.__add__(tuple([Proof.Line(line.formula, line.rule if not line.is_assumption() else None, None if line.is_assumption() else tuple(x + len_proof_one for x in line.assumptions)) for line in antecedent2_proof.lines]))
    #  add lines in following order: prove full double conditional
    lines = lines.__add__(tuple([Proof.Line(Formula.parse('(' + str(antecedent1_proof.statement.conclusion) + '->' +
                                                          '(' + str(antecedent2_proof.statement.conclusion) + '->' + str(consequent) + ')' + ')'),
                                            rule=double_conditional, assumptions=[])]))
    # Prove inner conditional using MP
    lines = lines.__add__(tuple([Proof.Line(Formula.parse('(' + str(antecedent2_proof.statement.conclusion) +
                                                          '->' + str(consequent) + ')'),
                                            rule=MP, assumptions=[len_proof_one-1, len_proof_combined])]))
    # Prove conclusion using MP on the inner condition and outer condition
    lines = lines.__add__(tuple([Proof.Line(consequent, MP, [len_proof_combined-1, len_proof_combined+1])]))
    new_rules = antecedent1_proof.rules | {MP, double_conditional}
    return Proof(new_statement, new_rules, lines)

def remove_assumption(proof: Proof) -> Proof:
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4

    # Create the new set of rules
    new_rules = proof.rules | {MP, I0, I1, D}

    # Create new statement, where the last assumption is dropped and instead the conclusion is assump -> conclusion
    phi = proof.statement.assumptions[-1]
    new_statement_assumptions = (list(proof.statement.assumptions))
    new_statement_assumptions.pop()
    new_statement_assumptions = tuple(new_statement_assumptions)
    new_statement = InferenceRule(new_statement_assumptions, Formula('->', phi, proof.statement.conclusion))

    # Iterate over the lines and create a new array of lines according to the 4 possible lines.
    counter = 0  # count any extra lines we add
    before_and_after = {line_number: line_number for line_number in range(len(proof.lines))}  # mapping of original lines and where they are now
    new_lines = []

    for line_num, line in zip(range(len(proof.lines)), proof.lines):

        # Case 1:
        if line.formula == phi:
            new_lines.append(Proof.Line(Formula('->', phi, phi), rule=I0, assumptions=[]))

        # Case 2 and 4: line is an assumption that isn't last_assumption, deduce from I1 and MP
        elif line.is_assumption() or line.rule != MP:
            # We will append the new line but also add a proof and show that theta
            new_lines.append(line)
            # Infer (etha -> (phi -> etha) according to I1
            new_lines.append(Proof.Line(Formula('->', line.formula, Formula('->', phi, line.formula)), I1, []))
            counter += 1

            # Infer from the two previous lines using MP that phi -> etha
            new_lines.append(Proof.Line(Formula('->', phi, line.formula), MP, [line_num+counter-1, line_num+counter]))
            counter += 1

            # update location of the line
            before_and_after = {key: (val+2 if key >= line_num else val) for key, val in before_and_after.items()}

        # Case 3: line is inferred, it must have a rule, if it is MP, Use D and MP and use them to infer this etha
        elif line.rule == MP:
            # this line uses assumptions, get them from the original proof.
            etha1, etha2 = (proof.lines[i].formula for i in line.assumptions)

            left_side_D  = Formula('->', phi, Formula('->', etha1, line.formula))
            phi_to_etha1 = Formula('->', phi, etha1)
            phi_to_line = Formula('->', phi, line.formula)
            new_lines.append(Proof.Line(Formula('->', left_side_D, Formula('->', phi_to_etha1, phi_to_line)), D, []))

            new_lines.append(Proof.Line(Formula('->', phi_to_etha1, phi_to_line), MP, [before_and_after[line.assumptions[1]], line_num + counter]))
            counter += 1

            new_lines.append(Proof.Line(phi_to_line, MP, [before_and_after[line.assumptions[0]], line_num + counter]))
            counter += 1

            before_and_after = {key: (val+2 if key >= line_num else val) for key, val in before_and_after.items()}
    return Proof(new_statement, new_rules, new_lines)


def proof_from_inconsistency(proof_of_affirmation: Proof,
                             proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6
    return combine_proofs(proof_of_negation, proof_of_affirmation, conclusion, I2)

def prove_by_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, into a proof of `formula` from
    the same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    # The idea here is to build the proof to the axiom p->p, then
    to_prove_formula = proof.statement.assumptions[-1].first
    p_to_p = (Formula.parse('(p->p)'))

    new_statement = InferenceRule(proof.statement.assumptions[:-1], p_to_p)
    new_lines = []
    new_lines.append(Proof.Line(p_to_p, I0, []))

    prove_p_to_p = Proof(new_statement, proof.rules | {MP, I0, I1, D, N}, new_lines)

    # Now we can take our contradiction proof ~(p->p) with our new rules and remove the assumption we want to prove
    contradiction_proof = Proof(proof.statement, proof.rules | {MP, I0, I1, D, N}, proof.lines)
    contradiction_proof = remove_assumption(contradiction_proof)
    # This now leaves us with a proof by contradiction similar to 5.6
    return combine_proofs(contradiction_proof, prove_p_to_p, to_prove_formula, N)
