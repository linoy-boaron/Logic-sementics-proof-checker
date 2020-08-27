# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/syntax.py



"""Syntactic handling of propositional formulae."""

from __future__ import annotations
from typing import Mapping, Optional, Set, Tuple, Union
import re
from collections import OrderedDict

from logic_utils import frozen

###################### Macros #########################

PARSE_ERR_MESSAGE_EMPTY_STR = "Parse failed, can't parse empty string"
PARSE_ERR_ILLEGAL_CHAR = "Parse failed, illegal character used."
PARSE_ERR_MISSING_BRACKET = "Missing right side ) bracket"

def is_variable(s: str) -> bool:
    """Checks if the given string is an atomic proposition.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())

def is_constant(s: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return s == 'T' or s == 'F'

def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s == '~'

def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return s == '&' or s == '|' or s == '->' or s == '+' or s == '<->' or s == '-&' or s == '-|'
    # For Chapter 3:
    # return s in {'&', '|',  '->', '+', '<->', '-&', '-|'}


def get_variable(s: str) -> Tuple[Union[Formula, None], str]:
    """
    Helper function for parse, Checks a string and gets the variable from it
    :param s: current string
    :return: tuple of formula of the string and the suffix of the rest without the variable
    """
    # check and see if there is a number after the variable name
    cur_token = s[0]
    i = 1
    cur_variable_num = ''
    while(i < len(s)):
        if s[i].isdigit():
            cur_variable_num += s[i]
            i += 1
        else:
            break

    # either adds the number to the token, or if it didnt exist, adds an empty string
    cur_token += cur_variable_num
    return Formula(cur_token), s[len(cur_token):]

def get_binary_formula(s: str) -> Tuple[Union[Formula, None], str]:
    """
    Helper function for parse, Checks a string that begins with '(' and returns a the binary formula prefix
    derived from s.
    :param s: the current string
    :return: tuple of a binary formula and the remaining suffix
    """
    cur_formula, cur_suffix = Formula.parse_prefix(s[1:])
    if len(cur_suffix) >= 2:  # after a binary operator there must be at least two characters in the suffix
        if is_binary(cur_suffix[0]):  # &, |, + cases
            right_formula, right_suffix = Formula.parse_prefix(cur_suffix[1:])
            # check for ')'
            if right_suffix == '' or right_suffix[0] != ')':
                return None, PARSE_ERR_MISSING_BRACKET

            return Formula(cur_suffix[0], cur_formula, right_formula), right_suffix[1:]
        elif is_binary(cur_suffix[0:2]):  # ->, -&, -| case
            right_formula, right_suffix = Formula.parse_prefix(cur_suffix[2:])
            # check for ')'
            if right_suffix == '' or right_suffix[0] != ')':
                return None, PARSE_ERR_MISSING_BRACKET
            return Formula(cur_suffix[0:2], cur_formula, right_formula), right_suffix[1:]

        elif len(cur_suffix) >= 3:
            if is_binary(cur_suffix[0:3]):  # the <-> case
                right_formula, right_suffix = Formula.parse_prefix(cur_suffix[3:])
                # check for ')'
                if right_suffix == '' or right_suffix[0] != ')':
                    return None, PARSE_ERR_MISSING_BRACKET
                return Formula(cur_suffix[0:3], cur_formula, right_formula), right_suffix[1:]


    return None, PARSE_ERR_ILLEGAL_CHAR

@frozen
class Formula:
    """An immutable propositional formula in tree representation.

    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root) and type(first) is Formula and \
                   type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            does not equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.


        Returns:
            The standard string representation of the current formula.
        """
        # check recursively
        # base case:
        ret = ''
        if is_constant(self.root) or is_variable(self.root):
            ret += self.root
            return ret
        elif is_unary(self.root):
            if self.first is not None:  # make sure no mistakes were made in init
                ret += self.root
                ret += self.first.__repr__()  # recursively call repr on the statement
                return ret
        elif is_binary(self.root):
            if self.first is not None and self.second is not None:  # make sure no mistakes were made in init
                ret += '('
                ret += self.first.__repr__()
                ret += self.root
                ret += self.second.__repr__()
                ret += ')'
                return ret




    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current formula.

        Returns:
            A set of all atomic propositions used in the current formula.
        """
        # defined recursively
        ret = set()
        # base cases
        if is_constant(self.root):
            return set()
        if is_variable(self.root):
            ret.update([self.root])
            return ret
        else:
            if is_unary(self.root):
                ret.update(self.first.variables())
                return ret
            if is_binary(self.root):
                ret.update(self.first.variables())
                ret.update(self.second.variables())
                return ret




    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # defined recursively
        ret = set()
        # base cases
        if is_constant(self.root):
            ret.update([self.root])
            return ret
        if is_variable(self.root):
            return ret
        else:
            if is_unary(self.root):
                ret.update(self.root)
                ret.update(self.first.operators())
                return ret
            if is_binary(self.root):
                ret.add(self.root)
                ret.update(self.first.operators())
                ret.update(self.second.operators())
                return ret
        
    @staticmethod
    def parse_prefix(s: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the first token of the string is a variable name (e.g.,
            ``'x12'``), then the parsed prefix will be that entire variable name
            (and not just a part of it, such as ``'x1'``). If no prefix of the
            given string is a valid standard string representation of a formula
            then returned pair should be of ``None`` and an error message, where
            the error message is a string with some human-readable content.
        """
        # get first letter, decide next move accordingly. done recursively
        # if string is empty return empty formula and string
        if s == '':
            return None, PARSE_ERR_MESSAGE_EMPTY_STR
        cur_token = s[0]
        # base cases:
        # 1. variable reached
        if 'p' <= cur_token <= 'z':
            return get_variable(s)
        # 2. T or F reached
        elif is_constant(cur_token):
            return Formula(cur_token), s[len(cur_token):]
        # (, ), binary operators and unary operators all require a recursive call.
        # unary call:
        elif is_unary(cur_token):
            cur_formula, cur_suffix = Formula.parse_prefix(s[1:])
            if cur_formula is None:
                return None, PARSE_ERR_ILLEGAL_CHAR
            else:
                return Formula(cur_token, cur_formula), s[len(str(cur_formula)) + len(cur_token):]
        # binary call: will start with '(' and with two legal formulae and a binary operator in the middle
        # ends with ')'
        elif cur_token == '(':
            return get_binary_formula(s)
        # reaching here means cur is illegal:
        return None, PARSE_ERR_ILLEGAL_CHAR





    @staticmethod
    def is_formula(s: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            s: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # We remember from the Lemma: Prefix-Free Property of Formulae. if the formula is a legal formula,
        # the only prefix that is a legal formula is the formula itself (the formula is its own substring)

        return str(Formula.parse_prefix(s)[0]) == s
        
    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(s)
        return Formula.parse_prefix(s)[0]

# Optional tasks for Chapter 1

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(s: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

# Tasks for Chapter 3

    def substitute_variables(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((p->p)|z)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)')})
            (((q&r)->(q&r))|z)
        """
        #  Edited for task 4, check if the original dictionary is empty
        if not substitution_map:
            return self
        for variable in substitution_map:
            assert is_variable(variable)
        ret_string = str(self)

        rep = dict((re.escape(k), str(v)) for k, v in (substitution_map.items()))

        # take out "tricky" variables that don't exist from the rep dictionary.
        for var in substitution_map:
            if var not in self.variables():
                rep.pop(var)

        if not rep:  # check if the dictionary is empty
            return self

        # the reason I sort the keys is to avoid a bug with substrings.
        # for example if we replace {v2: p, v22: r} if the dictionary is not an ordered dict
        # the substring may be replaced first in the v22 occurrence.

        # this code replaces strings using the created regex in one pass, replacements are done in the order
        # of the keys. substrings shouldnt affect this.

        # Fix made in targil 4, added boundaries to keys, which won't allow any substring confusion
        with_boundaries = map(lambda x: "\\b" + x + "\\b", rep.keys())
        pattern = re.compile("|".join(sorted(with_boundaries, key=len, reverse=True)))
        ret_string = pattern.sub(lambda m: rep[re.escape(m.group(0))], ret_string)
        return Formula.parse(ret_string)

    def substitute_operators(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or \
                   is_constant(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # return recursively changing the operators
        cur_operator = self.root

        # base case: root is empty
        if is_variable(cur_operator):
            return Formula(cur_operator)

        # if its a constant
        if is_constant(cur_operator):
            if cur_operator in substitution_map:
                return substitution_map[cur_operator]
            else:
                return Formula(cur_operator)

        # if it is a unary operator:
        if is_unary(cur_operator):
            replace_child = self.first.substitute_operators(substitution_map)
            ret_formula = Formula(cur_operator, replace_child)
            if cur_operator in substitution_map:
                return substitution_map[cur_operator].substitute_variables({'p': ret_formula.first})
            else:
                return ret_formula

        if is_binary(cur_operator):
            left_child = self.first.substitute_operators(substitution_map)
            right_child = self.second.substitute_operators(substitution_map)
            ret_formula = Formula(cur_operator, left_child, right_child)
            if cur_operator in substitution_map:
                return substitution_map[cur_operator].substitute_variables({'p': ret_formula.first, 'q': ret_formula.second})
            else:
                return ret_formula





