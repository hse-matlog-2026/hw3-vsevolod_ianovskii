# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    if type(formula) == bool:
        return Formula.TRUE() if formula else Formula.FALSE()

    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('|', Formula('p'), Formula('~', Formula('p')))
        else:
            return Formula('&', Formula('p'), Formula('~', Formula('p')))

    if is_variable(formula.root):
        return formula

    if is_unary(formula.root):
        if formula.root == '~':
            return Formula('~', to_not_and_or(formula.first))

    if is_binary(formula.root):
        if formula.root in ['&', '|', '->', '+', '<->', '-&', '-|']:
            left = to_not_and_or(formula.first)
            right = to_not_and_or(formula.second)
            if formula.root == '&' or formula.root == '|':
                return Formula(formula.root, left, right)
            elif formula.root == '->':
                return Formula('|', Formula('~', left), right)
            elif formula.root == '+':
                return Formula('|',
                               Formula('&', left, Formula('~', right)),
                               Formula('&', Formula('~', left), right))
            elif formula.root == '<->':
                return Formula('&',
                               Formula('|', Formula('~', left), right),
                               Formula('|', left, Formula('~', right)))
            elif formula.root == '-&':
                return Formula('~', Formula('&', left, right))
            elif formula.root == '-|':
                return Formula('~', Formula('|', left, right))
    return formula

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    f1 = to_not_and_or(formula)
    def convert_or(expr):
        if is_variable(expr.root):
            return expr
        if is_unary(expr.root):
            return Formula('~', convert_or(expr.first))
        if is_binary(expr.root):
            left = convert_or(expr.first)
            right = convert_or(expr.second)
            if expr.root == '&':
                return Formula('&', left, right)
            if expr.root == '|':
                return Formula('~', Formula('&', Formula('~', left), Formula('~', right)))
        return expr
    return convert_or(f1)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    f1 = to_not_and(formula)
    def convert_to_nand(expr):
        if is_variable(expr.root):
            return expr
        if is_unary(expr.root):
            inner = convert_to_nand(expr.first)
            return Formula('-&', inner, inner)
        if is_binary(expr.root) and expr.root == '&':
            left = convert_to_nand(expr.first)
            right = convert_to_nand(expr.second)
            nand = Formula('-&', left, right)
            return Formula('-&', nand, nand)
        return expr
    return convert_to_nand(f1)

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    f1 = to_not_and_or(formula)
    def convert_to_implies_not(expr):
        if is_variable(expr.root):
            return expr
        if is_unary(expr.root):
            return Formula('~', convert_to_implies_not(expr.first))
        if is_binary(expr.root):
            left = convert_to_implies_not(expr.first)
            right = convert_to_implies_not(expr.second)
            if expr.root == '&':
                return Formula('~', Formula('->', left, Formula('~', right)))
            if expr.root == '|':
                return Formula('->', Formula('~', left), right)
        return expr
    if is_constant(f1.root):
        if f1.root == 'T':
            p = Formula('p')
            return Formula('->', p, p)
        else:
            p = Formula('p')
            return Formula('~', Formula('->', p, p))
    return convert_to_implies_not(f1)

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    f1 = to_implies_not(formula)
    def convert_to_implies_false(expr):
        if is_variable(expr.root):
            return expr
        if is_unary(expr.root):
            inner = convert_to_implies_false(expr.first)
            return Formula('->', inner, Formula('F'))
        if is_binary(expr.root) and expr.root == '->':
            left = convert_to_implies_false(expr.first)
            right = convert_to_implies_false(expr.second)
            return Formula('->', left, right)
        return expr
    if is_constant(f1.root):
        if f1.root == 'T':
            return Formula('->', Formula('F'), Formula('F'))
    return convert_to_implies_false(f1)
