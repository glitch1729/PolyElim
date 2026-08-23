# PolyElim

Polynomial system solving via elimination in Macaulay2.

## Status

**Work in progress / research prototype**

This project is an implementation related to the Macaulay2 project:

> Solving systems of polynomial equations via elimination

The goal is to develop a Macaulay2 package for solving zero-dimensional
systems of polynomial equations using elimination methods.

## Current implementation

PolyElim currently includes:

- Gröbner-basis computation
- elimination-based triangular solving
- numerical back-substitution
- verification of numerical solutions
- duplicate solution removal
- recursive coefficient splitting
- ideal saturation for the nonvanishing coefficient branch
- configurable numerical tolerance
- configurable splitting depth

## Basic example

```m2
load "PolyElim.m2"

R = QQ[x,y,MonomialOrder => Lex];

I = ideal(
    y^2 - 1,
    x^2 - y
);

eliminationSolve(I,{x,y})
