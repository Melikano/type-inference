# Assignment 4: Type inference for BPCF

# Your Task
From: https://pages.cpsc.ucalgary.ca/~robin/class/521/types/Assignment_4.html
```
Assignment #4:  Type inference for BPCF.
 
The main requirement of this assignment is to develop a type inference algorithm for the simply typed lambda calculus with fixed points, pairs, natural numbers, and lists: I call this the Basic Programming language for Computable Functions (BPCF).   To achieve this you will need to collect the type equations and to solve them incrementally.  In addition, as an optional extra you can arrange for programs applied to values to be evaluated on the modern SECD machine.

This extension to the simply typed lambda calculus (BPCF): it is described here together with the type inference algorithm.
The deliverables for this assignment are:

  Input and output routines for BPCF programs and their types.
  An algorithm for collecting type equations and solving them: this the main part of the assignment.
  Optional extra: an evaluator for BPCF programs using an extended modern SECD machine.  For this you must support definitions of programs so that one can apply defined programs to inputs.
Your program (minimally) should allow you to determine whether a program is well-typed and display the program's most general type.   In order to run a program, you should arrange that defined programs can be applied to inputs.
```

# Autograder remarks
- Do NOT change the types of any function prefixed with ``autoGrader``
- Do NOT modify files in ``Lib/*`` 

- You are to ONLY submit the file ``TypeInference.hs`` to GradeScope 

# Directory overview
```
TypeInference.hs
```
You should implement the function ```autoGraderTypeInference``` in this file. 
DO NOT change the type signature of this function.

```
Examples.hs
```
Some example programs (you should write your own tests too!)

```
A4.hs
```
This module that imports everything for you, so you can type `ghci A4.hs` to play with all the functions and your code.

```
README.md
```
This helpful file (probably not that helpful).

```
fixtypes.pdf
```
The assignment document pdf.

```
Lib/AST.hs
```
This includes the AST of the lambda term and the AST of the type you will be working with. Moreover, it includes pretty printing functions of both the type and the lambda term

```
Lib/ASTParse.hs
```
This includes a parser for lambda terms

```
Lib/Monads.hs
```
This includes some common monads which you may find helpful.

```
Lib/RawString.hs
```
This includes some Template Haskell to make it easier to write your own examples (as a raw string literal)
