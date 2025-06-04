# Llean - Lean Implementations of Lambda Calculi and Type Systems

Llean is a collection of Lean formalizations of various lambda calculi and type systems, designed primarily for educational purposes and as a reference implementation for learning more about type theory and theorem provers like Lean 4.

## Overview

This repository contains implementations of three different calculi, developed as part of a study into formal systems and their implementation in a theorem prover:

1.  **Llean/Lc.lean**: A simple untyped lambda calculus with evaluation and termination control. This implementation focuses on the core mechanics of lambda calculus without the complexities of types.
2.  **Llean/Sf.lean**: A simply typed lambda calculus with integers, strings, and polymorphism. This file explores the basics of type systems, including concrete types and a form of polymorphism.
3.  **Llean/Stlc.lean**: A more advanced type system (System F style) with type variables and a type constructor for all. This implementation delves into more sophisticated type theory concepts like type variables and universal quantification.

## Features

### Untyped Lambda Calculus (Llean/Lc.lean)
-   Basic lambda calculus expressions: Defines the syntax for terms including variables, abstractions, and applications.
-   Evaluation with fuel-based termination control: Implements an evaluation strategy that uses a fuel parameter to prevent infinite loops during evaluation.
-   Simple variable substitution and application: Provides the core operations for reducing lambda calculus terms.
-   Closure representation for function values: Likely uses a representation for functions that captures the environment in which they were defined.

### Simply Typed Lambda Calculus (Llean/Sf.lean)
-   Support for integers and strings: Includes built-in types for basic data.
-   Type checking with error reporting: Implements a type checking function to verify the type correctness of terms and report errors.
-   Polymorphism through type variables and forall: Introduces type variables and a `forall` construct to allow for more general types.
-   Application and abstraction operations: Defines the operations for function application and abstraction within the typed setting.
-   Runtime evaluation with type safety: Provides an evaluation mechanism that respects the type system, ensuring that well-typed programs do not encounter type errors during execution.

### Advanced Type System (Llean/Stlc.lean)
-   System F-style type system: Implements a type system similar to System F, also known as the polymorphic lambda calculus.
-   Type variables and type constructors: Defines the structure of types, including type variables and ways to construct more complex types.
-   Type checking with context management: Implements a type checking algorithm that manages a type context to track the types of free variables.
-   Evaluation with type safety: Provides an evaluation mechanism for terms in this more advanced type system.
-   Complex type expressions and variable scoping: Handles the complexities of type expressions and variable binding within the type system.

## Getting Started

### Prerequisites
-   Lean 4 installed
-   Basic understanding of lambda calculus and type systems

### Installation
1.  Clone the repository
2.  No additional dependencies required

## Usage

Each file contains examples of how to use the respective calculus:

