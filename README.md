# Llean - Lean Implementations of Lambda Calculi and Type Systems

Llean is a collection of Lean formalizations of various lambda calculi and type systems, designed for educational purposes and as a reference implementation.

## Overview

This repository contains implementations of three different calculi:

1. **Llean/Lc.lean**: A simple untyped lambda calculus with evaluation and termination control
2. **Llean/Sf.lean**: A simply typed lambda calculus with integers, strings, and polymorphism
3. **Llean/Stlc.lean**: A more advanced type system (System F style) with type variables and a type constructor for all

## Features

### Untyped Lambda Calculus (Llean/Lc.lean)
- Basic lambda calculus expressions
- Evaluation with fuel-based termination control
- Simple variable substitution and application
- Closure representation for function values

### Simply Typed Lambda Calculus (Llean/Sf.lean)
- Support for integers and strings
- Type checking with error reporting
- Polymorphism through type variables and forall
- Application and abstraction operations
- Runtime evaluation with type safety

### Advanced Type System (Llean/Stlc.lean)
- System F-style type system
- Type variables and type constructors
- Type checking with context management
- Evaluation with type safety
- Complex type expressions and variable scoping

## Getting Started

### Prerequisites
- Lean 4 installed
- Basic understanding of lambda calculus and type systems

### Installation
1. Clone the repository
2. No additional dependencies required

## Usage

Each file contains examples of how to use the respective calculus:

