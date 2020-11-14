# Verbatim: A verified lexer generator

## Compilation
This project has been tested with Coq version 8.11.0.

To compile the project:

  make
  
To delete all generated files:

  make clean
  
## Correctness Specification

The definitions of correctness can be found in spec.v

## Correctness Theorems

The statements and proof of the correctness theorems can be found in correctness.v

## Components

The matcher, prefix finder, and lexer can be found in matcher.v, prefixer.v, and lexer.v; respectively.

## Helpers

Some auxilary definitions and lemmas can be found in the aux directory
