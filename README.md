# XYin

This repository is based on Chris Birkbeck's modular forms repository and is used for my PhD project on formalising modular curves in Lean.

## Current progress

The main completed components so far are:

1. Generalising the current `qExpansion` API in mathlib from modular forms to functions on the upper half plane that are periodic, holomorphic, and bounded at infinity.
2. Proving that the modular discriminant Delta and the j-function have integral q-expansion coefficients, and computing their first few coefficients explicitly.

## Ongoing work

Current projects include:

1. Building a new API for q-expansions as formal Laurent series.
2. Writing tactics for power series coefficients and q-expansions.
3. Building the APIs `IsRIntegralPowerSeries` and `HasRIntegralQExpansion` for general rings.
4. Defining modular equations.
