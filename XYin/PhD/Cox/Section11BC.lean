/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Arithmetic
import XYin.PhD.Cox.ModularFunctionField
import XYin.PhD.Cox.SingularModuli

/-!
# Cox, Chapter 11, Sections B and C

Umbrella module for the formalization of Cox, *Primes of the form `x² + ny²`*, §11.B–C:

* Theorem 11.9: level-one modular functions are rational in `j` (`theorem_11_9_i`, via Lemma
  11.10, `CuspData.polynomialInJ_of_holomorphic`), and `Γ₀(m)`-modular functions are rational in
  `j` and `j(mτ)` (`theorem_11_9_ii_pointwise`, and in field form `theorem_11_9_ii`,
  `gamma0ModularFunctionField_one`); as subfields of the meromorphic function field, the
  modular functions for `SL₂(ℤ)` and for `Γ₀(m)` are `ℂ(j)` and `ℂ(j, j(mτ))`
  (`theorem_11_9_i_subfield`, `theorem_11_9_ii_subfield`);
* Lemma 11.11 (`coxMatrixEquivRightCosets`) and equations (11.12)–(11.17): the Cox
  representatives `C(m)`, the modular polynomial `modularPolynomialC` characterized by
  `modularPolynomialC_map_evalRingHom`, and the interpolation and recovery formulas
  (`interpolationAt`, `recoveryFormula`);
* Theorem 11.18: integrality and irreducibility (`theorem_11_18_i`, `theorem_11_18_ii`),
  symmetry (`theorem_11_18_iii`), the diagonal (`theorem_11_18_iv_leadingCoeff`,
  `theorem_11_18_iv_degree`), Kronecker's congruence (`theorem_11_18_v`), and the explicit
  example (11.22) (`modularPolynomial_three`);
* Theorem 11.23 and Lemma 11.24: the zeros of `Φ_m` classify cyclic index-`m` lattice
  inclusions (`theorem_11_23`);
* singular moduli are algebraic integers (`singularModulus_isIntegral`);
* the prerequisite lattice `j` classification and the reusable rank-two HNF API.

Importing this module exposes the complete formalization of Cox, Chapter 11, Sections B and C.
-/
