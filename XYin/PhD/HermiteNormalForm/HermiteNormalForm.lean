/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.HermiteNormalForm.Basis
import XYin.PhD.HermiteNormalForm.Quotient

/-!
# Hermite normal forms and integer lattices

This is the entry point for the HNF API.

* `Basic`: the rectangular integer row predicate, decidability, pivot bounds, and RREF bridge.
* `Pivot`: mathlib pivot certificates, rank, triangularity, and determinant formulas.
* `RowEquivalence`: unimodular row operations preserve row span, rank, and absolute determinant.
* `RankTwo`: direct Bézout row reduction and uniqueness for nonsingular `2 × 2` matrices,
  with unimodular or positive-determinant `SL₂(ℤ)` transformation certificates.
* `Basis`: row HNF for coordinates of a submodule basis, and the index formula.
* `Content`: the gcd of the entries of a rectangular integer matrix, with invariance lemmas.
* `Quotient`: the rank-two cyclic-quotient criterion, independent of HNF.

The row predicate and pivot/rank API allow arbitrary finite rectangular shapes. Existence and
uniqueness are currently supplied for nonsingular rank two, which is the case used by the Cox
development. General rectangular normalization and uniqueness are not claimed here.
-/
