/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicAutomorphisms
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# Rational intersection gives cyclotomic irreducibility

Janusz V.5.4, printed161/PDF172, uses the actual rational intersection to preserve the full
cyclotomic degree. Irreducibility is first obtained over L and then descends along the actual
K-algebra map into L.
-/

open IntermediateField Polynomial
noncomputable section
namespace Cox.ClassFieldTheory.ArtinAuxiliary

/-- Janusz V.5.4: the actual rational intersection preserves cyclotomic irreducibility. -/
theorem irreducible_cyclotomic_of_rational_intersection
    {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [CharZero Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional ℚ L]
    (m : ℕ) (hm : 0 < m) (ξ : Ω) (hξ : IsPrimitiveRoot ξ m)
    (hinter : L.restrictScalars ℚ ⊓ adjoin ℚ {ξ} = ⊥) :
    Irreducible (cyclotomic m K) := by
  haveI hfinL : FiniteDimensional ℚ (L.restrictScalars ℚ) := by
    convert ‹FiniteDimensional ℚ L›
  haveI := CyclotomicIntersection.finiteDimensional_adjoin_root (F := ℚ) m hm ξ hξ
  haveI := CyclotomicBaseChange.rootField_isGalois (F := ℚ) m hm ξ hξ
  have hld : (adjoin ℚ {ξ}).LinearDisjoint (L.restrictScalars ℚ) :=
    IntermediateField.LinearDisjoint.of_inf_eq_bot (by rw [inf_comm]; exact hinter)
  have hld' : (adjoin ℚ {ξ}).LinearDisjoint L := by
    convert hld
  have hdeg := CyclotomicAutomorphisms.degree_of_rational_disjoint (K := L) m hm ξ hξ hld'
  have hirr := CyclotomicAutomorphisms.irreducible_cyclotomic_of_degree (K := L) m hm ξ hξ hdeg
  apply Polynomial.Monic.irreducible_of_irreducible_map (algebraMap K L) _ (cyclotomic.monic m K)
  rwa [map_cyclotomic]

end Cox.ClassFieldTheory.ArtinAuxiliary
