/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicCapture
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicIntersection

/-!
# Cyclotomic capture and change of base

Janusz V.5.4, printed161/PDF172, passes from the rational cyclotomic intersection to the relative
intersection over K. These contracts keep the actual embedded fields and expose the degree and
scalar-tower adapters.
-/

namespace Cox.ClassFieldTheory.CyclotomicBaseChange

/-- The captured intersection vanishes when the two root orders are coprime. -/
theorem rational_intersection_of_capture {Ω : Type*} [Field Ω] [CharZero Ω]
    (L : IntermediateField ℚ Ω) (M m : ℕ) (hM : 0 < M) (hm : 0 < m)
    (hcop : M.Coprime m) (ζ ξ : Ω)
    (hζ : IsPrimitiveRoot ζ M) (hξ : IsPrimitiveRoot ξ m)
    (hcap : L ⊓ IntermediateField.adjoin ℚ {ξ} ≤
      IntermediateField.adjoin ℚ {ζ}) :
    L ⊓ IntermediateField.adjoin ℚ {ξ} = ⊥ := by
  have hbot := CyclotomicIntersection.inf_eq_bot_of_coprime M m hM hm hcop ζ ξ hζ hξ
  rw [eq_bot_iff, ← hbot]
  exact le_inf hcap inf_le_right

/-- One finite root order controls all later rational intersections. -/
theorem exists_rational_intersection_bound {Ω : Type*} [Field Ω] [CharZero Ω]
    (L : IntermediateField ℚ Ω) [Finite (IntermediateField ℚ L)] :
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, 0 < m → M.Coprime m →
      ∀ ξ : Ω, IsPrimitiveRoot ξ m →
        L ⊓ IntermediateField.adjoin ℚ {ξ} = ⊥ := by
  obtain ⟨M, hM, ζ, hζ, hcap⟩ :=
    @CyclotomicCapture.exists_cyclotomic_intersection_capture ℚ Ω _ _ _ L
      (by convert ‹Finite (IntermediateField ℚ L)›)
  exact ⟨M, hM, fun m hm hcop ξ hξ =>
    rational_intersection_of_capture L M m hM hm hcop ζ ξ hζ hξ (hcap m hm ξ hξ)⟩

/-- A primitive root generates a cyclotomic intermediate field. -/
theorem rootField_isCyclotomic {F Ω : Type*}
    [Field F] [Field Ω] [Algebra F Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n) :
    IsCyclotomicExtension {n} F (IntermediateField.adjoin F {ξ}) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hint : IsIntegral F ξ := CyclotomicIntersection.isIntegral_of_primitiveRoot n hn ξ hξ
  have heq : (IntermediateField.adjoin F {ξ}).toSubalgebra = Algebra.adjoin F {ξ} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic
  haveI := IsPrimitiveRoot.adjoin_isCyclotomicExtension F hξ
  exact IsCyclotomicExtension.equiv (S := {n}) (A := F)
    (f := Subalgebra.equivOfEq _ _ heq.symm)

/-- A primitive root generates a Galois intermediate field. -/
theorem rootField_isGalois {F Ω : Type*}
    [Field F] [Field Ω] [Algebra F Ω]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n) :
    IsGalois F (IntermediateField.adjoin F {ξ}) := by
  haveI := rootField_isCyclotomic (F := F) n hn ξ hξ
  exact IsCyclotomicExtension.isGalois {n} F _

/-- Adjoining a set through a coherent field tower is idempotent. -/
theorem adjoin_adjoin_of_tower {F K Ω : Type*}
    [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω]
    [Algebra K Ω] [IsScalarTower F K Ω] (s : Set Ω) :
    IntermediateField.adjoin K (IntermediateField.adjoin F s : Set Ω) =
      IntermediateField.adjoin K s := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    have hle : IntermediateField.adjoin F s ≤ (IntermediateField.adjoin K s).restrictScalars F := by
      rw [IntermediateField.adjoin_le_iff]
      exact IntermediateField.subset_adjoin K s
    exact hle hx
  · exact IntermediateField.adjoin.mono K _ _ (IntermediateField.subset_adjoin F s)

/-- Linear disjointness preserves the degree of an adjoining field. -/
theorem finrank_adjoin_of_linearDisjoint {F L Ω : Type*}
    [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω]
    [Algebra L Ω] [IsScalarTower F L Ω]
    (A : IntermediateField F Ω) [Algebra.IsAlgebraic F A]
    (h : A.LinearDisjoint L) :
    Module.finrank L (IntermediateField.adjoin L (A : Set Ω)) =
      Module.finrank F A := by
  exact congrArg Cardinal.toNat h.adjoin_rank_eq_rank_left_of_isAlgebraic_left

/-- The relative degree equality implies disjointness of the adjoining field. -/
theorem linearDisjoint_adjoin_of_finrank_eq {K Ω : Type*}
    [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) (s : Set Ω)
    [FiniteDimensional K L] [FiniteDimensional K (IntermediateField.adjoin K s)]
    (hdeg : Module.finrank L (IntermediateField.adjoin L s) =
      Module.finrank K (IntermediateField.adjoin K s)) :
    (IntermediateField.adjoin K s).LinearDisjoint L := by
  apply IntermediateField.LinearDisjoint.of_finrank_sup
  have h := Module.finrank_mul_finrank K L (IntermediateField.adjoin L s)
  rw [hdeg] at h
  rw [sup_comm, ← IntermediateField.restrictScalars_adjoin_eq_sup, mul_comm]
  exact h.symm

/-- Linear disjointness persists when the base is enlarged inside the other field. -/
theorem linearDisjoint_adjoin_baseChange {F K Ω : Type*}
    [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω]
    [Algebra K Ω] [IsScalarTower F K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsScalarTower F L Ω]
    (ξ : Ω) (hInt : IsIntegral F ξ)
    (h : (IntermediateField.adjoin F {ξ}).LinearDisjoint L) :
    (IntermediateField.adjoin K {ξ}).LinearDisjoint L := by
  haveI : FiniteDimensional F (IntermediateField.adjoin F {ξ}) :=
    IntermediateField.adjoin.finiteDimensional hInt
  haveI : FiniteDimensional K (IntermediateField.adjoin K {ξ}) :=
    IntermediateField.adjoin.finiteDimensional hInt.tower_top
  haveI : Algebra.IsAlgebraic F (IntermediateField.adjoin F {ξ}) :=
    Algebra.IsAlgebraic.of_finite _ _
  have hL := finrank_adjoin_of_linearDisjoint (L := L) (IntermediateField.adjoin F {ξ}) h
  have hK := finrank_adjoin_of_linearDisjoint (L := K) (IntermediateField.adjoin F {ξ})
    (h.of_le_right' K)
  rw [adjoin_adjoin_of_tower] at hL hK
  exact linearDisjoint_adjoin_of_finrank_eq L {ξ} (hL.trans hK.symm)

/-- Janusz V.5.4: rational disjointness gives the required relative intersection. -/
theorem relative_intersection_of_rational_intersection {K Ω : Type*}
    [Field K] [CharZero K] [Field Ω] [CharZero Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional ℚ L]
    (n : ℕ) (hn : 0 < n) (ξ : Ω) (hξ : IsPrimitiveRoot ξ n)
    (hinter : L.restrictScalars ℚ ⊓ IntermediateField.adjoin ℚ {ξ} = ⊥) :
    L ⊓ IntermediateField.adjoin K {ξ} = ⊥ := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional ℚ (L.restrictScalars ℚ) := inferInstanceAs (FiniteDimensional ℚ L)
  have hint : IsIntegral ℚ ξ := CyclotomicIntersection.isIntegral_of_primitiveRoot n hn ξ hξ
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ξ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI := rootField_isGalois (F := ℚ) n hn ξ hξ
  have hld : (IntermediateField.adjoin ℚ {ξ}).LinearDisjoint (L.restrictScalars ℚ) :=
    IntermediateField.LinearDisjoint.of_inf_eq_bot (by rw [inf_comm]; exact hinter)
  have hld' : (IntermediateField.adjoin ℚ {ξ}).LinearDisjoint L := hld
  have hK := linearDisjoint_adjoin_baseChange (F := ℚ) L ξ hint hld'
  rw [inf_comm]
  exact hK.inf_eq_bot

/-- Janusz V.5.4: choose the finite exclusion order before selecting the modulus. -/
theorem exists_relative_intersection_bound {K Ω : Type*}
    [Field K] [CharZero K] [Field Ω] [CharZero Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional ℚ L] :
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, 0 < m → M.Coprime m →
      ∀ ξ : Ω, IsPrimitiveRoot ξ m →
        L ⊓ IntermediateField.adjoin K {ξ} = ⊥ := by
  haveI : FiniteDimensional ℚ (L.restrictScalars ℚ) := inferInstanceAs (FiniteDimensional ℚ L)
  haveI : Finite (IntermediateField ℚ (L.restrictScalars ℚ)) :=
    CyclotomicCapture.finite_intermediateFields_of_finite_separable ℚ _
  obtain ⟨M, hM, hbound⟩ := exists_rational_intersection_bound (L.restrictScalars ℚ)
  exact ⟨M, hM, fun m hm hcop ξ hξ =>
    relative_intersection_of_rational_intersection L m hm ξ hξ (hbound m hm hcop ξ hξ)⟩

end Cox.ClassFieldTheory.CyclotomicBaseChange
