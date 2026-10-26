/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldAuxiliaryFamily
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicBaseChange

/-!
# The same root family inside a common finite ambient

Janusz V.5.4–5.6, printed161–162/PDF172–173, first passes from rational root fields to relative
fields, then uses the entire selected prefix in a common compositum. These adapters preserve those
literal fields through scalar and ambient restriction. Constructing the finite Galois ambient and
proving its all-prime unramification remain separate obligations.
-/

open IntermediateField
noncomputable section
namespace Cox.ClassFieldTheory.ArtinAuxiliary

/-- Janusz V.5.4–5.6, pp161–162: native scalar transport of the anchored root prefix. -/
theorem restrictScalars_sup_iSup_adjoin
    {F K Ω ι : Type*} [Field F] [Field K] [Field Ω]
    [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
    (L : IntermediateField K Ω) (s : ι → Set Ω) :
    (L ⊔ ⨆ i, adjoin K (s i)).restrictScalars F =
      L.restrictScalars F ⊔ ⨆ i, adjoin F (s i) := by
  apply le_antisymm
  · have hK : ∀ x : K, algebraMap K Ω x ∈
        (L.restrictScalars F ⊔ ⨆ i, adjoin F (s i)).toSubfield := fun x =>
      (le_sup_left : L.restrictScalars F ≤ L.restrictScalars F ⊔ ⨆ i, adjoin F (s i))
        (L.algebraMap_mem x)
    let T : IntermediateField K Ω :=
      (L.restrictScalars F ⊔ ⨆ i, adjoin F (s i)).toSubfield.toIntermediateField hK
    have hle : L ⊔ ⨆ i, adjoin K (s i) ≤ T := by
      refine sup_le (fun x hx => (le_sup_left :
        L.restrictScalars F ≤ L.restrictScalars F ⊔ ⨆ i, adjoin F (s i)) hx)
        (iSup_le fun i => ?_)
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      exact (le_sup_right : (⨆ i, adjoin F (s i)) ≤ L.restrictScalars F ⊔ ⨆ i, adjoin F (s i))
        ((le_iSup (fun i => adjoin F (s i)) i) (subset_adjoin F (s i) hx))
    intro x hx
    exact hle hx
  · refine sup_le (fun x hx => (le_sup_left : L ≤ L ⊔ ⨆ i, adjoin K (s i)) hx)
      (iSup_le fun i => ?_)
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    exact (le_sup_right : (⨆ i, adjoin K (s i)) ≤ L ⊔ ⨆ i, adjoin K (s i))
      ((le_iSup (fun i => adjoin K (s i)) i) (subset_adjoin K (s i) hx))

/-- Janusz V.5.4–5.6, pp161–162: native ambient restriction of the same field prefix. -/
theorem restrict_sup_iSup_inf_eq_bot
    {K Ω ι : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (M L Q : IntermediateField K Ω) (E : ι → IntermediateField K Ω)
    (hL : L ≤ M) (hQ : Q ≤ M) (hE : ∀ i, E i ≤ M)
    (hInf : (L ⊔ ⨆ i, E i) ⊓ Q = ⊥) :
    ((L.restrict hL) ⊔ ⨆ i, (E i).restrict (hE i)) ⊓ Q.restrict hQ = ⊥ := by
  apply IntermediateField.lift_injective
  have hi : IntermediateField.lift (⨆ i, (E i).restrict (hE i)) = ⨆ i, E i := by
    rw [IntermediateField.lift, IntermediateField.map_iSup]
    exact iSup_congr fun i => IntermediateField.lift_restrict (hE i)
  rw [IntermediateField.lift_inf, IntermediateField.lift_sup, IntermediateField.lift_restrict,
    hi, IntermediateField.lift_restrict, IntermediateField.lift_bot]
  exact hInf

/-- Janusz V.5.4–5.6, pp161–162: rational disjointness gives the same relative prefix. -/
theorem restricted_prefix_inf_eq_bot_of_rational
    {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [CharZero Ω] [Algebra K Ω]
    (M L : IntermediateField K Ω) [FiniteDimensional ℚ M]
    (r : ℕ) (m : Fin r → ℕ) (ξ : Fin r → Ω)
    (hm : ∀ i, 0 < m i) (hξ : ∀ i, IsPrimitiveRoot (ξ i) (m i))
    (hL : L ≤ M) (hE : ∀ i, adjoin K {ξ i} ≤ M)
    (hInf : ∀ i,
      (L.restrictScalars ℚ ⊔ ⨆ j : {j : Fin r // j < i}, adjoin ℚ {ξ j.1}) ⊓
        adjoin ℚ {ξ i} = ⊥) :
    ∀ i,
      ((L.restrict hL) ⊔ ⨆ j : {j : Fin r // j < i},
        (adjoin K {ξ j.1}).restrict (hE j.1)) ⊓
          (adjoin K {ξ i}).restrict (hE i) = ⊥ := by
  intro i
  have hPM : L ⊔ ⨆ j : {j : Fin r // j < i}, adjoin K {ξ j.1} ≤ M :=
    sup_le hL (iSup_le fun j => hE j.1)
  haveI : FiniteDimensional ℚ (M.restrictScalars ℚ) := inferInstanceAs (FiniteDimensional ℚ M)
  have hle : (L ⊔ ⨆ j : {j : Fin r // j < i}, adjoin K {ξ j.1}).restrictScalars ℚ ≤
      M.restrictScalars ℚ := fun x hx => hPM hx
  haveI : FiniteDimensional ℚ
      ((L ⊔ ⨆ j : {j : Fin r // j < i}, adjoin K {ξ j.1}).restrictScalars ℚ) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).toRingHom.injective
  haveI : FiniteDimensional ℚ ↥(L ⊔ ⨆ j : {j : Fin r // j < i}, adjoin K {ξ j.1}) :=
    inferInstanceAs (FiniteDimensional ℚ
      ((L ⊔ ⨆ j : {j : Fin r // j < i}, adjoin K {ξ j.1}).restrictScalars ℚ))
  have hrat : (L ⊔ ⨆ j : {j : Fin r // j < i}, adjoin K {ξ j.1}).restrictScalars ℚ ⊓
      adjoin ℚ {ξ i} = ⊥ := by
    rw [restrictScalars_sup_iSup_adjoin L (fun j : {j : Fin r // j < i} => ({ξ j.1} : Set Ω))]
    exact hInf i
  have hrel := CyclotomicBaseChange.relative_intersection_of_rational_intersection
    (L ⊔ ⨆ j : {j : Fin r // j < i}, adjoin K {ξ j.1}) (m i) (hm i) (ξ i) (hξ i) hrat
  exact restrict_sup_iSup_inf_eq_bot M L (adjoin K {ξ i})
    (fun j : {j : Fin r // j < i} => adjoin K {ξ j.1}) hL (hE i) (fun j => hE j.1) hrel

end Cox.ClassFieldTheory.ArtinAuxiliary
