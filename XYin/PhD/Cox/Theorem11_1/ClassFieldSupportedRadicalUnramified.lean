/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnitRadicalUnramified
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnramifiedPrimeDescent
import XYin.PhD.Cox.Theorem11_1.ClassFieldRadicalSupport

/-! # Unramified radical subfields supported on S

Source: Janusz V.9.3. A radical field with radicands supported on S lies in the S-unit
radical field, so unramifiedness descends to it.
-/

noncomputable section
open NumberField IsDedekindDomain
namespace Cox.ClassFieldTheory

/-- A radical field supported on S is unramified outside S when S contains the exponent primes. -/
theorem supported_radicalField_ramificationIdx_eq_one
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (hcover : CoversNthPrimes K n S) (W : Subgroup Kˣ)
    (hW : W ≤ sUnits K S ⊔ nthPowers K n)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (w : HeightOneSpectrum (𝓞 (radicalField K n W)))
    [w.asIdeal.LiesOver v.asIdeal] :
    Ideal.ramificationIdx v.asIdeal w.asIdeal = 1 := by
  have hunit := nth_isUnit_in_completion_of_not_mem_support K n S hcover v hv
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    simp [hn0] at hunit
  letI := sUnits_finiteQuotient K S n hn
  let M := radicalField K n W
  let N := radicalField K n (sUnits K S)
  letI := radicalField_finiteDimensional K n hn (sUnits K S)
  letI : NumberField N := NumberField.of_module_finite K N
  have hMN : M ≤ N := radicalField_le_of_le_sup_nthPowers K n hW
  letI : FiniteDimensional K M := FiniteDimensional.of_injective
    (IntermediateField.inclusion hMN).toLinearMap (IntermediateField.inclusion_injective hMN)
  letI : NumberField M := NumberField.of_module_finite K M
  letI : Algebra M N := (IntermediateField.inclusion hMN).toAlgebra
  letI : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  apply ramificationIdx_eq_one_of_forall_liesOver (𝓞 K) (𝓞 M) (𝓞 N) v.asIdeal w.asIdeal
  intro Q hQ hz
  letI := hQ
  letI := hz
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let z : HeightOneSpectrum (𝓞 N) := ⟨Q, hQ, hQ0⟩
  exact sUnitRadicalField_ramificationIdx_eq_one K S n hcover v hv z

end Cox.ClassFieldTheory
