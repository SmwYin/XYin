/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldFiniteRadicalUnramified
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnitRadicalFinite
import XYin.PhD.Cox.Theorem11_1.ClassFieldFiniteRadicalGenerators
import XYin.PhD.Cox.Theorem11_1.ClassFieldRadicalLocalUnits

/-! # Finite S-unit radical extensions are unramified outside S

Source: Janusz V.8.2 and V.9.3.
-/

noncomputable section
namespace Cox.ClassFieldTheory
open NumberField IsDedekindDomain IntermediateField

/-- The radical field of S-units is unramified outside S when S contains the exponent primes. -/
theorem sUnitRadicalField_ramificationIdx_eq_one
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (hcover : CoversNthPrimes K n S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (w : HeightOneSpectrum (𝓞 (radicalField K n (sUnits K S))))
    [w.asIdeal.LiesOver v.asIdeal] :
    Ideal.ramificationIdx v.asIdeal w.asIdeal = 1 := by
  have hunit := nth_isUnit_in_completion_of_not_mem_support K n S hcover v hv
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    simp [hn0] at hunit
  letI := sUnits_finiteQuotient K S n hn
  letI := radicalField_finiteDimensional K n hn (sUnits K S)
  letI := NumberField.of_module_finite K (radicalField K n (sUnits K S))
  obtain ⟨s, hgen, hs⟩ := exists_finite_radical_generators K n hn (sUnits K S)
  apply ramificationIdx_eq_one_of_finite_radical_generators K
    (radicalField K n (sUnits K S)) v n hunit s hgen _ w
  intro x hx
  obtain ⟨a, ha⟩ := hs x hx
  exact ⟨((a : Kˣ) : K), valuation_eq_one_of_mem_sUnits K S (a : Kˣ) a.property v hv, ha⟩

end Cox.ClassFieldTheory
