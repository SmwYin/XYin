/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnits
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import XYin.PhD.Cox.Theorem11_1.ClassFieldPrincipalValuation

/-! # Local units and the finite radical family

Janusz V.9.3 and its preceding finite radical reduction: valuation-one elements and
S-units outside S give units of the completed integer rings.
-/
noncomputable section
open NumberField IsDedekindDomain IntermediateField
open scoped nonZeroDivisors
namespace Cox.ClassFieldTheory

/-- A field element of valuation one gives an actual unit in the completed integer ring. -/
theorem exists_completionUnit_of_valuation_eq_one
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (x : K) (hx : v.valuation K x = 1) :
    ∃ u : (v.adicCompletionIntegers K)ˣ,
      ((u : v.adicCompletionIntegers K) : v.adicCompletion K) =
        algebraMap K (v.adicCompletion K) x := by
  let a : v.adicCompletionIntegers K :=
    ⟨algebraMap K (v.adicCompletion K) x, by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.algebraMap_adicCompletion,
        Algebra.algebraMap_self, Function.comp_apply, RingHom.id_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hx.le⟩
  have hu : IsUnit a :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr
      (by simpa only [a, HeightOneSpectrum.algebraMap_adicCompletion,
        Algebra.algebraMap_self, Function.comp_apply, RingHom.id_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hx)
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, congrArg (fun z : v.adicCompletionIntegers K => (z : v.adicCompletion K)) hu⟩

/-- Outside support containing the prime divisors of n, the exponent n is a local integer unit. -/
theorem nth_isUnit_in_completion_of_not_mem_support
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hcover : CoversNthPrimes K n S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    IsUnit (n : v.adicCompletionIntegers K) := by
  apply HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr
  rw [← map_natCast (algebraMap (𝓞 K) (v.adicCompletionIntegers K))]
  change Valued.v ((algebraMap (𝓞 K) K (n : 𝓞 K) : K) : v.adicCompletion K) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.mpr (fun h => hv (hcover v h))

/-- An S-unit has valuation one at every prime outside S. -/
theorem valuation_eq_one_of_mem_sUnits
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) (ha : a ∈ sUnits K S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    v.valuation K (a : K) = 1 := by
  have hc := count_eq_zero_of_mem_supportedIdeals K S ⟨toPrincipalIdeal (𝓞 K) K a, ha⟩ v hv
  rw [coe_toPrincipalIdeal] at hc
  rw [valuation_eq_exp_neg_count_spanSingleton v (a : K) a.ne_zero, hc, neg_zero,
    WithZero.exp_zero]

end Cox.ClassFieldTheory
