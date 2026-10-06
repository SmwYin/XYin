/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldSupportedOrbits
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The finite local-degree product in Janusz V.2.5

The actual supported orbit product is reindexed by base prime divisors and compared
with the existing finprod. Reciprocal Herbrand cancellation remains in the parent.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- A nonzero extended modulus has finitely many actual supported primes. -/
theorem supportedPrime_finite (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Finite (supportedPrimeSubMulAction K L m) := by
  have hM : m.map (algebraMap (𝓞 K) (𝓞 L)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot]
    exact Ideal.map_ne_bot_of_ne_bot hm
  have hfin := Ideal.finite_factors hM
  simp only [Ideal.dvd_iff_le] at hfin
  exact hfin.to_subtype

omit [NumberField K] [NumberField L] in
/-- The existing finprod is exactly the finite product over actual base prime divisors. -/
theorem localDegreeProduct_eq_subtypeProduct (m : Ideal (𝓞 K))
    [Fintype {v : HeightOneSpectrum (𝓞 K) // m ≤ v.asIdeal}] :
    localDegreeProduct K L m =
      ∏ v : {v : HeightOneSpectrum (𝓞 K) // m ≤ v.asIdeal},
        v.val.asIdeal.ramificationIdxIn (𝓞 L) *
          v.val.asIdeal.inertiaDegIn (𝓞 L) := by
  classical
  rw [localDegreeProduct]
  have h : (∏ᶠ v : HeightOneSpectrum (𝓞 K), if m ≤ v.asIdeal then
      v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) else 1) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : m ≤ v.asIdeal),
        v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) :=
    finprod_congr fun v => finprod_eq_if.symm
  rw [h, ← finprod_subtype_eq_finprod_cond, finprod_eq_prod_of_fintype]

open Classical in
/-- Reindexing actual supported orbits yields the source's local-degree product. -/
theorem supportedPrime_stabilizerProduct [IsGalois K L] (m : Ideal (𝓞 K))
    [Fintype (supportedPrimeSubMulAction K L m)] :
    (∏ c : MulAction.orbitRel.Quotient (L ≃ₐ[K] L)
        (supportedPrimeSubMulAction K L m),
      Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) c.out)) =
        localDegreeProduct K L m := by
  obtain ⟨E, hE⟩ := exists_supportedPrimeOrbitEquiv K L m
  letI : Fintype {v : HeightOneSpectrum (𝓞 K) // m ≤ v.asIdeal} := Fintype.ofEquiv _ E
  rw [localDegreeProduct_eq_subtypeProduct K L m, ← Equiv.prod_comp E
    (fun v : {v : HeightOneSpectrum (𝓞 K) // m ≤ v.asIdeal} =>
      v.val.asIdeal.ramificationIdxIn (𝓞 L) * v.val.asIdeal.inertiaDegIn (𝓞 L))]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [supportedPrime_stabilizer_card]
  have h := hE c.out
  rw [Quotient.out_eq'] at h
  rw [h]

end Cox.ClassFieldTheory
