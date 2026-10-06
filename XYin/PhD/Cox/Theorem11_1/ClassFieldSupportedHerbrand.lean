/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldSupportedProduct

/-! # The supported-ideal Herbrand quotient in Janusz V.2.5 -/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
open Cox.CyclicCohomology
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable [hGalois : IsGalois K L]
include hGalois

/-- The prime orbits in Janusz V.2.5 contribute reciprocal local degrees. -/
theorem supportedIdeal_herbrandQuotient (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    herbrandQuotient (supportedIdealRepresentation K L m) σ *
      localDegreeProduct K L m = 1 := by
  haveI := supportedPrime_finite K L m hm
  letI : Fintype (supportedPrimeSubMulAction K L m) := Fintype.ofFinite _
  rw [supportedIdeal_herbrandQuotient_orbits K L m σ hσ,
    ← supportedPrime_stabilizerProduct K L m, Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro c _
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end Cox.ClassFieldTheory
