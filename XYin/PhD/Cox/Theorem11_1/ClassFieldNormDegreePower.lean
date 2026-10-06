/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import XYin.PhD.Cox.Theorem11_1.ClassFieldTheory

/-! # Degree powers in the norm image

Janusz V.5.6, printed164: extension followed by norm is the degree power.
The norm image and good-ideal carriers are the existing definitions.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

/-- Every degree power is a norm of a good ideal in the extension. -/
theorem pow_finrank_mem_normImage
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (m : Ideal (𝓞 K)) (u : coprimeIdeals K m) :
    u ^ Module.finrank K L ∈ normImage K m L := by
  letI : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    FractionRing.liftAlgebra _ _
  let N := (normImage K m L).map (coprimeIdeals K m).subtype
  have hdeg : Module.finrank (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) =
      Module.finrank K L := by
    apply Algebra.finrank_eq_of_equiv_equiv
      (FractionRing.algEquiv (𝓞 K) K).toRingEquiv
      (FractionRing.algEquiv (𝓞 L) L).toRingEquiv
    ext x
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 K) K)
      (FractionRing.algEquiv (𝓞 L) L) x
  have hg : coprimeGenerators K m ⊆ N.comap (powMonoidHom (Module.finrank K L)) := by
    intro v hv
    obtain ⟨A, hA, hAm, hvA⟩ := hv
    have hvg : v ∈ coprimeIdeals K m := Subgroup.subset_closure ⟨A, hA, hAm, hvA⟩
    let w : coprimeIdeals K m := ⟨v, hvg⟩
    refine ⟨w ^ Module.finrank K L, Subgroup.subset_closure ?_, rfl⟩
    refine ⟨A.map (algebraMap (𝓞 K) (𝓞 L)), ?_, ?_, ?_⟩
    · exact (Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).not.mpr hA
    · rw [← Ideal.map_sup, hAm, Ideal.map_top]
    · simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      change (v : FractionalIdeal (𝓞 K)⁰ K) ^ Module.finrank K L = _
      rw [hvA, Ideal.relNorm_algebraMap, hdeg, FractionalIdeal.coeIdeal_pow]
  have h := (Subgroup.closure_le _).mpr hg u.property
  rcases h with ⟨v, hv, hvu⟩
  have heq : v = u ^ Module.finrank K L := Subtype.ext hvu
  simpa only [heq] using hv

end Cox.ClassFieldTheory
