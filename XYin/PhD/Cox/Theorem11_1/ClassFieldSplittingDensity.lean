/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldDefs
import XYin.PhD.Cox.Theorem11_1.Chebotarev
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # Complete-splitting density, before class-field existence
These source-derived contracts are shared by Janusz IV.5.5 and IV.5.6.
-/
open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]
variable (m : Ideal (𝓞 K)) (L : Type*) [Field L] [NumberField L] [Algebra K L]
variable [Module.Finite (𝓞 K) (𝓞 L)]

/-- Identity Frobenius is the complete-splitting condition over an arbitrary number field. -/
theorem splittingIdeals_eq_frobeniusClass_one [IsGalois K L] :
    splittingIdeals K L =
      Chebotarev.frobeniusClassPrimes K L (ConjClasses.mk (1 : L ≃ₐ[K] L)) := by
  ext q
  constructor
  · rintro ⟨hqp, hq0, hsplit⟩
    haveI := hqp
    have hunr : Chebotarev.UnramifiedIn K L q := by
      refine ⟨hq0, fun P hPmax hPlo => ?_⟩
      have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq0 P
      refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP0).mpr ?_
      rw [← hPlo.over]
      exact (hsplit P ⟨hPmax.isPrime, hPlo⟩).1
    refine ⟨hqp, hunr, ?_⟩
    obtain ⟨P, hPp, hPlo, -⟩ := Chebotarev.exists_prime_liesOver K L q hq0
    haveI := hPp
    haveI : Finite (𝓞 L ⧸ P) := Chebotarev.UnramifiedIn.finite_quotient K L hunr P hPlo
    have hφ := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) P
    have hcl := Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt K L q hunr _ P hφ hPlo
    have hord := Chebotarev.finrank_residue_eq_orderOf K L _ _ rfl q hunr hcl P hPlo
    have hpbot : P.under (𝓞 K) ≠ ⊥ := hPlo.over ▸ hq0
    haveI : (P.under (𝓞 K)).IsMaximal := (inferInstance : (P.under (𝓞 K)).IsPrime).isMaximal hpbot
    haveI : P.LiesOver (P.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := P)
    have hf : Ideal.inertiaDeg (P.under (𝓞 K)) P = 1 := by
      rw [← hPlo.over]
      exact (hsplit P ⟨hPp, hPlo⟩).2
    rw [Ideal.inertiaDeg_algebraMap, hord] at hf
    rw [hcl, orderOf_eq_one_iff.mp hf]
  · rintro ⟨hqp, hunr, hcl⟩
    haveI := hqp
    refine ⟨hqp, hunr.1, fun P hP => ?_⟩
    haveI := hP.1
    haveI := hP.2
    have he := Chebotarev.UnramifiedIn.ramificationIdx_eq_one K L hunr P hP.2
    rw [← hP.2.over] at he
    refine ⟨he, ?_⟩
    have hord := Chebotarev.finrank_residue_eq_orderOf K L 1 _ rfl q hunr hcl P hP.2
    rw [orderOf_one] at hord
    have hpbot : P.under (𝓞 K) ≠ ⊥ := hP.2.over ▸ hunr.1
    haveI : (P.under (𝓞 K)).IsMaximal := (inferInstance : (P.under (𝓞 K)).IsPrime).isMaximal hpbot
    haveI : P.LiesOver (P.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := P)
    rw [hP.2.over, Ideal.inertiaDeg_algebraMap]
    exact hord

/-- Janusz IV.5.2, identity case: complete-split primes have density the inverse degree. -/
theorem density_splittingIdeals [IsGalois K L] :
    Chebotarev.HasDirichletDensity (splittingIdeals K L)
      (1 / (Module.finrank K L : ℝ)) := by
  rw [splittingIdeals_eq_frobeniusClass_one K L]
  have h := Chebotarev.chebotarev_density K L (ConjClasses.mk (1 : L ≃ₐ[K] L))
  have hcar : (ConjClasses.mk (1 : L ≃ₐ[K] L)).carrier = {1} := by
    ext g
    rw [ConjClasses.mem_carrier_iff_mk_eq, Set.mem_singleton_iff, ConjClasses.mk_eq_mk_iff_isConj,
      isConj_one_left]
  rw [hcar, Nat.card_coe_set_eq, Set.ncard_singleton, IsGalois.card_aut_eq_finrank] at h
  simpa using h

/-- Removing the finitely many modulus primes does not change a Dirichlet density. -/
theorem density_diff_finite {S E : Set (Ideal (𝓞 K))} {δ : ℝ}
    (hS : Chebotarev.HasDirichletDensity S δ) (hE : E.Finite) :
    Chebotarev.HasDirichletDensity (S \ E) δ := by
  have hfin : Chebotarev.HasDirichletDensity (S ∩ E) 0 :=
    Chebotarev.hasDirichletDensity_of_finite K (hE.subset Set.inter_subset_right)
  have hsub := hS.sub hfin
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hdisj : Disjoint (S \ E) (S ∩ E) :=
    Set.disjoint_left.mpr fun x hx hx' => hx.2 hx'.2
  have hS' : Chebotarev.primeIdealZetaSum S s =
      Chebotarev.primeIdealZetaSum (S \ E) s + Chebotarev.primeIdealZetaSum (S ∩ E) s := by
    rw [← Chebotarev.primeIdealZetaSum_union_of_disjoint K hdisj hs, Set.diff_union_inter]
  rw [hS']
  ring

/-- Only finitely many nonzero prime ideals divide a nonzero modulus. -/
theorem finite_primes_meeting_modulus (hm : m ≠ ⊥) :
    {q : Ideal (𝓞 K) | q.IsPrime ∧ q ≠ ⊥ ∧ q ⊔ m ≠ ⊤}.Finite := by
  refine ((Ideal.finite_factors hm).image
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v.asIdeal)).subset ?_
  rintro q ⟨hqp, hq0, hqm⟩
  have hmax : q.IsMaximal := hqp.isMaximal hq0
  have hle : m ≤ q := le_sup_right.trans (hmax.eq_of_le hqm le_sup_left).ge
  exact ⟨⟨q, hqp, hq0⟩, Ideal.dvd_iff_le.mpr hle, rfl⟩

end Cox.ClassFieldTheory
