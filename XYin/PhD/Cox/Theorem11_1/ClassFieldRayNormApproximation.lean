/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldGlobalNormIndex
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormApproximation

/-! # Global norm approximation preserving a complementary ray

Janusz V.12.2 (printed p. 187, PDF p. 198) invokes the simultaneous approximation of
V.4.5. The auxiliary modulus imposes deeper one-congruences at the nondistinguished
inverse-conjugate primes. Only the distinguished prime must avoid the original
modulus.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory

section Approximation
variable (L : Type*) [Field L] [hNL : NumberField L]
include hNL

-- `hNL` is included for the whole section; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- A stronger ideal congruence gives a stronger generated ray subgroup. -/
theorem rayElements_mono {m n : Ideal (𝓞 L)} (h : m ≤ n) :
    rayElements L m ≤ rayElements L n := by
  exact Subgroup.closure_mono fun _ ⟨α, hα, hαm⟩ => ⟨α, hα, h hαm⟩

open Classical in
/-- Impose the original ray and one-congruences at the other chosen primes. -/
def rayApproximationModulus (w : HeightOneSpectrum (𝓞 L)) (n : Ideal (𝓞 L))
    (S : Finset (HeightOneSpectrum (𝓞 L))) (s : ℕ) : Ideal (𝓞 L) :=
  n * ∏ q ∈ S.erase w, q.asIdeal ^ s

-- `hNL` is included for the whole section; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- The auxiliary congruence modulus is nonzero. -/
theorem rayApproximationModulus_ne_bot (w : HeightOneSpectrum (𝓞 L))
    (n : Ideal (𝓞 L)) (hn : n ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 L))) (s : ℕ) :
    rayApproximationModulus L w n S s ≠ ⊥ := by
  rw [rayApproximationModulus, ← Ideal.zero_eq_bot]
  refine mul_ne_zero (by rwa [Ideal.zero_eq_bot]) ?_
  rw [Finset.prod_ne_zero_iff]
  exact fun q _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact q.ne_bot)

/-- The auxiliary modulus still avoids the distinguished prime. -/
theorem rayApproximationModulus_coprime (w : HeightOneSpectrum (𝓞 L))
    (n : Ideal (𝓞 L)) (hcop : w.asIdeal ⊔ n = ⊤)
    (S : Finset (HeightOneSpectrum (𝓞 L))) (s : ℕ) :
    w.asIdeal ⊔ rayApproximationModulus L w n S s = ⊤ := by
  classical
  rw [rayApproximationModulus, Ideal.sup_mul_eq_of_coprime_left hcop]
  refine Ideal.sup_prod_eq_top fun q hq => Ideal.sup_pow_eq_top ?_
  refine Ideal.IsMaximal.coprime_of_ne w.isMaximal q.isMaximal fun h => ?_
  exact (Finset.mem_erase.mp hq).1 (HeightOneSpectrum.ext h.symm)

-- `hNL` is included for the whole section; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- The original complementary ray condition is retained. -/
theorem rayApproximationModulus_le (w : HeightOneSpectrum (𝓞 L))
    (n : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L))) (s : ℕ) :
    rayApproximationModulus L w n S s ≤ n := by
  exact Ideal.mul_le_right

-- `hNL` is included for the whole section; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Every nondistinguished selected prime receives the required one-congruence. -/
theorem rayApproximationModulus_le_primePower (w : HeightOneSpectrum (𝓞 L))
    (n : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L))) (s : ℕ)
    (q : HeightOneSpectrum (𝓞 L)) (hq : q ∈ S) (hqw : q ≠ w) :
    rayApproximationModulus L w n S s ≤ q.asIdeal ^ s := by
  classical
  have hq' : q ∈ S.erase w := Finset.mem_erase.mpr ⟨hqw, hq⟩
  exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hq'))

/-- The actual ray-quotient surjection gives a ray-preserving approximation witness. -/
theorem exists_ray_preserving_localApprox (w : HeightOneSpectrum (𝓞 L))
    (n : Ideal (𝓞 L)) (hn : n ≠ ⊥) (hcop : w.asIdeal ⊔ n = ⊤)
    (β : (w.adicCompletion L)ˣ) (s : ℕ) :
    ∃ γ : rayElements L n,
      completionUnitMap L w (γ : Lˣ) * β⁻¹ ∈ localFieldUnitFiltration L w s := by
  obtain ⟨γ, hγ⟩ := localRayMap_ray_restriction_surjective L w n hn hcop s (QuotientGroup.mk β)
  refine ⟨γ, ?_⟩
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, localRayMap_apply, QuotientGroup.eq] at hγ
  have h := Subgroup.inv_mem _ hγ
  rw [mul_inv_rev, inv_inv, mul_comm] at h
  exact h

/-- A single ray element realizes the target at w and one at every other selected prime. -/
theorem exists_ray_preserving_finitePrimeApprox (w : HeightOneSpectrum (𝓞 L))
    (n : Ideal (𝓞 L)) (hn : n ≠ ⊥) (hcop : w.asIdeal ⊔ n = ⊤)
    (S : Finset (HeightOneSpectrum (𝓞 L))) (β : (w.adicCompletion L)ˣ)
    (s : ℕ) (hs : 0 < s) :
    ∃ γ : rayElements L n,
      completionUnitMap L w (γ : Lˣ) * β⁻¹ ∈ localFieldUnitFiltration L w s ∧
        ∀ q ∈ S, q ≠ w →
          completionUnitMap L q (γ : Lˣ) ∈ localFieldUnitFiltration L q s := by
  obtain ⟨γ, hγ⟩ := exists_ray_preserving_localApprox L w (rayApproximationModulus L w n S s)
    (rayApproximationModulus_ne_bot L w n hn S s) (rayApproximationModulus_coprime L w n hcop S s)
    β s
  refine ⟨⟨γ, rayElements_mono L (rayApproximationModulus_le L w n S s) γ.2⟩, hγ,
    fun q hq hqw => ?_⟩
  have hray : (γ : Lˣ) ∈ rayElements L (q.asIdeal ^ s) :=
    rayElements_mono L (rayApproximationModulus_le_primePower L w n S s q hq hqw) γ.2
  rw [← localRayMap_ker L q s hs, MonoidHom.mem_ker, localRayMap_apply,
    QuotientGroup.eq_one_iff] at hray
  exact hray

variable (K : Type*) [Field K] [Algebra K L]

/-- The source coset product approximation can retain a prescribed complementary ray. -/
theorem exists_coset_product_localRay_approx_preserving_ray
    (w : HeightOneSpectrum (𝓞 L)) (n : Ideal (𝓞 L)) (hn : n ≠ ⊥)
    (hcop : w.asIdeal ⊔ n = ⊤) (T : Finset (L ≃ₐ[K] L))
    (hT : Subgroup.IsComplement
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal : Set (L ≃ₐ[K] L))
      (T : Set (L ≃ₐ[K] L))) (h1 : 1 ∈ T)
    (β : (w.adicCompletion L)ˣ) (s : ℕ) (hs : 0 < s) :
    ∃ γ : rayElements L n,
      (∏ τ ∈ T, completionUnitMap L w (Units.map τ.toMonoidHom (γ : Lˣ))) * β⁻¹ ∈
        localFieldUnitFiltration L w s := by
  classical
  let S := T.image (fun τ : L ≃ₐ[K] L => inverseConjugatePrime L τ.toRingEquiv w)
  obtain ⟨γ, hγw, hγS⟩ := exists_ray_preserving_finitePrimeApprox L w n hn hcop S β s hs
  refine ⟨γ, ?_⟩
  have key := prod_mul_inv_mem_of_forall T (localFieldUnitFiltration L w s)
    (fun τ => completionUnitMap L w (Units.map τ.toMonoidHom (γ : Lˣ)))
    (fun τ => if 1 = τ then β else 1) (fun τ hτ => ?_)
  · have hprod : (∏ τ ∈ T, if 1 = τ then β else 1) = β :=
      Finset.prod_ite_eq_of_mem T 1 (fun _ => β) h1
    rwa [hprod] at key
  · by_cases hτ1 : τ = 1
    · subst hτ1
      beta_reduce
      rw [if_pos rfl]
      exact hγw
    · beta_reduce
      rw [if_neg (Ne.symm hτ1), inv_one, mul_one]
      have hne := inverseConjugatePrime_ne_of_transversal K L w T hT h1 τ hτ hτ1
      have hmem := hγS _ (Finset.mem_image_of_mem _ hτ) hne
      exact conjugate_localRay_mem L τ.toRingEquiv w (γ : Lˣ) s hs hmem
end Approximation

/-- Coprime ideals remain coprime to any ideal lying over the first one. -/
theorem extended_modulus_coprime_at_liesOver (A B : Type*)
    [CommSemiring A] [Semiring B] [Algebra A B]
    (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (m : Ideal A) (hcop : p ⊔ m = ⊤) :
    P ⊔ m.map (algebraMap A B) = ⊤ := by
  have hp : p.map (algebraMap A B) ≤ P :=
    Ideal.map_le_iff_le_comap.mpr (Ideal.over_def P p).le
  have htop : p.map (algebraMap A B) ⊔ m.map (algebraMap A B) = ⊤ := by
    rw [← Ideal.map_sup, hcop, Ideal.map_top]
  exact eq_top_mono (sup_le_sup hp le_rfl) htop

section Norm
variable (K L : Type*) [Field K] [Field L] [hNK : NumberField K]
  [hNL : NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
include hNK hNL hvw

/-- Janusz V.12.2: one global norm preserves the ray condition and approximates a local norm. -/
theorem exists_globalNorm_localRay_approx_preserving_ray [IsGalois K L]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤)
    (β : (w.adicCompletion L)ˣ) (b : ℕ) :
    letI := completionAlgebra K L v w
    ∃ γ : Lˣ,
      Units.map (Algebra.norm K : L →* K) γ ∈ rayElements K m ∧
        completionUnitMap K v (Units.map (Algebra.norm K : L →* K) γ) *
          (Units.map (Algebra.norm (v.adicCompletion K) :
            w.adicCompletion L →* v.adicCompletion K) β)⁻¹ ∈
              localFieldUnitFiltration K v b := by
  have hn : m.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hm
  have hcopn : w.asIdeal ⊔ m.map (algebraMap (𝓞 K) (𝓞 L)) = ⊤ :=
    extended_modulus_coprime_at_liesOver (𝓞 K) (𝓞 L) v.asIdeal w.asIdeal m hcop
  obtain ⟨T, hT, h1⟩ := exists_finset_rightTransversal_one (L ≃ₐ[K] L)
    (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)
  obtain ⟨s, hs, hs'⟩ := LocalCyclic.exists_localNorm_ray_depth K L v w β b
  obtain ⟨γ, hγ⟩ := exists_coset_product_localRay_approx_preserving_ray L K w _ hn hcopn
    T hT h1 β s hs
  refine ⟨γ, norm_rayElements_le K L m γ.2, ?_⟩
  rw [LocalCyclic.global_norm_coset_product_units K L v w T hT γ]
  exact hs' _ hγ
end Norm
end Cox.ClassFieldTheory
