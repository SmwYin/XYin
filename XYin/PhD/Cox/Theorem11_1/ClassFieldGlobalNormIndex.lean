/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldGlobalLocalUnits
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicModules
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormCosets
import XYin.PhD.Cox.Theorem11_1.ClassFieldValuationTransport
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Global norms in local unit-ray quotients

Janusz V.3.4, printed p. 150. The distinguished right transversal prescribes a
completed target at one prime and 1 at each other inverse-conjugate prime.
The source's explicit depth `n * e` is replaced by a sufficiently deep neighborhood,
obtained from continuity of the same determinant norm. This keeps the source's
approximation and coset-product argument.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise WithZero
noncomputable section
namespace Cox.ClassFieldTheory

/-- V.3.4: the distinguished representative is the only one in the decomposition subgroup. -/
theorem rightTransversal_mem_subgroup_iff {G : Type*} [Group G]
    (D : Subgroup G) (T : Finset G)
    (hT : Subgroup.IsComplement (D : Set G) (T : Set G)) (h1 : 1 ∈ T)
    (τ : G) (hτ : τ ∈ T) : τ ∈ D ↔ τ = 1 := by
  refine ⟨fun hD => ?_, fun h => by rw [h]; exact D.one_mem⟩
  have h := (hT.existsUnique τ).unique
    (y₁ := ((⟨τ, hD⟩ : (D : Set G)), (⟨1, h1⟩ : (T : Set G))))
    (y₂ := ((⟨1, D.one_mem⟩ : (D : Set G)), (⟨τ, hτ⟩ : (T : Set G)))) (mul_one τ) (one_mul τ)
  exact (congrArg (fun p => (p.2 : G)) h).symm

/-- V.3.4: termwise multiplicative congruences pass to their finite product. -/
theorem prod_mul_inv_mem_of_forall {ι A : Type*} [CommGroup A]
    (s : Finset ι) (H : Subgroup A) (f g : ι → A)
    (h : ∀ i ∈ s, f i * (g i)⁻¹ ∈ H) :
    (∏ i ∈ s, f i) * (∏ i ∈ s, g i)⁻¹ ∈ H := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  exact Subgroup.prod_mem H h

/-- Normalized integer-radius balls form a cofinal neighborhood basis in a valued ring. -/
theorem exists_valued_small_ball_subset {F : Type*} [Ring F] [Valued F ℤᵐ⁰]
    (a : F) (s : Set F) (hs : s ∈ nhds a) :
    ∃ N : ℤ, {x : F | Valued.v (x - a) < WithZero.exp (-N)} ⊆ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt
    (MonoidWithZeroHom.ValueGroup₀.embedding_unit_pos γ).ne'
  refine ⟨n, fun x hx => hγ ?_⟩
  rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  exact lt_trans hx hn

section CompletionPrecision
variable (K : Type*) [Field K] [hNK : NumberField K]
include hNK


/-- V.3.4: sufficiently deep relative congruence implies any fixed absolute precision. -/
theorem exists_localRay_depth_for_error (v : HeightOneSpectrum (𝓞 K))
    (β : (v.adicCompletion K)ˣ) (N : ℤ) :
    ∃ s : ℕ, 0 < s ∧ ∀ x : (v.adicCompletion K)ˣ,
      x * β⁻¹ ∈ localFieldUnitFiltration K v s →
        Valued.v ((x : v.adicCompletion K) - β) < WithZero.exp (-N) := by
  set k := Multiplicative.toAdd (localUnitValuation K v β)
  have hβ : Valued.v (β : v.adicCompletion K) = WithZero.exp k :=
    (localUnitValuation_apply K v β).symm
  refine ⟨(N + k).toNat + 1, Nat.succ_pos _, fun x hx => ?_⟩
  rw [mem_localFieldUnitFiltration_iff K v _ (Nat.succ_pos _)] at hx
  have hxβ : (x : v.adicCompletion K) - β =
      (((x * β⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1) * β := by
    rw [Units.val_mul, sub_mul, mul_assoc, Units.inv_mul, mul_one, one_mul]
  rw [hxβ, Valuation.map_mul, hβ]
  calc _ ≤ WithZero.exp (-(((N + k).toNat + 1 : ℕ) : ℤ)) * WithZero.exp k :=
        mul_le_mul_left hx _
    _ = WithZero.exp (-(((N + k).toNat + 1 : ℕ) : ℤ) + k) := (WithZero.exp_add _ _).symm
    _ < WithZero.exp (-N) := by
        rw [WithZero.exp_lt_exp]
        have := Int.self_le_toNat (N + k)
        push_cast
        omega
end CompletionPrecision

section PrimeTransport
variable (L : Type*) [Field L] [hNL : NumberField L]
include hNL

/-- The actual inverse-conjugate finite prime used for the source simultaneous approximation. -/
def inverseConjugatePrime (σ : L ≃+* L) (w : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv σ).symm w

omit hNL in
/-- The distinguished representative 1 contributes the originally selected prime. -/
theorem inverseConjugatePrime_one (w : HeightOneSpectrum (𝓞 L)) :
    inverseConjugatePrime L (RingEquiv.refl L) w = w := by
  apply HeightOneSpectrum.ext
  ext x
  exact Iff.rfl

omit hNL in
/-- The inverse-prime definition supplies the forward map equality needed for valuation
transport. -/
theorem map_inverseConjugatePrime_asIdeal (σ : L ≃+* L)
    (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.map (RingOfIntegers.mapRingEquiv σ).toRingHom
      (inverseConjugatePrime L σ w).asIdeal = w.asIdeal := by
  exact Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv σ).surjective w.asIdeal

/-- V.3.4: approximation at the inverse-conjugate prime becomes congruence at the chosen prime. -/
theorem conjugate_localRay_mem (σ : L ≃+* L) (w : HeightOneSpectrum (𝓞 L))
    (γ : Lˣ) (s : ℕ) (hs : 0 < s)
    (hγ : completionUnitMap L (inverseConjugatePrime L σ w) γ ∈
      localFieldUnitFiltration L (inverseConjugatePrime L σ w) s) :
    completionUnitMap L w (Units.map σ.toMonoidHom γ) ∈
      localFieldUnitFiltration L w s := by
  rw [mem_localFieldUnitFiltration_iff L _ s hs, completionUnitMap_apply,
    ← map_one (FinitePlace.embedding _), ← map_sub, FinitePlace.embedding_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hγ ⊢
  have h := primeTransport_valuation L σ (inverseConjugatePrime L σ w) w
    (map_inverseConjugatePrime_asIdeal L σ w) ((γ : L) - 1)
  rw [map_sub, map_one] at h
  rw [Units.coe_map]
  exact h ▸ hγ
end PrimeTransport

section Transversal
variable (K L : Type*) [Field K] [Field L]
  [hNL : NumberField L] [Algebra K L]
include hNL
variable (w : HeightOneSpectrum (𝓞 L))

omit hNL in
/-- Identify inverse prime transport with the ideal action defining the stabilizer. -/
theorem inverseConjugatePrime_asIdeal_inv_smul (τ : L ≃ₐ[K] L) :
    (inverseConjugatePrime L τ.toRingEquiv w).asIdeal = τ⁻¹ • w.asIdeal := by
  ext x
  change RingOfIntegers.mapRingEquiv τ.toRingEquiv x ∈ w.asIdeal ↔ x ∈ τ⁻¹ • w.asIdeal
  rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  have hx : (MulSemiringAction.toRingAut (L ≃ₐ[K] L) (𝓞 L) τ⁻¹).symm x =
      RingOfIntegers.mapRingEquiv τ.toRingEquiv x := by
    change τ⁻¹⁻¹ • x = _
    rw [inv_inv]
    rfl
  rw [hx]

omit hNL in
/-- V.3.4: each nondistinguished right-coset representative uses a different prime. -/
theorem inverseConjugatePrime_ne_of_transversal (T : Finset (L ≃ₐ[K] L))
    (hT : Subgroup.IsComplement
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal : Set (L ≃ₐ[K] L))
      (T : Set (L ≃ₐ[K] L))) (h1 : 1 ∈ T) (τ : L ≃ₐ[K] L)
    (hτ : τ ∈ T) (hτ1 : τ ≠ 1) : inverseConjugatePrime L τ.toRingEquiv w ≠ w := by
  intro h
  have hsmul : τ⁻¹ • w.asIdeal = w.asIdeal := by
    rw [← inverseConjugatePrime_asIdeal_inv_smul K L w τ, h]
  have hD : τ⁻¹ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal :=
    MulAction.mem_stabilizer_iff.mpr hsmul
  have hD' : τ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
    simpa using Subgroup.inv_mem _ hD
  exact hτ1 ((rightTransversal_mem_subgroup_iff _ T hT h1 τ hτ).mp hD')

/-- V.3.4: approximate the selected target at one prime and 1 at the other inverse-conjugate
primes. -/
theorem exists_coset_product_localRay_approx (T : Finset (L ≃ₐ[K] L))
    (hT : Subgroup.IsComplement
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal : Set (L ≃ₐ[K] L))
      (T : Set (L ≃ₐ[K] L))) (h1 : 1 ∈ T)
    (β : (w.adicCompletion L)ˣ) (s : ℕ) (hs : 0 < s) :
    ∃ γ : Lˣ, (∏ τ ∈ T, completionUnitMap L w (Units.map τ.toMonoidHom γ)) * β⁻¹ ∈
      localFieldUnitFiltration L w s := by
  classical
  let S := T.image (fun τ : L ≃ₐ[K] L => inverseConjugatePrime L τ.toRingEquiv w)
  have hwS : w ∈ S := Finset.mem_image.mpr ⟨1, h1, inverseConjugatePrime_one L w⟩
  obtain ⟨γ, hγw, hγS⟩ := exists_selected_localRay_approx L S w hwS β s
  refine ⟨γ, ?_⟩
  have key := prod_mul_inv_mem_of_forall T (localFieldUnitFiltration L w s)
    (fun τ => completionUnitMap L w (Units.map τ.toMonoidHom γ))
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
      exact conjugate_localRay_mem L τ.toRingEquiv w γ s hs hmem
end Transversal

namespace LocalCyclic
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable [hGalois : IsGalois K L]
include hGalois
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
attribute [local instance] localAlgebra localFinite

omit hGalois in
/-- Positive residue degree makes a local norm a unit exactly when its argument is a unit. -/
theorem localNorm_valuation_eq_one_iff (x : (w.adicCompletion L)ˣ) :
    Valued.v (Algebra.norm (v.adicCompletion K) (x : w.adicCompletion L)) = 1 ↔
      Valued.v (x : w.adicCompletion L) = 1 := by
  rw [valuation_local_norm K L v w (x : w.adicCompletion L)]
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hf0 : Ideal.inertiaDeg v.asIdeal w.asIdeal ≠ 0 :=
    (Ideal.inertiaDeg_pos v.asIdeal w.asIdeal).ne'
  rw [pow_eq_one_iff, or_iff_left hf0]

/-- The image of the determinant norm restricted to completed integral units. -/
def unitNormGroup : Subgroup (v.adicCompletion K)ˣ :=
  (localFieldUnitFiltration L w 0).map
    (Units.map (Algebra.norm (v.adicCompletion K) :
      w.adicCompletion L →* v.adicCompletion K))

omit hGalois in
/-- The norm of a local integral unit is a local integral unit. -/
theorem unitNormGroup_le_units :
    unitNormGroup K L v w ≤ localFieldUnitFiltration K v 0 := by
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, mem_localFieldUnitFiltration_zero_iff] at hy
  rw [mem_localFieldUnitFiltration_zero_iff]
  exact (localNorm_valuation_eq_one_iff K L v w y).mpr hy

omit hGalois in
/-- A local field norm has a unit preimage exactly when its value is a unit. -/
theorem unitNormGroup_eq_inf_norm :
    unitNormGroup K L v w = localNormGroup K L v w ⊓ localFieldUnitFiltration K v 0 := by
  apply le_antisymm
  · intro u hu
    refine ⟨?_, unitNormGroup_le_units K L v w hu⟩
    obtain ⟨y, -, rfl⟩ := hu
    exact ⟨y, rfl⟩
  · intro u hu
    rw [Subgroup.mem_inf] at hu
    obtain ⟨⟨x, rfl⟩, hu⟩ := hu
    refine ⟨x, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_localFieldUnitFiltration_zero_iff]
    rw [mem_localFieldUnitFiltration_zero_iff] at hu
    exact (localNorm_valuation_eq_one_iff K L v w x).mp hu

omit hGalois in
/-- Norm continuity gives an explicit input radius for any prescribed output radius. -/
theorem continuous_norm_precision (β : w.adicCompletion L) (N : ℤ) :
    ∃ M : ℤ, ∀ x : w.adicCompletion L,
      Valued.v (x - β) < WithZero.exp (-M) →
        Valued.v (Algebra.norm (v.adicCompletion K) x -
          Algebra.norm (v.adicCompletion K) (β : w.adicCompletion L)) <
            WithZero.exp (-N) := by
  have hball := completion_small_ball_mem_nhds K v
    (Algebra.norm (v.adicCompletion K) β) N
  have hpre := (continuous_local_norm K L v w).continuousAt.preimage_mem_nhds hball
  obtain ⟨M, hM⟩ := exists_valued_small_ball_subset β _ hpre
  exact ⟨M, fun x hx => hM hx⟩

omit hGalois in
/-- A deep enough upstairs principal-unit error has the desired downstairs norm error. -/
theorem exists_localNorm_ray_depth (β : (w.adicCompletion L)ˣ) (t : ℕ) :
    ∃ s : ℕ, 0 < s ∧ ∀ x : (w.adicCompletion L)ˣ,
      x * β⁻¹ ∈ localFieldUnitFiltration L w s →
        (Units.map (Algebra.norm (v.adicCompletion K) :
          w.adicCompletion L →* v.adicCompletion K) x) *
        (Units.map (Algebra.norm (v.adicCompletion K) :
          w.adicCompletion L →* v.adicCompletion K) β)⁻¹ ∈
          localFieldUnitFiltration K v t := by
  obtain ⟨N, hN⟩ := exists_precision_for_localRay K v t
    (Units.map (Algebra.norm (v.adicCompletion K) :
      w.adicCompletion L →* v.adicCompletion K) β)
  obtain ⟨M, hM⟩ := continuous_norm_precision K L v w (β : w.adicCompletion L) N
  obtain ⟨s, hs, hs'⟩ := exists_localRay_depth_for_error L w β M
  exact ⟨s, hs, fun x hx => hN _ (hM _ (hs' x hx))⟩

/-- Lift the fixed-w coset norm identity to the actual unit groups. -/
theorem global_norm_coset_product_units (T : Finset (L ≃ₐ[K] L))
    (hT : Subgroup.IsComplement
      (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal : Set (L ≃ₐ[K] L))
      (T : Set (L ≃ₐ[K] L))) (γ : Lˣ) :
    completionUnitMap K v (Units.map (Algebra.norm K : L →* K) γ) =
      Units.map (Algebra.norm (v.adicCompletion K) : w.adicCompletion L →* v.adicCompletion K)
        (∏ τ ∈ T, completionUnitMap L w (Units.map τ.toMonoidHom γ)) := by
  apply Units.ext
  simp only [completionUnitMap_apply, Units.coe_map, Units.coe_prod]
  exact completion_global_norm_coset_product K L v w T hT (γ : L)

/-- V.3.4: every local norm can be approximated by a global norm modulo the chosen filtration. -/
theorem exists_globalNorm_localRay_approx (β : (w.adicCompletion L)ˣ) (t : ℕ) :
    ∃ γ : Lˣ,
      completionUnitMap K v (Units.map (Algebra.norm K : L →* K) γ) *
        (Units.map (Algebra.norm (v.adicCompletion K) :
          w.adicCompletion L →* v.adicCompletion K) β)⁻¹ ∈
          localFieldUnitFiltration K v t := by
  obtain ⟨T, hT, h1⟩ := exists_finset_rightTransversal_one (L ≃ₐ[K] L)
    (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)
  obtain ⟨s, hs, hs'⟩ := exists_localNorm_ray_depth K L v w β t
  obtain ⟨γ, hγ⟩ := exists_coset_product_localRay_approx K L w T hT h1 β s hs
  refine ⟨γ, ?_⟩
  rw [global_norm_coset_product_units K L v w T hT γ]
  exact hs' _ hγ

/-- A global norm that is a unit at v maps into the local integral-unit norm group. -/
theorem completion_globalNorm_mem_unitNormGroup (a : Kˣ)
    (ha : a ∈ elementNormGroup K L) (hua : a ∈ globalValuationUnitGroup K v) :
    completionUnitMap K v a ∈ unitNormGroup K L v w := by
  rw [unitNormGroup_eq_inf_norm]
  obtain ⟨y, rfl⟩ := ha
  exact ⟨global_norm_mem_localNormGroup K L v w y, hua⟩

/-- The global norm image is contained in the local unit norm image in the unit-ray quotient. -/
theorem globalNorm_unitRay_image_le (t : ℕ) :
    ((elementNormGroup K L).subgroupOf (globalValuationUnitGroup K v)).map
      (globalUnitRayMap K v t) ≤
        ((unitNormGroup K L v w).subgroupOf (localFieldUnitFiltration K v 0)).map
          (QuotientGroup.mk' ((localFieldUnitFiltration K v t).subgroupOf
            (localFieldUnitFiltration K v 0))) := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨globalUnitAtMap K v a,
    completion_globalNorm_mem_unitNormGroup K L v w a ha a.2, rfl⟩

/-- V.3.4: simultaneous approximation gives the reverse inclusion of the norm images. -/
theorem unitNorm_unitRay_image_le (t : ℕ) :
    ((unitNormGroup K L v w).subgroupOf (localFieldUnitFiltration K v 0)).map
      (QuotientGroup.mk' ((localFieldUnitFiltration K v t).subgroupOf
        (localFieldUnitFiltration K v 0))) ≤
          ((elementNormGroup K L).subgroupOf (globalValuationUnitGroup K v)).map
            (globalUnitRayMap K v t) := by
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨β, -, hβb⟩ := hb
  obtain ⟨γ, hγ⟩ := exists_globalNorm_localRay_approx K L v w β t
  rw [Subgroup.coe_subtype] at hβb
  rw [hβb] at hγ
  have ha0 : Units.map (Algebra.norm K : L →* K) γ ∈ globalValuationUnitGroup K v := by
    have h := Subgroup.mul_mem _ (localFieldUnitFiltration_le_zero K v t hγ) b.2
    rwa [inv_mul_cancel_right] at h
  refine ⟨⟨_, ha0⟩, ⟨γ, rfl⟩, ?_⟩
  rw [globalUnitRayMap_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h := Subgroup.inv_mem _ hγ
  rw [mul_inv_rev, inv_inv, mul_comm] at h
  exact h

/-- The exact image equality underlying the source local quotient comparison. -/
theorem globalNorm_unitRay_image (t : ℕ) :
    ((elementNormGroup K L).subgroupOf (globalValuationUnitGroup K v)).map
      (globalUnitRayMap K v t) =
        ((unitNormGroup K L v w).subgroupOf (localFieldUnitFiltration K v 0)).map
          (QuotientGroup.mk' ((localFieldUnitFiltration K v t).subgroupOf
            (localFieldUnitFiltration K v 0))) := by
  exact le_antisymm (globalNorm_unitRay_image_le K L v w t) (unitNorm_unitRay_image_le K L v w t)
end LocalCyclic
end Cox.ClassFieldTheory
