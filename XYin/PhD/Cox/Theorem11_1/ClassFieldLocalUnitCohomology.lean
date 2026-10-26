/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormalBasis
import XYin.PhD.Cox.Theorem11_1.ClassFieldFieldUnits
import XYin.PhD.Cox.Theorem11_1.ClassFieldTateDifference
import XYin.PhD.Cox.Theorem11_1.ClassFieldGlobalNormIndexAssembly

/-! # Local-unit H¹ in Janusz V.3.8

The source's difference quotient and the normalized valuation compute the index e.
-/
open NumberField IsDedekindDomain
open scoped WithZero
noncomputable section
namespace Cox.ClassFieldTheory.LocalCyclic
open Cox.CyclicCohomology
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
attribute [local instance] localAlgebra localFinite

/-- A completed automorphism preserves the actual normalized valuation homomorphism. -/
theorem localUnitValuation_aut
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (x : (w.adicCompletion L)ˣ) :
    localUnitValuation L w (Units.map σ.toRingHom.toMonoidHom x) =
      localUnitValuation L w x := by
  apply Multiplicative.toAdd.injective
  apply WithZero.exp_injective
  rw [localUnitValuation_apply, localUnitValuation_apply, Units.coe_map]
  exact automorphism_preserves_valuation K L v w σ (x : w.adicCompletion L)

/-- The additive integral submodule of completed field units of valuation zero. -/
def unitSubmodule : Submodule ℤ (Additive (w.adicCompletion L)ˣ) :=
  (localFieldUnitFiltration L w 0).toAddSubgroup.toIntSubmodule

/-- The valuation-zero subgroup is stable under the local Galois action. -/
theorem unitSubmodule_stable
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    unitSubmodule L w ≤ (unitSubmodule L w).comap
      ((Representation.ofMulDistribMulAction
        (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
        (w.adicCompletion L)ˣ) σ) := by
  intro x hx
  rw [Submodule.mem_comap]
  change Additive.toMul x ∈ localFieldUnitFiltration L w 0 at hx
  change σ • Additive.toMul x ∈ localFieldUnitFiltration L w 0
  have hσx : σ • Additive.toMul x =
      Units.map σ.toRingHom.toMonoidHom (Additive.toMul x) := Units.ext rfl
  rw [localFieldUnitFiltration_zero_eq_ker, MonoidHom.mem_ker] at hx ⊢
  rw [hσx, localUnitValuation_aut K L v w σ, hx]

/-- The actual local-unit representation, not an assumed cohomological model. -/
def unitRepresentation :
    Representation ℤ (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
      (unitSubmodule L w) :=
  (Representation.ofMulDistribMulAction
    (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (w.adicCompletion L)ˣ).subrepresentation (unitSubmodule L w)
      (unitSubmodule_stable K L v w)

/-- Every difference of completed field units has valuation zero. -/
theorem fieldUnitDifference_range_le_units
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    LinearMap.range
      ((Representation.ofMulDistribMulAction
        (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
        (w.adicCompletion L)ˣ) σ - LinearMap.id) ≤ unitSubmodule L w := by
  rintro _ ⟨x, rfl⟩
  change (σ • Additive.toMul x) / Additive.toMul x ∈ localFieldUnitFiltration L w 0
  have hσx : σ • Additive.toMul x =
      Units.map σ.toRingHom.toMonoidHom (Additive.toMul x) := Units.ext rfl
  rw [localFieldUnitFiltration_zero_eq_ker, MonoidHom.mem_ker, map_div, hσx,
    localUnitValuation_aut K L v w σ, div_self']

/-- Embedding a base unit multiplies its normalized valuation by the ramification index. -/
theorem localUnitValuation_fieldUnitEmbedding (x : (v.adicCompletion K)ˣ) :
    localUnitValuation L w (fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L) x) =
      localUnitValuation K v x ^ Ideal.ramificationIdx v.asIdeal w.asIdeal := by
  apply Multiplicative.toAdd.injective
  apply WithZero.exp_injective
  rw [localUnitValuation_apply, toAdd_pow, WithZero.exp_nsmul, localUnitValuation_apply]
  exact completion_valuation_map K L v w (x : v.adicCompletion K)

/-- The valuation image of the base field is exactly eℤ in multiplicative notation. -/
theorem fieldUnitEmbedding_map_valuation :
    (fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L)).range.map
      (localUnitValuation L w) =
        Subgroup.zpowers
          (Multiplicative.ofAdd (Ideal.ramificationIdx v.asIdeal w.asIdeal : ℤ)) := by
  rw [← MonoidHom.range_comp]
  ext z
  rw [MonoidHom.mem_range, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨Multiplicative.toAdd (localUnitValuation K v x), ?_⟩
    rw [MonoidHom.comp_apply, localUnitValuation_fieldUnitEmbedding]
    apply Multiplicative.toAdd.injective
    rw [toAdd_zpow, toAdd_pow, toAdd_ofAdd, smul_eq_mul, nsmul_eq_mul, mul_comm]
  · rintro ⟨k, rfl⟩
    obtain ⟨x, hx⟩ := localUnitValuation_surjective K v (Multiplicative.ofAdd k)
    refine ⟨x, ?_⟩
    rw [MonoidHom.comp_apply, localUnitValuation_fieldUnitEmbedding, hx]
    apply Multiplicative.toAdd.injective
    rw [toAdd_zpow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, smul_eq_mul, nsmul_eq_mul, mul_comm]

/-- Quotienting upstairs units by base-field elements and valuation-zero units has order e. -/
theorem fieldUnitEmbedding_sup_units_index :
    ((fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L)).range ⊔
      localFieldUnitFiltration L w 0).index =
        Ideal.ramificationIdx v.asIdeal w.asIdeal := by
  rw [localFieldUnitFiltration_zero_eq_ker,
    index_sup_ker_eq_index_map_of_surjective _ _ (localUnitValuation_surjective L w),
    fieldUnitEmbedding_map_valuation, index_zpowers_multiplicative_int]

variable [hLocalGalois : IsGalois (v.adicCompletion K) (w.adicCompletion L)]
include hLocalGalois

/-- Fixed completed field units form exactly the embedded base-field subgroup. -/
theorem fixedFieldUnitSubmodule_eq_range
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    LinearMap.ker
      ((Representation.ofMulDistribMulAction
        (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
        (w.adicCompletion L)ˣ) σ - LinearMap.id) =
      (fieldUnitEmbedding (v.adicCompletion K)
        (w.adicCompletion L)).range.toAddSubgroup.toIntSubmodule := by
  ext a
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := fixed_fieldUnit_descends (v.adicCompletion K) (w.adicCompletion L) σ hσ
      ⟨a, ha⟩
    exact ⟨x, (congrArg Additive.toMul hx).symm⟩
  · rintro ⟨x, hx⟩
    have h := fieldUnitEmbedding_mem_fixed (v.adicCompletion K) (w.adicCompletion L) σ
      (Additive.ofMul x)
    have hax : (fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L)).toAdditive
        (Additive.ofMul x) = a := congrArg Additive.ofMul hx
    rwa [hax] at h

/-- Hilbert90 and the difference-class map give precisely the source's field-unit quotient. -/
theorem unit_tateOne_equiv_fieldQuotient
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Nonempty (tateOne (unitRepresentation K L v w) σ ≃+
      Additive ((w.adicCompletion L)ˣ ⧸
        ((fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L)).range ⊔
          localFieldUnitFiltration L w 0))) := by
  haveI := tateOne_fieldUnits_subsingleton (v.adicCompletion K) (w.adicCompletion L) σ hσ
  have hFull := range_difference_eq_ker_norm_of_subsingleton
    (Representation.ofMulDistribMulAction
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) (w.adicCompletion L)ˣ) σ
  obtain ⟨e⟩ := tateOne_subrepresentation_equiv_quotient _ σ (unitSubmodule L w)
    (unitSubmodule_stable K L v w) (fieldUnitDifference_range_le_units K L v w σ) hFull
  have hsup : unitSubmodule L w ⊔ LinearMap.ker ((Representation.ofMulDistribMulAction
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) (w.adicCompletion L)ˣ) σ -
        LinearMap.id) =
      ((fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L)).range ⊔
        localFieldUnitFiltration L w 0).toAddSubgroup.toIntSubmodule := by
    rw [fixedFieldUnitSubmodule_eq_range K L v w σ hσ, unitSubmodule, ← OrderIso.map_sup,
      ← OrderIso.map_sup, sup_comm]
  exact ⟨e.trans ((Submodule.quotEquivOfEq _ _ hsup).toAddEquiv.trans
    (additiveIntQuotientEquiv _))⟩

/-- Hilbert 90 and the valuation quotient identify local-unit H¹ as an e-element group. -/
theorem unit_tateOne_card
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Nat.card (tateOne (unitRepresentation K L v w) σ) =
      Ideal.ramificationIdx v.asIdeal w.asIdeal := by
  obtain ⟨e⟩ := unit_tateOne_equiv_fieldQuotient K L v w σ hσ
  rw [Nat.card_congr e.toEquiv, ← fieldUnitEmbedding_sup_units_index K L v w, Subgroup.index]
  rfl

end Cox.ClassFieldTheory.LocalCyclic
