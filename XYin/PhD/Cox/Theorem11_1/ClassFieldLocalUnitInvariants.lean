/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalUnitCohomology

/-! # Local-unit invariants and actual norm classes

Janusz V.3.7–3.8 identifies the zeroth Tate quotient with base units modulo
norms of upper units. The chosen invariant equivalence retains its field value.
-/
open NumberField IsDedekindDomain
noncomputable section
namespace Cox.ClassFieldTheory.LocalCyclic
open Cox.CyclicCohomology
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
attribute [local instance] localAlgebra localFinite

/-- An embedded base field unit is integral upstairs exactly when it is integral downstairs. -/
theorem fieldUnitEmbedding_mem_units_iff (x : (v.adicCompletion K)ˣ) :
    fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L) x ∈
      localFieldUnitFiltration L w 0 ↔ x ∈ localFieldUnitFiltration K v 0 := by
  have he : Ideal.ramificationIdx v.asIdeal w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot
  rw [localFieldUnitFiltration_zero_eq_ker, localFieldUnitFiltration_zero_eq_ker,
    MonoidHom.mem_ker, MonoidHom.mem_ker, localUnitValuation_fieldUnitEmbedding, pow_eq_one_iff,
    or_iff_left he]

/-- A fixed vector of the restricted representation is fixed in the ambient one. -/
theorem unitFixed_mem_ker
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (a : LinearMap.ker (unitRepresentation K L v w σ - LinearMap.id)) :
    ((a : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ) ∈
      LinearMap.ker ((Representation.ofMulDistribMulAction
        (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) (w.adicCompletion L)ˣ) σ -
          LinearMap.id) := by
  rw [LinearMap.mem_ker]
  exact congrArg Subtype.val (LinearMap.mem_ker.mp a.2)

/-- Embedded valuation-zero base units, as fixed vectors of the restricted representation. -/
def unitFixedEmbedding
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    Additive (localFieldUnitFiltration K v 0) →+
      LinearMap.ker (unitRepresentation K L v w σ - LinearMap.id) where
  toFun y := ⟨⟨Additive.ofMul (fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L)
      ((Additive.toMul y : localFieldUnitFiltration K v 0) : (v.adicCompletion K)ˣ)),
      (fieldUnitEmbedding_mem_units_iff K L v w _).mpr (Additive.toMul y).2⟩, by
    have h := fieldUnitEmbedding_mem_fixed (v.adicCompletion K) (w.adicCompletion L) σ
      (Additive.ofMul ((Additive.toMul y : localFieldUnitFiltration K v 0) :
        (v.adicCompletion K)ˣ))
    rw [LinearMap.mem_ker] at h ⊢
    exact Subtype.ext h⟩
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_add' y z := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- The embedding of valuation-zero base units is injective. -/
theorem unitFixedEmbedding_injective
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    Function.Injective (unitFixedEmbedding K L v w σ) := by
  intro y z hyz
  have h1 := congrArg (fun a : LinearMap.ker (unitRepresentation K L v w σ - LinearMap.id) =>
    Additive.toMul ((a : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ)) hyz
  exact Additive.toMul.injective (Subtype.ext
    (fieldUnitEmbedding_injective (v.adicCompletion K) (w.adicCompletion L) h1))

variable [hLocalGalois : IsGalois (v.adicCompletion K) (w.adicCompletion L)]
include hLocalGalois

/-- Fixed-field descent makes the embedding of valuation-zero base units surjective. -/
theorem unitFixedEmbedding_surjective
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Function.Surjective (unitFixedEmbedding K L v w σ) := by
  intro a
  obtain ⟨x, hx⟩ := fixed_fieldUnit_descends (v.adicCompletion K) (w.adicCompletion L) σ hσ
    ⟨_, unitFixed_mem_ker K L v w σ a⟩
  have hx0 : x ∈ localFieldUnitFiltration K v 0 := by
    rw [← fieldUnitEmbedding_mem_units_iff K L v w]
    have h := (a : unitSubmodule L w).2
    change Additive.toMul ((a : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ) ∈
      localFieldUnitFiltration L w 0 at h
    rwa [show ((a : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ) =
      Additive.ofMul (fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L) x) from hx,
      toMul_ofMul] at h
  exact ⟨Additive.ofMul ⟨x, hx0⟩, Subtype.ext (Subtype.ext hx.symm)⟩

/-- Restrict fixed-field descent to valuation-zero units, retaining its actual embedded value. -/
theorem exists_unitFixedEquiv
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ∃ e : LinearMap.ker (unitRepresentation K L v w σ - LinearMap.id) ≃ₗ[ℤ]
        Additive (localFieldUnitFiltration K v 0),
      ∀ a, fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L)
        ((e a).toMul : (v.adicCompletion K)ˣ) =
          ((a : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ).toMul := by
  have hE := LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective
    (unitFixedEmbedding K L v w σ).toIntLinearMap
    ⟨unitFixedEmbedding_injective K L v w σ, unitFixedEmbedding_surjective K L v w σ hσ⟩)
  refine ⟨(LinearEquiv.ofBijective (unitFixedEmbedding K L v w σ).toIntLinearMap
    ⟨unitFixedEmbedding_injective K L v w σ, unitFixedEmbedding_surjective K L v w σ hσ⟩).symm,
    fun a => ?_⟩
  exact congrArg (fun b : LinearMap.ker (unitRepresentation K L v w σ - LinearMap.id) =>
    Additive.toMul ((b : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ)) (hE a)

/-- The same invariant equivalence used in the norm-range calculation. -/
def unitFixedEquiv
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    LinearMap.ker (unitRepresentation K L v w σ - LinearMap.id) ≃ₗ[ℤ]
      Additive (localFieldUnitFiltration K v 0) :=
  Classical.choose (exists_unitFixedEquiv K L v w σ hσ)

/-- The chosen invariant equivalence has the original completed field-unit value. -/
theorem unitFixedEquiv_apply
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (a : LinearMap.ker (unitRepresentation K L v w σ - LinearMap.id)) :
    fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L)
      ((unitFixedEquiv K L v w σ hσ a).toMul : (v.adicCompletion K)ˣ) =
        ((a : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ).toMul := by
  exact Classical.choose_spec (exists_unitFixedEquiv K L v w σ hσ) a

/-- The actual invariant equivalence sends the group norm range to norms of local integral units. -/
theorem unitFixedEquiv_normRange
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ((LinearMap.range (unitRepresentation K L v w).norm).comap
      (LinearMap.ker (unitRepresentation K L v w σ - LinearMap.id)).subtype).map
        (unitFixedEquiv K L v w σ hσ).toLinearMap =
      ((unitNormGroup K L v w).subgroupOf
        (localFieldUnitFiltration K v 0)).toAddSubgroup.toIntSubmodule := by
  have hnorm : ∀ b : unitSubmodule L w,
      (((unitRepresentation K L v w).norm b : unitSubmodule L w) :
        Additive (w.adicCompletion L)ˣ) =
        Additive.ofMul (fieldUnitEmbedding (v.adicCompletion K) (w.adicCompletion L)
          (Units.map (Algebra.norm (v.adicCompletion K))
            (Additive.toMul (b : Additive (w.adicCompletion L)ˣ)))) := by
    intro b
    have h1 := subrepresentation_norm_coe (Representation.ofMulDistribMulAction
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) (w.adicCompletion L)ˣ)
      (unitSubmodule L w) (unitSubmodule_stable K L v w) b
    have h2 := fieldUnit_norm_formula (v.adicCompletion K) (w.adicCompletion L)
      (Additive.toMul (b : Additive (w.adicCompletion L)ˣ))
    rw [ofMul_toMul] at h2
    exact h1.trans h2
  ext k
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨a, ⟨b, hb⟩, rfl⟩
    have h3 : ((Additive.toMul (unitFixedEquiv K L v w σ hσ a) : localFieldUnitFiltration K v 0) :
        (v.adicCompletion K)ˣ) = Units.map (Algebra.norm (v.adicCompletion K))
          (Additive.toMul (b : Additive (w.adicCompletion L)ˣ)) :=
      fieldUnitEmbedding_injective (v.adicCompletion K) (w.adicCompletion L)
        ((unitFixedEquiv_apply K L v w σ hσ a).trans
          ((congrArg (fun z : Additive (w.adicCompletion L)ˣ => Additive.toMul z)
            (congrArg Subtype.val hb.symm)).trans (congrArg Additive.toMul (hnorm b))))
    exact (congrArg (fun z => z ∈ unitNormGroup K L v w) h3).mpr ⟨_, b.2, rfl⟩
  · intro hk
    obtain ⟨u, hu, huk⟩ := hk
    have hbfix : (unitRepresentation K L v w).norm ⟨Additive.ofMul u, hu⟩ ∈
        LinearMap.ker (unitRepresentation K L v w σ - LinearMap.id) :=
      range_norm_le_ker_difference _ σ ⟨⟨Additive.ofMul u, hu⟩, rfl⟩
    refine ⟨⟨_, hbfix⟩, ⟨⟨Additive.ofMul u, hu⟩, rfl⟩, ?_⟩
    have h3 : ((Additive.toMul (unitFixedEquiv K L v w σ hσ ⟨_, hbfix⟩) :
        localFieldUnitFiltration K v 0) : (v.adicCompletion K)ˣ) =
          Units.map (Algebra.norm (v.adicCompletion K)) u :=
      fieldUnitEmbedding_injective (v.adicCompletion K) (w.adicCompletion L)
        ((unitFixedEquiv_apply K L v w σ hσ ⟨_, hbfix⟩).trans
          (congrArg Additive.toMul (hnorm ⟨Additive.ofMul u, hu⟩)))
    exact Additive.toMul.injective (Subtype.ext (h3.trans huk))

/-- The local-unit norm quotient is the genuine invariant/norm Tate quotient. -/
theorem unit_tateZero_equiv_normQuotient
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Nonempty (tateZero (unitRepresentation K L v w) σ ≃+
      Additive ((localFieldUnitFiltration K v 0) ⧸
        (unitNormGroup K L v w).subgroupOf (localFieldUnitFiltration K v 0))) := by
  exact ⟨(Submodule.Quotient.equiv _ _ (unitFixedEquiv K L v w σ hσ)
    (unitFixedEquiv_normRange K L v w σ hσ)).toAddEquiv.trans (additiveIntQuotientEquiv _)⟩

end Cox.ClassFieldTheory.LocalCyclic
