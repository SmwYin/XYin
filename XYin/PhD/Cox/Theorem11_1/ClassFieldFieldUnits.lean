/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicModules
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicCocycle

/-! # Janusz V.2.1 field-unit Tate identifications

The invariant/base-unit equivalence and its quotient equivalence are actual maps.
Their representatives and transported norm subgroups are stated explicitly.
-/

noncomputable section
namespace Cox.CyclicCohomology

/-- The integral submodule quotient and additive form of the multiplicative quotient
are definitionally the same additive group. -/
def additiveIntQuotientEquiv {M : Type*} [CommGroup M] (H : Subgroup M) :
    (Additive M ⧸ H.toAddSubgroup.toIntSubmodule) ≃+ Additive (M ⧸ H) :=
  AddEquiv.refl _

/-- Fixing a generator fixes every element of its generated group action. -/
theorem fixed_of_generator {G X : Type*} [Group G] [MulAction G X]
    (g : G) (hg : ∀ γ : G, γ ∈ Subgroup.zpowers g) (x : X) (hx : g • x = x) :
    ∀ γ : G, γ • x = x := by
  intro γ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg γ)
  have hmem : g ∈ MulAction.stabilizer G x := hx
  exact (MulAction.stabilizer G x).zpow_mem hmem k

end Cox.CyclicCohomology

namespace Cox.ClassFieldTheory
open NumberField IsDedekindDomain
open Cox.CyclicCohomology
open scoped nonZeroDivisors
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The actual embedding on nonzero base-field elements. -/
def fieldUnitEmbedding : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom

/-- The unit embedding is injective because the field embedding is injective. -/
theorem fieldUnitEmbedding_injective : Function.Injective (fieldUnitEmbedding K L) := by
  exact Units.map_injective (f := (algebraMap K L).toMonoidHom) (algebraMap K L).injective

/-- Embedded base units lie in the actual generator-difference kernel. -/
theorem fieldUnitEmbedding_mem_fixed (σ : L ≃ₐ[K] L) (x : Additive Kˣ) :
    (fieldUnitEmbedding K L).toAdditive x ∈
      LinearMap.ker (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ σ - LinearMap.id) := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  change Additive.ofMul (σ • fieldUnitEmbedding K L (Additive.toMul x)) =
    Additive.ofMul (fieldUnitEmbedding K L (Additive.toMul x))
  congr 1
  ext
  simp [fieldUnitEmbedding, AlgEquiv.commutes]

/-- The actual base-unit embedding, with codomain restricted to the invariant module. -/
def fixedFieldUnitMap (σ : L ≃ₐ[K] L) : Additive Kˣ →ₗ[ℤ]
    LinearMap.ker (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ σ - LinearMap.id) :=
  (fieldUnitEmbedding K L).toAdditive.toIntLinearMap.codRestrict _
    (fieldUnitEmbedding_mem_fixed K L σ)

/-- Restricting the codomain preserves injectivity. -/
theorem fixedFieldUnitMap_injective (σ : L ≃ₐ[K] L) :
    Function.Injective (fixedFieldUnitMap K L σ) := by
  intro x y h
  have h' := congrArg Subtype.val h
  have h'' : fieldUnitEmbedding K L (Additive.toMul x) =
      fieldUnitEmbedding K L (Additive.toMul y) :=
    congrArg Additive.toMul h'
  exact Additive.toMul.injective (fieldUnitEmbedding_injective K L h'')

variable [FiniteDimensional K L] [hGalois : IsGalois K L]
include hGalois

/-- A generator-fixed unit descends to the base field, using the Galois fixed-field theorem. -/
theorem fixed_fieldUnit_descends (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (a : LinearMap.ker
      (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ σ - LinearMap.id)) :
    ∃ x : Kˣ, (a : Additive Lˣ) = Additive.ofMul (fieldUnitEmbedding K L x) := by
  set u : Lˣ := Additive.toMul (a : Additive Lˣ) with hu
  have hfix : σ • u = u := by
    have h := LinearMap.mem_ker.mp a.2
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h
    exact congrArg Additive.toMul h
  have hall := fixed_of_generator σ hσ u hfix
  have hmem : (u : L) ∈ (⊥ : IntermediateField K L) := by
    rw [IsGalois.mem_bot_iff_fixed]
    intro τ
    exact congrArg Units.val (hall τ)
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hmem
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact u.ne_zero hy.symm
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Additive.toMul.injective
  rw [toMul_ofMul]
  ext
  exact hy.symm

/-- Fixed-unit descent makes the actual invariant map surjective. -/
theorem fixedFieldUnitMap_surjective (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Function.Surjective (fixedFieldUnitMap K L σ) := by
  intro a
  obtain ⟨x, hx⟩ := fixed_fieldUnit_descends K L σ hσ a
  exact ⟨Additive.ofMul x, Subtype.ext hx.symm⟩

/-- The actual inverse of the bijective embedding from base units to fixed units. -/
def fixedFieldUnitsEquiv (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    LinearMap.ker
        (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ σ - LinearMap.id) ≃ₗ[ℤ]
      Additive Kˣ :=
  (LinearEquiv.ofBijective (fixedFieldUnitMap K L σ)
    ⟨fixedFieldUnitMap_injective K L σ, fixedFieldUnitMap_surjective K L σ hσ⟩).symm

/-- The fixed-unit equivalence sends an embedded base unit to that same base unit. -/
theorem fixedFieldUnitsEquiv_apply (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (x : Additive Kˣ) :
    fixedFieldUnitsEquiv K L σ hσ (fixedFieldUnitMap K L σ x) = x := by
  exact (LinearEquiv.ofBijective _ _).symm_apply_apply x

/-- The representation norm is the embedded field norm, as an equality of actual units. -/
theorem fieldUnit_norm_formula (x : Lˣ) :
    (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ).norm (Additive.ofMul x) =
      Additive.ofMul (fieldUnitEmbedding K L (Units.map (Algebra.norm K) x)) := by
  apply Additive.toMul.injective
  rw [Representation.norm, LinearMap.sum_apply, toMul_sum, toMul_ofMul]
  ext
  rw [Units.coe_prod]
  change ∏ τ : L ≃ₐ[K] L, ((τ • x : Lˣ) : L) = algebraMap K L (Algebra.norm K (x : L))
  rw [Algebra.norm_eq_prod_automorphisms]
  rfl

/-- The actual invariant equivalence takes the Tate norm submodule to actual element norms. -/
theorem fixedFieldUnitsEquiv_normRange (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ((LinearMap.range
          (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ).norm).comap
        (LinearMap.ker
          (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ σ - LinearMap.id)).subtype).map
        (fixedFieldUnitsEquiv K L σ hσ).toLinearMap =
      (elementNormGroup K L).toAddSubgroup.toIntSubmodule := by
  ext k
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨y, hy⟩ := ha
    have ha' : a = fixedFieldUnitMap K L σ
        (Additive.ofMul (Units.map (Algebra.norm K : L →* K) (Additive.toMul y))) := by
      apply Subtype.ext
      have h := fieldUnit_norm_formula K L (Additive.toMul y)
      rw [ofMul_toMul] at h
      exact hy.symm.trans h
    rw [ha']
    change fixedFieldUnitsEquiv K L σ hσ (fixedFieldUnitMap K L σ _) ∈ _
    rw [fixedFieldUnitsEquiv_apply]
    exact ⟨Additive.toMul y, rfl⟩
  · intro hk
    obtain ⟨z, hz⟩ := hk
    refine ⟨fixedFieldUnitMap K L σ k, Submodule.mem_comap.mpr
      (LinearMap.mem_range.mpr ⟨Additive.ofMul z, ?_⟩), fixedFieldUnitsEquiv_apply K L σ hσ k⟩
    rw [fieldUnit_norm_formula, hz]
    rfl

/-- The actual quotient equivalence induced by fixed-unit descent and norm transport. -/
def fieldUnitsTateEquiv (σ : L ≃ₐ[K] L) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    tateZero (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ ≃+
      Additive (Kˣ ⧸ elementNormGroup K L) :=
  (Submodule.Quotient.equiv _ _ (fixedFieldUnitsEquiv K L σ hσ)
    (fixedFieldUnitsEquiv_normRange K L σ hσ)).toAddEquiv.trans
      (additiveIntQuotientEquiv (elementNormGroup K L))

/-- The induced quotient equivalence has the source's representative formula. -/
theorem fieldUnitsTateEquiv_apply (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (x : Kˣ)
    (a : LinearMap.ker
      (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ σ - LinearMap.id))
    (ha : (a : Additive Lˣ) = Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x)) :
    fieldUnitsTateEquiv K L σ hσ (zeroClass _ σ a) =
      Additive.ofMul (QuotientGroup.mk x) := by
  have ha' : a = fixedFieldUnitMap K L σ (Additive.ofMul x) := Subtype.ext ha
  subst ha'
  change Submodule.Quotient.mk
    (fixedFieldUnitsEquiv K L σ hσ (fixedFieldUnitMap K L σ (Additive.ofMul x))) = _
  rw [fixedFieldUnitsEquiv_apply]
  rfl

/-- Janusz V.2.1(b), with the representative condition fixing the actual norm quotient map. -/
theorem exists_fieldUnitsTateEquiv (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ∃ e : tateZero (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ ≃+
        Additive (Kˣ ⧸ elementNormGroup K L),
      ∀ (x : Kˣ)
        (a : LinearMap.ker
          (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ σ - LinearMap.id)),
        (a : Additive Lˣ) = Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x) →
        e (zeroClass _ σ a) = Additive.ofMul (QuotientGroup.mk x) := by
  exact ⟨fieldUnitsTateEquiv K L σ hσ, fun x a ha => fieldUnitsTateEquiv_apply K L σ hσ x a ha⟩

omit hGalois in
/-- Hilbert 90 makes the first cohomology of field units trivial. -/
theorem fieldUnits_tateOne_subsingleton (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Subsingleton (tateOne
      (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ) := by
  exact tateOne_fieldUnits_subsingleton K L σ hσ

end Cox.ClassFieldTheory
