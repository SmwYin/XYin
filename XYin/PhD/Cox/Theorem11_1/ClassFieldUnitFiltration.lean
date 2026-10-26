/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalUnitCohomology
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalAnalytic

/-! # The finite-index logarithmic comparison in Janusz V.3.9

The two submodules are the actual principal-unit filtration and ideal power.
All equivariance assertions refer to the completed automorphisms already fixed.
-/
open NumberField IsDedekindDomain
noncomputable section
namespace Cox.ClassFieldTheory.LocalCyclic
open Cox.CyclicCohomology
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
attribute [local instance] localAlgebra localFinite

/-- Valuation preservation makes every completed field automorphism continuous. -/
theorem automorphism_continuous
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    Continuous σ := by
  have hv := automorphism_preserves_valuation K L v w σ
  refine continuous_of_continuousAt_zero σ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
  rw [Filter.mem_map]
  refine Valued.mem_nhds_zero.mpr ⟨γ, fun x hx => hγ ?_⟩
  rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rwa [hv]

/-- The actual deep unit subgroup inside the additive integral-unit module. -/
def unitFiltrationSubmodule (t : ℕ) : Submodule ℤ (unitSubmodule L w) :=
  (localFieldUnitFiltration L w t).toAddSubgroup.toIntSubmodule.comap
    (unitSubmodule L w).subtype

/-- The actual completed ideal power viewed only as an integral module. -/
def integerIdealSubmodule (t : ℕ) : Submodule ℤ (w.adicCompletionIntegers L) :=
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ t).restrictScalars ℤ

/-- Completed automorphisms preserve every principal-unit depth. -/
theorem unitFiltrationSubmodule_stable (t : ℕ)
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    unitFiltrationSubmodule L w t ≤ (unitFiltrationSubmodule L w t).comap
      (unitRepresentation K L v w σ) := by
  intro x hx
  rw [Submodule.mem_comap]
  change Additive.toMul ((x : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ) ∈
    localFieldUnitFiltration L w t at hx
  change σ • Additive.toMul ((x : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ) ∈
    localFieldUnitFiltration L w t
  have hv := automorphism_preserves_valuation K L v w σ
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [mem_localFieldUnitFiltration_zero_iff] at hx ⊢
    exact (hv _).trans hx
  · rw [mem_localFieldUnitFiltration_iff L w t ht] at hx ⊢
    have h1 : ((σ • Additive.toMul ((x : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ) :
        (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
        σ (((Additive.toMul ((x : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ) :
          (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1) := by
      rw [map_sub, map_one]
      rfl
    rw [h1, hv]
    exact hx

/-- Completed automorphisms preserve every additive ideal power. -/
theorem integerIdealSubmodule_stable (t : ℕ)
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    integerIdealSubmodule L w t ≤ (integerIdealSubmodule L w t).comap
      (integerRepresentation K L v w σ) := by
  intro x hx
  rw [Submodule.mem_comap]
  change integerRepresentation K L v w σ x ∈
    IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ t
  change x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ t at hx
  rw [completed_mem_maximalIdeal_pow_iff] at hx ⊢
  rw [integerRepresentation_apply, automorphism_preserves_valuation K L v w σ]
  exact hx

/-- Restriction of the actual unit action to the principal-unit filtration. -/
def unitFiltrationRepresentation (t : ℕ) :
    Representation ℤ (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
      (unitFiltrationSubmodule L w t) :=
  (unitRepresentation K L v w).subrepresentation (unitFiltrationSubmodule L w t)
    (unitFiltrationSubmodule_stable K L v w t)

/-- Restriction of the actual integer action to its ideal power. -/
def integerIdealRepresentation (t : ℕ) :
    Representation ℤ (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
      (integerIdealSubmodule L w t) :=
  (integerRepresentation K L v w).subrepresentation (integerIdealSubmodule L w t)
    (integerIdealSubmodule_stable K L v w t)

/-- Finite residue rings give finite quotients by every unit-filtration depth. -/
theorem unit_filtration_finiteIndex (t : ℕ) :
    (localFieldUnitFiltration L w t).relIndex (localFieldUnitFiltration L w 0) ≠ 0 := by
  haveI := finite_completed_primary_quotient L w t
  haveI : Finite ((w.adicCompletionIntegers L) ⧸
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ t)ˣ :=
    Finite.of_injective _ Units.val_injective
  have hinj : Function.Injective
      (Units.map (w.adicCompletionIntegers L).subtype.toMonoidHom) :=
    Units.map_injective (f := (w.adicCompletionIntegers L).subtype.toMonoidHom)
      Subtype.val_injective
  rw [localFieldUnitFiltration, localFieldUnitFiltration,
    Subgroup.relIndex_map_map_of_injective _ _ hinj, localUnitFiltration_zero,
    Subgroup.relIndex_top_right, localUnitFiltration]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- The actual additive unit module has finite quotient by its deep subgroup. -/
theorem unitFiltrationSubmodule_quotient_finite (t : ℕ) :
    Finite ((unitSubmodule L w) ⧸ unitFiltrationSubmodule L w t) := by
  have hr : (unitSubmodule L w).subtype.toAddMonoidHom.range =
      (localFieldUnitFiltration L w 0).toAddSubgroup := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hidx : (unitFiltrationSubmodule L w t).toAddSubgroup.index ≠ 0 := by
    have h : (unitFiltrationSubmodule L w t).toAddSubgroup =
        (localFieldUnitFiltration L w t).toAddSubgroup.comap
          (unitSubmodule L w).subtype.toAddMonoidHom := rfl
    rw [h, AddSubgroup.index_comap, hr, Subgroup.relIndex_toAddSubgroup]
    exact unit_filtration_finiteIndex L w t
  haveI : (unitFiltrationSubmodule L w t).toAddSubgroup.FiniteIndex := ⟨hidx⟩
  exact AddSubgroup.finite_quotient_of_finiteIndex

/-- Completed residue-power finiteness also applies to the additive ideal quotient. -/
theorem integerIdealSubmodule_quotient_finite (t : ℕ) :
    Finite ((w.adicCompletionIntegers L) ⧸ integerIdealSubmodule L w t) := by
  exact finite_completed_primary_quotient L w t

/-- Transfer the same convergent logarithm to the source's two actual submodule carriers. -/
theorem exists_unitFiltrationLogEquiv :
    ∃ t₀ : ℕ, ∀ t ≥ t₀,
      ∃ e : unitFiltrationSubmodule L w t ≃+ integerIdealSubmodule L w t,
        ∀ u : unitFiltrationSubmodule L w t, HasSum (logTerm L w
          ((((u : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ).toMul :
            w.adicCompletion L) - 1))
          ((e u : w.adicCompletionIntegers L) : w.adicCompletion L) := by
  obtain ⟨t₀, ht₀⟩ := exists_logIso L w
  refine ⟨t₀, fun t ht => ?_⟩
  obtain ⟨E, hE, -⟩ := ht₀ t ht
  have hinj : Function.Injective
      (Units.map (w.adicCompletionIntegers L).subtype.toMonoidHom) :=
    Units.map_injective (f := (w.adicCompletionIntegers L).subtype.toMonoidHom)
      Subtype.val_injective
  let M := Subgroup.equivMapOfInjective (localUnitFiltration L w t) _ hinj
  let A : unitFiltrationSubmodule L w t ≃+ Additive (localFieldUnitFiltration L w t) :=
    { toFun := fun x => Additive.ofMul ⟨Additive.toMul
          ((x : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ), x.2⟩
      invFun := fun y => ⟨⟨Additive.ofMul ((Additive.toMul y : localFieldUnitFiltration L w t) :
          (w.adicCompletion L)ˣ), localFieldUnitFiltration_le_zero L w t (Additive.toMul y).2⟩,
          (Additive.toMul y).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let D : Additive (Multiplicative
      ↥(IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ t)) ≃+
        integerIdealSubmodule L w t :=
    { toFun := fun y => ⟨(Multiplicative.toAdd (Additive.toMul y)).1,
          (Multiplicative.toAdd (Additive.toMul y)).2⟩
      invFun := fun z => Additive.ofMul (Multiplicative.ofAdd ⟨z.1, z.2⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have key : ∀ z : localFieldUnitFiltration L w t,
      (((M.symm z : localUnitFiltration L w t) : (w.adicCompletionIntegers L)ˣ) :
        w.adicCompletion L) = ((z : (w.adicCompletion L)ˣ) : w.adicCompletion L) := fun z =>
    congrArg (fun q : localFieldUnitFiltration L w t =>
      ((q : (w.adicCompletion L)ˣ) : w.adicCompletion L)) (M.apply_symm_apply z)
  refine ⟨A.trans (M.symm.toAdditive.trans (E.toAdditive.trans D)), fun u => ?_⟩
  have h := hE (M.symm (Additive.toMul (A u)))
  rw [key] at h
  exact h

/-- Continuity and uniqueness of the source logarithmic sum prove Galois equivariance. -/
theorem unitFiltrationLogEquiv_equivariant (t : ℕ)
    (e : unitFiltrationSubmodule L w t ≃+ integerIdealSubmodule L w t)
    (he : ∀ u : unitFiltrationSubmodule L w t, HasSum (logTerm L w
      ((((u : unitSubmodule L w) : Additive (w.adicCompletion L)ˣ).toMul :
        w.adicCompletion L) - 1))
      ((e u : w.adicCompletionIntegers L) : w.adicCompletion L))
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (u : unitFiltrationSubmodule L w t) :
    e (unitFiltrationRepresentation K L v w t σ u) =
      integerIdealRepresentation K L v w t σ (e u) := by
  -- Rewriting only inside the small transported sum keeps this proof cheap; rewriting the
  -- representation-valued hypothesis exceeds the heartbeat limit.
  have h2 := log_equivariant L w σ.toRingEquiv (automorphism_continuous K L v w σ) _ _ (he u)
  rw [map_sub, map_one] at h2
  have h3 := (he (unitFiltrationRepresentation K L v w t σ u)).unique h2
  have h4 : (((integerIdealRepresentation K L v w t σ (e u) : integerIdealSubmodule L w t) :
      w.adicCompletionIntegers L) : w.adicCompletion L) =
        σ.toRingEquiv (((e u : integerIdealSubmodule L w t) : w.adicCompletionIntegers L) :
          w.adicCompletion L) :=
    integerRepresentation_apply K L v w σ _
  exact Subtype.ext (Subtype.ext (h3.trans h4.symm))

variable [hLocalGalois : IsGalois (v.adicCompletion K) (w.adicCompletion L)]
include hLocalGalois

/-- Local unit Tate groups are finite, transferred from the finite-index regular lattice. -/
theorem unit_finiteHerbrand
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    FiniteHerbrand (unitRepresentation K L v w) σ := by
  obtain ⟨t₀, ht₀⟩ := exists_unitFiltrationLogEquiv L w
  obtain ⟨e, he⟩ := ht₀ t₀ le_rfl
  haveI := integerIdealSubmodule_quotient_finite L w t₀
  haveI := unitFiltrationSubmodule_quotient_finite L w t₀
  have hIS := (finiteHerbrand_iff_subrepresentation (integerRepresentation K L v w) σ _
    (integerIdealSubmodule_stable K L v w t₀) hσ).mp (integer_finiteHerbrand K L v w σ hσ)
  have hUS := (finiteHerbrand_iff σ (unitFiltrationRepresentation K L v w t₀)
    (integerIdealRepresentation K L v w t₀) e
    (fun γ x => unitFiltrationLogEquiv_equivariant K L v w t₀ e he γ x)).mpr hIS
  exact (finiteHerbrand_iff_subrepresentation (unitRepresentation K L v w) σ _
    (unitFiltrationSubmodule_stable K L v w t₀) hσ).mpr hUS

/-- Local logarithms, finite-index comparison and the normal-basis lattice compute
Janusz V.3.9's local-unit Herbrand quotient. -/
theorem unit_herbrandQuotient
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    herbrandQuotient (unitRepresentation K L v w) σ = 1 := by
  obtain ⟨t₀, ht₀⟩ := exists_unitFiltrationLogEquiv L w
  obtain ⟨e, he⟩ := ht₀ t₀ le_rfl
  haveI := integerIdealSubmodule_quotient_finite L w t₀
  haveI := unitFiltrationSubmodule_quotient_finite L w t₀
  have hIA := integer_finiteHerbrand K L v w σ hσ
  have hIS := (finiteHerbrand_iff_subrepresentation (integerRepresentation K L v w) σ _
    (integerIdealSubmodule_stable K L v w t₀) hσ).mp hIA
  have hUA := unit_finiteHerbrand K L v w σ hσ
  have hUS := (finiteHerbrand_iff_subrepresentation (unitRepresentation K L v w) σ _
    (unitFiltrationSubmodule_stable K L v w t₀) hσ).mp hUA
  have h1 := herbrandQuotient_subrepresentation (unitRepresentation K L v w) σ _
    (unitFiltrationSubmodule_stable K L v w t₀) hσ hUA hUS
  have h2 := herbrandQuotient_congr σ (unitFiltrationRepresentation K L v w t₀)
    (integerIdealRepresentation K L v w t₀) e
    (fun γ x => unitFiltrationLogEquiv_equivariant K L v w t₀ e he γ x)
  have h3 := herbrandQuotient_subrepresentation (integerRepresentation K L v w) σ _
    (integerIdealSubmodule_stable K L v w t₀) hσ hIA hIS
  exact h1.symm.trans (h2.trans (h3.trans (integer_herbrandQuotient K L v w σ hσ)))

end Cox.ClassFieldTheory.LocalCyclic
