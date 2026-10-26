/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldFiniteLattice
import XYin.PhD.Cox.Theorem11_1.ClassFieldArithmetic
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionGalois
import XYin.PhD.Cox.Theorem11_1.ClassFieldCohomology

/-! # The local normal-basis lattice

Janusz V.3.9, p. 152: clear a base denominator, form the integral conjugate span,
identify its regular action, and transfer Tate groups across the finite quotient.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise WithZero
noncomputable section
namespace Cox.ClassFieldTheory

open Cox.CyclicCohomology

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

namespace LocalCyclic

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] localAlgebra localFinite

variable [hLocalGalois : IsGalois (v.adicCompletion K) (w.adicCompletion L)]
include hLocalGalois

attribute [local instance] completionIntegerFieldAlgebra completionIntegerAlgebra
  completion_integerField_isScalarTower completion_integerRing_isScalarTower
  completion_integers_isIntegralClosure completion_integers_finite
  completion_integers_isTorsionFree

omit hLocalGalois in
/-- Uniqueness of the extended complete discrete valuation forces local automorphisms
above the fixed base field to preserve the normalized valuation. -/
theorem automorphism_preserves_valuation
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (x : w.adicCompletion L) :
    (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰) (σ x) =
      (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰) x := by
  have h1 := valuation_local_norm K L v w (σ x)
  have h2 := valuation_local_norm K L v w x
  rw [Algebra.norm_eq_of_algEquiv σ x, h2] at h1
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hf0 : Ideal.inertiaDeg v.asIdeal w.asIdeal ≠ 0 :=
    (Ideal.inertiaDeg_pos v.asIdeal w.asIdeal).ne'
  exact ((pow_left_inj₀ zero_le' zero_le' hf0).mp h1).symm

omit hLocalGalois in
/-- A local automorphism preserves membership in the actual valuation ring. -/
theorem automorphism_mem_integers_iff
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (x : w.adicCompletion L) :
    σ x ∈ w.adicCompletionIntegers L ↔ x ∈ w.adicCompletionIntegers L := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    automorphism_preserves_valuation K L v w σ x]

omit hLocalGalois in
/-- Restrict the actual local field automorphism to its invariant integer ring. -/
def integerAut
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    w.adicCompletionIntegers L ≃+* w.adicCompletionIntegers L where
  toFun x := ⟨σ x, (automorphism_mem_integers_iff K L v w σ x).2 x.property⟩
  invFun x := ⟨σ.symm x, (automorphism_mem_integers_iff K L v w σ.symm x).2 x.property⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext
    (map_mul σ (x : w.adicCompletion L) (y : w.adicCompletion L))
  map_add' x y := Subtype.ext
    (map_add σ (x : w.adicCompletion L) (y : w.adicCompletion L))

omit hLocalGalois in
/-- The restricted automorphism has precisely the original field value. -/
theorem integerAut_apply
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (x : w.adicCompletionIntegers L) :
    (integerAut K L v w σ x : w.adicCompletion L) = σ x := by
  rfl

omit hLocalGalois in
/-- Restriction sends the identity automorphism to the identity. -/
theorem integerAut_one :
    integerAut K L v w 1 = RingEquiv.refl (w.adicCompletionIntegers L) := by
  exact RingEquiv.ext fun x => Subtype.ext rfl

omit hLocalGalois in
/-- Restriction preserves the actual order of automorphism composition. -/
theorem integerAut_mul
    (σ τ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    integerAut K L v w (σ * τ) =
      (integerAut K L v w τ).trans (integerAut K L v w σ) := by
  exact RingEquiv.ext fun x => Subtype.ext rfl

omit hLocalGalois in
/-- The completed base integer ring has finite nonzero ideal quotients. -/
theorem completionIntegers_hasFiniteQuotients :
    Ring.HasFiniteQuotients (v.adicCompletionIntegers K) := by
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
    have h := finite_completed_primary_quotient K v 1
    rw [pow_one] at h
    exact h
  exact dvr_hasFiniteQuotients (v.adicCompletionIntegers K)

omit hLocalGalois in
/-- The upstairs integer rank is the local field degree over the fixed base. -/
theorem completionIntegers_finrank :
    Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  haveI := completion_isSeparable K L v w
  haveI : Module.IsTorsionFree (v.adicCompletionIntegers K) (w.adicCompletion L) :=
    Module.IsTorsionFree.trans (v.adicCompletion K)
  exact IsIntegralClosure.rank (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.adicCompletion L) (w.adicCompletionIntegers L)

omit hLocalGalois in
/-- The specified local integer ring is the actual integral closure of the base DVR. -/
theorem completion_mem_integers_iff_integral (x : w.adicCompletion L) :
    x ∈ w.adicCompletionIntegers L ↔ IsIntegral (v.adicCompletionIntegers K) x := by
  rw [IsIntegralClosure.isIntegral_iff (A := w.adicCompletionIntegers L)]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

omit hLocalGalois in
/-- The additive integral span of the local Galois conjugates of a proposed normal
basis element, using coefficients in the actual base valuation ring. -/
def normalBasisLattice (a : w.adicCompletion L) :
    AddSubgroup (w.adicCompletionIntegers L) :=
  AddSubgroup.closure {x | ∃ c :
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) →
        v.adicCompletionIntegers K,
    (x : w.adicCompletion L) = ∑ σ,
      algebraMap (v.adicCompletion K) (w.adicCompletion L)
        (c σ : v.adicCompletion K) * σ a}

omit hLocalGalois in
/-- The actual base-integer linear combination of integral conjugates. -/
def normalBasisMap (a : w.adicCompletion L)
    (ha : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      σ a ∈ w.adicCompletionIntegers L) :
    ((w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) →₀
        v.adicCompletionIntegers K) →ₗ[v.adicCompletionIntegers K]
      w.adicCompletionIntegers L :=
  Finsupp.linearCombination (v.adicCompletionIntegers K) (fun σ => ⟨σ a, ha σ⟩)

omit hLocalGalois in
/-- Its field value is the source's finite sum of integral conjugate multiples. -/
theorem normalBasisMap_apply (a : w.adicCompletion L)
    (ha : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      σ a ∈ w.adicCompletionIntegers L)
    (c : (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) →₀
      v.adicCompletionIntegers K) :
    (normalBasisMap K L v w a ha c : w.adicCompletion L) =
      ∑ σ, algebraMap (v.adicCompletion K) (w.adicCompletion L)
        (c σ : v.adicCompletion K) * σ a := by
  rw [normalBasisMap, Finsupp.linearCombination_apply, Finsupp.sum_fintype c
    (fun σ r => r • (⟨σ a, ha σ⟩ : w.adicCompletionIntegers L)) (fun _ => zero_smul _ _)]
  push_cast
  refine Finset.sum_congr rfl fun σ _ => ?_
  rfl

omit hLocalGalois in
/-- The old closure definition is precisely the range of the actual coordinate map. -/
theorem normalBasisLattice_eq_range (a : w.adicCompletion L)
    (ha : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      σ a ∈ w.adicCompletionIntegers L) :
    normalBasisLattice K L v w a =
      (LinearMap.range (normalBasisMap K L v w a ha)).toAddSubgroup := by
  apply le_antisymm
  · rw [normalBasisLattice, AddSubgroup.closure_le]
    rintro x ⟨c, hc⟩
    refine ⟨Finsupp.equivFunOnFinite.symm c, Subtype.ext ?_⟩
    rw [normalBasisMap_apply, hc]
    simp
  · rintro x ⟨c, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, normalBasisMap_apply K L v w a ha c⟩

omit hLocalGalois in
/-- Independence over the completed field implies injectivity of the integral map. -/
theorem normalBasisMap_injective (a : w.adicCompletion L)
    (ha : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      σ a ∈ w.adicCompletionIntegers L)
    (hlin : LinearIndependent (v.adicCompletion K)
      (fun σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L => σ a)) :
    Function.Injective (normalBasisMap K L v w a ha) := by
  have h1 : LinearIndependent (v.adicCompletionIntegers K)
      (fun σ : (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) => σ a) :=
    hlin.restrict_scalars' (v.adicCompletionIntegers K)
  have h2 : LinearIndependent (v.adicCompletionIntegers K)
      (fun σ : (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) =>
        (⟨σ a, ha σ⟩ : w.adicCompletionIntegers L)) :=
    LinearIndependent.of_comp (IsScalarTower.toAlgHom (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) (w.adicCompletion L)).toLinearMap h1
  exact h2

/-- The integral conjugate span has the same rank as the upstairs local integers. -/
theorem normalBasisMap_range_finrank (a : w.adicCompletion L)
    (ha : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      σ a ∈ w.adicCompletionIntegers L)
    (hlin : LinearIndependent (v.adicCompletion K)
      (fun σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L => σ a)) :
    Module.finrank (v.adicCompletionIntegers K)
        (LinearMap.range (normalBasisMap K L v w a ha)) =
      Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  rw [LinearMap.finrank_range_of_inj (normalBasisMap_injective K L v w a ha hlin),
    Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
    completionIntegers_finrank]

/-- Full rank over the base DVR gives an actually finite additive lattice quotient. -/
theorem normalBasisLattice_finite_quotient (a : w.adicCompletion L)
    (ha : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      σ a ∈ w.adicCompletionIntegers L)
    (hlin : LinearIndependent (v.adicCompletion K)
      (fun σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L => σ a)) :
    Finite ((w.adicCompletionIntegers L) ⧸ normalBasisLattice K L v w a) := by
  haveI := completionIntegers_hasFiniteQuotients K v
  haveI := completion_isSeparable K L v w
  haveI : Module.IsTorsionFree (v.adicCompletionIntegers K) (w.adicCompletion L) :=
    Module.IsTorsionFree.trans (v.adicCompletion K)
  haveI : Module.Free (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
    IsIntegralClosure.module_free (v.adicCompletionIntegers K) (v.adicCompletion K)
      (w.adicCompletion L) (w.adicCompletionIntegers L)
  have h := finite_quotient_of_full_rank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
    (LinearMap.range (normalBasisMap K L v w a ha)) (normalBasisMap_range_finrank K L v w a ha hlin)
  rw [normalBasisLattice_eq_range K L v w a ha]
  exact h

/-- Janusz V.3.9: a normal-basis element gives an integral stable lattice with finite
quotient in the completed valuation ring. -/
theorem exists_normalBasis_lattice :
    ∃ a : w.adicCompletion L,
      LinearIndependent (v.adicCompletion K)
        (fun σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L => σ a) ∧
      (∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
        σ a ∈ w.adicCompletionIntegers L) ∧
      Finite ((w.adicCompletionIntegers L) ⧸ normalBasisLattice K L v w a) := by
  obtain ⟨a, hint, hlin⟩ := exists_integral_normal_basis (v.adicCompletion K)
    (w.adicCompletion L) (v.adicCompletionIntegers K)
  have ha : ∀ σ : (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L),
      σ a ∈ w.adicCompletionIntegers L :=
    fun σ => (completion_mem_integers_iff_integral K L v w (σ a)).mpr (hint σ)
  exact ⟨a, hlin, ha, normalBasisLattice_finite_quotient K L v w a ha hlin⟩

omit hLocalGalois in
/-- Local automorphisms act linearly on the additive valuation ring, with the action
characterized by the existing field automorphisms. -/
theorem exists_integerRepresentation :
    ∃ ρ : Representation ℤ
        (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
        (w.adicCompletionIntegers L),
      ∀ σ x, (ρ σ x : w.adicCompletion L) = σ (x : w.adicCompletion L) := by
  refine ⟨{ toFun := fun σ => (integerAut K L v w σ).toAddEquiv.toAddMonoidHom.toIntLinearMap
            map_one' := LinearMap.ext fun x => Subtype.ext rfl
            map_mul' := fun σ τ => LinearMap.ext fun x => Subtype.ext rfl }, fun σ x => rfl⟩

omit hLocalGalois in
/-- The actual additive local-integer representation. -/
def integerRepresentation : Representation ℤ
    (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (w.adicCompletionIntegers L) :=
  Classical.choose (exists_integerRepresentation K L v w)

omit hLocalGalois in
/-- The chosen representation acts by the specified local field automorphisms. -/
theorem integerRepresentation_apply
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (x : w.adicCompletionIntegers L) :
    (integerRepresentation K L v w σ x : w.adicCompletion L) = σ x := by
  exact Classical.choose_spec (exists_integerRepresentation K L v w) σ x

omit hLocalGalois in
/-- Permuting the conjugate coordinates is the actual local Galois action. -/
theorem normalBasisMap_equivariant (a : w.adicCompletion L)
    (ha : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      σ a ∈ w.adicCompletionIntegers L)
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (c : (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) →₀
      v.adicCompletionIntegers K) :
    normalBasisMap K L v w a ha
        (Representation.ofMulAction (v.adicCompletionIntegers K)
          (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
          (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) σ c) =
      integerRepresentation K L v w σ (normalBasisMap K L v w a ha c) := by
  apply Subtype.ext
  rw [integerRepresentation_apply, normalBasisMap_apply, normalBasisMap_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft σ⁻¹) _ _ fun τ => ?_
  rw [Representation.ofMulAction_apply, map_mul, AlgEquiv.commutes, Equiv.coe_mulLeft,
    smul_eq_mul, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

omit hLocalGalois in
/-- Reindexing the conjugates makes the integral normal-basis lattice stable. -/
theorem normalBasisLattice_stable (a : w.adicCompletion L)
    (ha : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      σ a ∈ w.adicCompletionIntegers L)
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    (normalBasisLattice K L v w a).toIntSubmodule ≤
      (normalBasisLattice K L v w a).toIntSubmodule.comap
        (integerRepresentation K L v w σ) := by
  intro x hx
  rw [Submodule.mem_comap]
  change x ∈ normalBasisLattice K L v w a at hx
  change integerRepresentation K L v w σ x ∈ normalBasisLattice K L v w a
  rw [normalBasisLattice_eq_range K L v w a ha] at hx ⊢
  obtain ⟨c, rfl⟩ := hx
  exact ⟨_, normalBasisMap_equivariant K L v w a ha σ c⟩

omit hLocalGalois in
/-- The inherited action on the actual integral normal-basis lattice. -/
def normalBasisRepresentation (a : w.adicCompletion L)
    (ha : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      σ a ∈ w.adicCompletionIntegers L) :
    Representation ℤ
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
      (normalBasisLattice K L v w a).toIntSubmodule :=
  (integerRepresentation K L v w).subrepresentation
    (normalBasisLattice K L v w a).toIntSubmodule
      (normalBasisLattice_stable K L v w a ha)

omit hLocalGalois in
/-- Normal-basis coordinates identify the lattice equivariantly with the regular
representation having coefficients in the base valuation ring. -/
theorem normalBasisLattice_equiv_regular (a : w.adicCompletion L)
    (ha : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      σ a ∈ w.adicCompletionIntegers L)
    (hlin : LinearIndependent (v.adicCompletion K)
      (fun σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L => σ a)) :
    ∃ e : ((w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) →₀
        v.adicCompletionIntegers K) ≃+ (normalBasisLattice K L v w a).toIntSubmodule,
      ∀ σ x, e ((Representation.ofMulAction (v.adicCompletionIntegers K)
          (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
          (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)) σ x) =
        (normalBasisRepresentation K L v w a ha) σ (e x) := by
  have hrange := normalBasisLattice_eq_range K L v w a ha
  have hinj := normalBasisMap_injective K L v w a ha hlin
  let E := LinearEquiv.ofInjective _ hinj
  refine ⟨{ toFun := fun c => ⟨normalBasisMap K L v w a ha c,
              (SetLike.ext_iff.mp hrange _).mpr ⟨c, rfl⟩⟩
            invFun := fun x => E.symm ⟨x.1, (SetLike.ext_iff.mp hrange x.1).mp x.2⟩
            left_inv := fun c => E.symm_apply_apply c
            right_inv := fun x => Subtype.ext ((LinearEquiv.ofInjective_apply _ _).symm.trans
              (congrArg Subtype.val
                (E.apply_symm_apply ⟨x.1, (SetLike.ext_iff.mp hrange x.1).mp x.2⟩)))
            map_add' := fun c d => Subtype.ext (map_add _ c d) }, fun σ x => ?_⟩
  exact Subtype.ext (normalBasisMap_equivariant K L v w a ha σ x)

/-- Tate finiteness of the local integer ring transfers from the finite-index
normal-basis lattice, whose coefficient-general regular Tate groups are trivial. -/
theorem integer_finiteHerbrand
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    FiniteHerbrand (integerRepresentation K L v w) σ := by
  obtain ⟨a, hlin, ha, hfin⟩ := exists_normalBasis_lattice K L v w
  obtain ⟨e, he⟩ := normalBasisLattice_equiv_regular K L v w a ha hlin
  haveI : Finite ((w.adicCompletionIntegers L) ⧸
      (normalBasisLattice K L v w a).toIntSubmodule) := hfin
  rw [finiteHerbrand_iff_subrepresentation (integerRepresentation K L v w) σ _
    (normalBasisLattice_stable K L v w a ha) hσ]
  exact (finiteHerbrand_iff σ _ _ e he).mp
    (finiteHerbrand_regular_coeff σ (v.adicCompletionIntegers K) hσ)

/-- The finite-index normal-basis lattice has regular quotient one, giving q(O_L)=1. -/
theorem integer_herbrandQuotient
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    herbrandQuotient (integerRepresentation K L v w) σ = 1 := by
  obtain ⟨a, hlin, ha, hfin⟩ := exists_normalBasis_lattice K L v w
  obtain ⟨e, he⟩ := normalBasisLattice_equiv_regular K L v w a ha hlin
  haveI : Finite ((w.adicCompletionIntegers L) ⧸
      (normalBasisLattice K L v w a).toIntSubmodule) := hfin
  have hA := integer_finiteHerbrand K L v w σ hσ
  have hS := (finiteHerbrand_iff_subrepresentation (integerRepresentation K L v w) σ _
    (normalBasisLattice_stable K L v w a ha) hσ).mp hA
  have h1 := herbrandQuotient_subrepresentation (integerRepresentation K L v w) σ _
    (normalBasisLattice_stable K L v w a ha) hσ hA hS
  have h2 := herbrandQuotient_congr σ _ _ e he
  have h3 := herbrandQuotient_regular_coeff σ (v.adicCompletionIntegers K) hσ
  exact h1.symm.trans (h2.symm.trans h3)

end LocalCyclic
end Cox.ClassFieldTheory
