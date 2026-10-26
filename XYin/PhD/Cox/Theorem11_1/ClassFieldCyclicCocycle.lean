/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCohomology
import Mathlib.GroupTheory.SemidirectProduct

/-! # The Type*-general cyclic adapter to the existing Hilbert 90

Janusz V.2.1(a) invokes Hilbert 90. The existing Noether cocycle theorem is universe
polymorphic. This finite cyclic adapter constructs its actual cocycle from a
norm-one element, without transporting a field and its extension across universes.
No nontriviality assumption on the cyclic group is made.
-/

noncomputable section
namespace Cox.CyclicCocycle
variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- The literal element (x,g) of the semidirect product for the given action. -/
def generatorPair (g : G) (x : M) : M ⋊[MulDistribMulAction.toMulAut G M] G :=
  ⟨x, g⟩

/-- The right coordinate of the nth power is gⁿ. -/
theorem generatorPair_pow_right (g : G) (x : M) (n : ℕ) :
    ((generatorPair g x) ^ n).right = g ^ n := by
  exact map_pow (SemidirectProduct.rightHom (φ := MulDistribMulAction.toMulAut G M))
    (generatorPair g x) n

/-- The left coordinate of the nth power is the ordered orbit product. -/
theorem generatorPair_pow_left (g : G) (x : M) (n : ℕ) :
    ((generatorPair g x) ^ n).left = ∏ i ∈ Finset.range n, (g ^ i) • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, SemidirectProduct.mul_left, ih, Finset.prod_range_succ, generatorPair_pow_right]
    rfl

/-- A generator of the finite group has positive order, including order one. -/
theorem generator_order_pos [Finite G] (g : G) : 0 < orderOf g := by
  exact orderOf_pos g

variable [hFinG : Fintype G] (g : G) (hg : ∀ γ : G, γ ∈ Subgroup.zpowers g)

include hg

/-- The finite orbit product over generator powers is the full group norm. -/
theorem prod_generatorPowers (x : M) :
    (∏ i ∈ Finset.range (orderOf g), (g ^ i) • x) = ∏ γ : G, γ • x := by
  classical
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [← IsCyclic.image_range_card hg, Finset.prod_image, hord]
  intro i hi j hj hij
  exact pow_injOn_Iio_orderOf (by rw [hord]; simpa using hi) (by rw [hord]; simpa using hj) hij

/-- Norm one makes the literal semidirect generator satisfy the cyclic relation. -/
theorem generatorPair_pow_order (x : M) (hx : (∏ γ : G, γ • x) = 1) :
    generatorPair g x ^ orderOf g = 1 := by
  ext
  · rw [generatorPair_pow_left, prod_generatorPowers g hg, hx, SemidirectProduct.one_left]
  · rw [generatorPair_pow_right, pow_orderOf_eq_one, SemidirectProduct.one_right]

/-- The semidirect generator order divides the actual finite generator order. -/
theorem generatorPair_order_dvd (x : M) (hx : (∏ γ : G, γ • x) = 1) :
    orderOf (generatorPair g x) ∣ orderOf g := by
  exact orderOf_dvd_of_pow_eq_one (generatorPair_pow_order g hg x hx)

/-- The actual cyclic homomorphism sends g to (x,g). -/
def generatorLift (x : M) (hx : (∏ γ : G, γ • x) = 1) :
    G →* M ⋊[MulDistribMulAction.toMulAut G M] G :=
  monoidHomOfForallMemZpowers hg (generatorPair_order_dvd g hg x hx)

/-- The generator value fixes this homomorphism completely. -/
theorem generatorLift_apply_gen (x : M) (hx : (∏ γ : G, γ • x) = 1) :
    generatorLift g hg x hx g = generatorPair g x := by
  exact monoidHomOfForallMemZpowers_apply_gen hg _

/-- The right projection is the identity, by equality on the generator. -/
theorem generatorLift_right (x : M) (hx : (∏ γ : G, γ • x) = 1) (γ : G) :
    (generatorLift g hg x hx γ).right = γ := by
  have h := (MonoidHom.eq_iff_eq_on_generator hg
    ((SemidirectProduct.rightHom).comp (generatorLift g hg x hx)) (MonoidHom.id G)).mpr
    (congrArg SemidirectProduct.right (generatorLift_apply_gen g hg x hx))
  exact DFunLike.congr_fun h γ

/-- The actual cocycle is the left coordinate of the cyclic lift. -/
def normOneCocycle (x : M) (hx : (∏ γ : G, γ • x) = 1) : G → M :=
  fun γ ↦ (generatorLift g hg x hx γ).left

/-- Multiplication in the semidirect product supplies precisely the cocycle identity. -/
theorem normOneCocycle_isCocycle (x : M) (hx : (∏ γ : G, γ • x) = 1) :
    groupCohomology.IsMulCocycle₁ (normOneCocycle g hg x hx) := by
  intro a b
  change (generatorLift g hg x hx (a * b)).left =
    a • (generatorLift g hg x hx b).left * (generatorLift g hg x hx a).left
  rw [map_mul, SemidirectProduct.mul_left, generatorLift_right]
  exact mul_comm _ _

/-- Its value at g is the prescribed norm-one element, also when order g=1. -/
theorem normOneCocycle_apply_gen (x : M) (hx : (∏ γ : G, γ • x) = 1) :
    normOneCocycle g hg x hx g = x := by
  exact congrArg SemidirectProduct.left (generatorLift_apply_gen g hg x hx)

end Cox.CyclicCocycle

namespace Cox.CyclicCohomology
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Noether's existing Type* Hilbert90 applied to the actual norm-one cyclic cocycle. -/
theorem exists_unit_coboundary (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (x : Lˣ)
    (hx : (∏ τ : L ≃ₐ[K] L, τ • x) = 1) :
    ∃ y : Lˣ, σ • y / y = x := by
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
    (Cox.CyclicCocycle.normOneCocycle σ hσ x hx)
    (Cox.CyclicCocycle.normOneCocycle_isCocycle σ hσ x hx)
  exact ⟨β, (hβ σ).trans (Cox.CyclicCocycle.normOneCocycle_apply_gen σ hσ x hx)⟩

/-- The norm-zero/difference quotient vanishes for the natural field-unit action.
This universe-general formulation requires no Galois or number-field hypothesis. -/
theorem tateOne_fieldUnits_subsingleton (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Subsingleton (tateOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  rintro ⟨a, ha⟩ -
  have hnorm : (∏ τ : L ≃ₐ[K] L, τ • Additive.toMul a) = 1 := by
    have h := congrArg Additive.toMul (LinearMap.mem_ker.mp ha)
    rw [Representation.norm, LinearMap.sum_apply] at h
    simpa only [toMul_sum, toMul_zero, Representation.ofMulDistribMulAction_apply_apply,
      toMul_ofMul] using h
  obtain ⟨y, hy⟩ := exists_unit_coboundary K L σ hσ (Additive.toMul a) hnorm
  refine Submodule.mem_comap.mpr (LinearMap.mem_range.mpr ⟨Additive.ofMul y, ?_⟩)
  change Additive.ofMul (σ • y) - Additive.ofMul y = a
  rw [← ofMul_div, hy, ofMul_toMul]

end Cox.CyclicCohomology
