/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitOrbitProducts
import Mathlib.LinearAlgebra.LinearIndependent.Basic
/-! # Janusz V.2.3 coefficient nonvanishing and normalization

The actual orbit relation is expanded over the exact restriction fibers. Full
weighted-log deletion independence forces every base coefficient to be nonzero.
The normalized family is the literal family of integer powers. It need not retain
the original smallness inequalities when exponents are negative. Relation
uniqueness, finite index and the Herbrand computation are subsequent steps.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory

/-- The full weighted logarithm of an actual field-unit power scales by its integer exponent. -/
theorem weightedLog_zpow (L : Type*) [Field L] (u : Lˣ) (n : ℤ) (v : InfinitePlace L) :
    (v.mult : ℝ) * Real.log (v ((u ^ n : Lˣ) : L)) =
      (n : ℝ) * ((v.mult : ℝ) * Real.log (v (u : L))) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, Real.log_zpow]
  ring

/-- The full weighted logarithm of a finite product of actual field units is additive. -/
theorem weightedLog_prod (L : Type*) [Field L] {ι : Type*} [Fintype ι]
    (u : ι → Lˣ) (v : InfinitePlace L) :
    (v.mult : ℝ) * Real.log (v ((∏ i, u i : Lˣ) : L)) =
      ∑ i, (v.mult : ℝ) * Real.log (v (u i : L)) := by
  rw [Units.coe_prod, map_prod,
    Real.log_prod (fun i _ => (InfinitePlace.pos_iff.mpr (u i).ne_zero).ne'), Finset.mul_sum]

/-- An exact multiplicative relation gives the actual full-coordinate logarithmic relation. -/
theorem relation_weightedLog_sum_eq_zero (L : Type*) [Field L] {ι : Type*} [Fintype ι]
    (u : ι → Lˣ) (a : ι → ℤ) (ha : (∏ i, u i ^ a i) = 1) :
    (∑ i, (a i : ℝ) • (fun v : InfinitePlace L =>
      (v.mult : ℝ) * Real.log (v (u i : L)))) = 0 := by
  funext v
  have h := congrArg (fun x : Lˣ => (v.mult : ℝ) * Real.log (v (x : L))) ha
  simp only [Units.val_one, map_one, Real.log_one, mul_zero] at h
  simp only [weightedLog_prod, weightedLog_zpow] at h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  exact h

/-- Deleting a zero coefficient from a relation among an independent deleted family forces all
coefficients to vanish. -/
theorem coefficients_eq_zero_of_deleted_independent {R V ι : Type*}
    [Semiring R] [AddCommMonoid V] [Module R V] [Fintype ι]
    (v : ι → V) (i₀ : ι) (hv : LinearIndependent R (fun i : {i : ι // i ≠ i₀} => v i.val))
    (a : ι → R) (ha : (∑ i, a i • v i) = 0) (ha₀ : a i₀ = 0) : a = 0 := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀, ha₀, zero_smul, zero_add] at ha
  have h := (Fintype.linearIndependent_iffₛ.mp hv) (fun i => a i.val) 0 (by simpa using ha)
  funext i
  by_cases hi : i = i₀
  · rw [hi, ha₀]
    rfl
  · exact h ⟨i, hi⟩

/-- Expand the actual orbit products into one product over the exact upstairs restriction
fibers. -/
theorem orbitUnitProducts_zpow_expand (K L : Type*) [Field K] [Field L]
    [NumberField L] [Algebra K L] [Fintype (InfinitePlace K)]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker) (a : InfinitePlace K → ℤ) :
    (∏ v, orbitUnitProduct K L u v ^ a v) =
      ∏ w, u w ^ a (w.comap (algebraMap K L)) := by
  classical
  rw [← Fintype.prod_fiberwise (fun w : InfinitePlace L => w.comap (algebraMap K L))
    (fun w => u w ^ a (w.comap (algebraMap K L)))]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [orbitUnitProduct, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [w.2]

/-- Every base coefficient is nonzero, using deletion independence and algebraic surjectivity on
places. -/
theorem orbitRelation_coefficients_ne_zero (K L : Type*) [Field K] [Field L]
    [NumberField L] [Algebra K L] [Algebra.IsAlgebraic K L] [Fintype (InfinitePlace K)]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hu : ∀ w₀ : InfinitePlace L, LinearIndependent ℝ
      (fun j : {w : InfinitePlace L // w ≠ w₀} => fun v : InfinitePlace L =>
        (v.mult : ℝ) * Real.log (v ((u j.val : Lˣ) : L))))
    (a : InfinitePlace K → ℤ) (ha : a ≠ 0)
    (hrel : (∏ v, orbitUnitProduct K L u v ^ a v) = 1) :
    ∀ v, a v ≠ 0 := by
  intro v₀ hv₀
  apply ha
  obtain ⟨w₀, hw₀⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v₀
  change w₀.comap (algebraMap K L) = v₀ at hw₀
  rw [orbitUnitProducts_zpow_expand K L u a] at hrel
  have hrel' : (∏ w, ((u w : Lˣ)) ^ a (w.comap (algebraMap K L))) = 1 := by
    have h := congrArg (fun x : (toPrincipalIdeal (𝓞 L) L).ker => (x : Lˣ)) hrel
    push_cast at h
    exact h
  have hsum := relation_weightedLog_sum_eq_zero L (fun w => (u w : Lˣ))
    (fun w => a (w.comap (algebraMap K L))) hrel'
  have hz := coefficients_eq_zero_of_deleted_independent
    (fun w : InfinitePlace L => fun v : InfinitePlace L =>
      (v.mult : ℝ) * Real.log (v ((u w : Lˣ) : L))) w₀ (hu w₀)
    (fun w => (a (w.comap (algebraMap K L)) : ℝ)) hsum (by simp only [hw₀, hv₀, Int.cast_zero])
  funext v
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
  change w.comap (algebraMap K L) = v at hw
  have h := congrFun hz w
  simp only [Pi.zero_apply, Int.cast_eq_zero] at h
  rw [← hw]
  exact h

/-- The literal Janusz normalization raises each unit to its base-place coefficient. -/
def normalizedUnitFamily (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker) (a : InfinitePlace K → ℤ)
    (w : InfinitePlace L) : (toPrincipalIdeal (𝓞 L) L).ker :=
  u w ^ a (w.comap (algebraMap K L))

/-- Powers constant on each restriction fiber preserve equivariance. -/
theorem normalizedUnitFamily_equivariant (K L : Type*) [Field K] [Field L]
    [NumberField L] [Algebra K L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hu : ∀ (σ : L ≃ₐ[K] L) w, σ • (u w : Lˣ) = (u (σ • w) : Lˣ))
    (a : InfinitePlace K → ℤ) :
    ∀ (σ : L ≃ₐ[K] L) w, σ • (normalizedUnitFamily K L u a w : Lˣ) =
      (normalizedUnitFamily K L u a (σ • w) : Lˣ) := by
  intro σ w
  have hfib : (σ • w).comap (algebraMap K L) = w.comap (algebraMap K L) := by
    rw [InfinitePlace.comap_smul]
    congr 1
    ext x
    exact σ.symm.commutes x
  simp only [normalizedUnitFamily, hfib, Subgroup.coe_zpow]
  rw [smul_zpow', hu]

/-- The actual normalized family has product one by the exact orbit-product relation. -/
theorem normalizedUnitFamily_prod_eq_one (K L : Type*) [Field K] [Field L]
    [NumberField L] [Algebra K L] [Fintype (InfinitePlace K)]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker) (a : InfinitePlace K → ℤ)
    (hrel : (∏ v, orbitUnitProduct K L u v ^ a v) = 1) :
    (∏ w, normalizedUnitFamily K L u a w) = 1 := by
  unfold normalizedUnitFamily
  rw [← orbitUnitProducts_zpow_expand K L u a, hrel]

/-- Nonzero real scaling preserves deletion independence for the actual normalized logarithms. -/
theorem normalizedUnitFamily_linearIndependent_delete (K L : Type*) [Field K] [Field L]
    [NumberField L] [Algebra K L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker) (a : InfinitePlace K → ℤ)
    (ha : ∀ v, a v ≠ 0) (w₀ : InfinitePlace L)
    (hu : LinearIndependent ℝ
      (fun j : {w : InfinitePlace L // w ≠ w₀} => fun v : InfinitePlace L =>
        (v.mult : ℝ) * Real.log (v ((u j.val : Lˣ) : L)))) :
    LinearIndependent ℝ
      (fun j : {w : InfinitePlace L // w ≠ w₀} => fun v : InfinitePlace L =>
        (v.mult : ℝ) * Real.log (v ((normalizedUnitFamily K L u a j.val : Lˣ) : L))) := by
  let c : {w : InfinitePlace L // w ≠ w₀} → ℝˣ := fun j =>
    Units.mk0 (a (j.val.comap (algebraMap K L)) : ℝ) (Int.cast_ne_zero.mpr (ha _))
  convert hu.units_smul c using 1
  funext j v
  change (v.mult : ℝ) * Real.log (v (((u j.val ^ a (j.val.comap (algebraMap K L)) :
      (toPrincipalIdeal (𝓞 L) L).ker) : Lˣ) : L)) =
    (a (j.val.comap (algebraMap K L)) : ℝ) * ((v.mult : ℝ) * Real.log (v ((u j.val : Lˣ) : L)))
  rw [Subgroup.coe_zpow, weightedLog_zpow]

/-- The source construction gives one equivariant normalized family with every deleted
logarithmic family independent. Relation uniqueness and finite index remain separate
conclusions. -/
theorem exists_normalized_equivariant_unit_family (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    ∃ u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker,
      (∀ (σ : L ≃ₐ[K] L) w, σ • (u w : Lˣ) = (u (σ • w) : Lˣ)) ∧
      (∏ w, u w) = 1 ∧
      ∀ w₀ : InfinitePlace L, LinearIndependent ℝ
        (fun j : {w : InfinitePlace L // w ≠ w₀} => fun v : InfinitePlace L =>
          (v.mult : ℝ) * Real.log (v ((u j.val : Lˣ) : L))) := by
  obtain ⟨u, hequiv, hsmall⟩ := exists_equivariant_small_unit_family K L
  have hli : ∀ w₀ : InfinitePlace L, LinearIndependent ℝ
      (fun j : {w : InfinitePlace L // w ≠ w₀} => fun v : InfinitePlace L =>
        (v.mult : ℝ) * Real.log (v ((u j.val : Lˣ) : L))) := fun w₀ =>
    linearIndependent_weightedLog_delete L u w₀ hsmall
  obtain ⟨a, ha, hrel⟩ := orbitUnitProducts_nonzero_relation K L u hequiv
  have hne := orbitRelation_coefficients_ne_zero K L u hli a ha hrel
  exact ⟨normalizedUnitFamily K L u a, normalizedUnitFamily_equivariant K L u hequiv a,
    normalizedUnitFamily_prod_eq_one K L u a hrel,
    fun w₀ => normalizedUnitFamily_linearIndependent_delete K L u a hne w₀ (hli w₀)⟩

end Cox.ClassFieldTheory
