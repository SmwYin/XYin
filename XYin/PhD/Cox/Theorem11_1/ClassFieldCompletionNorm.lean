/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionDegree
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

/-! # Norms on completions

Janusz II.3.4 and V.3.3. The valuation formula uses the ideal norm of a
uniformizer and the determinant norm on units.
-/
open NumberField IsDedekindDomain IsLocalRing
open scoped nonZeroDivisors WithZero Pointwise
noncomputable section
namespace Cox.ClassFieldTheory

/-- The determinant norm on a finite extension with continuous scalar action is continuous. -/
theorem continuous_algebraNorm (F E : Type*) [NontriviallyNormedField F] [CompleteSpace F]
    [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [T2Space E] [ContinuousSMul F E] [FiniteDimensional F E] :
    Continuous (Algebra.norm F : E → F) := by
  classical
  let b := Module.finBasis F E
  have h : (Algebra.norm F : E → F) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [h]
  exact Continuous.matrix_det
    (LinearMap.continuous_of_finiteDimensional (Algebra.leftMulMatrix b).toLinearMap)

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [hvw : w.asIdeal.LiesOver v.asIdeal]
include hvw

/-- The image of the actual determinant norm on completed field units. -/
def localNormGroup : Subgroup (v.adicCompletion K)ˣ :=
  letI := completionAlgebra K L v w
  (Units.map (Algebra.norm (v.adicCompletion K) :
    w.adicCompletion L →* v.adicCompletion K)).range

/-- Membership in the local norm group is witnessed by an actual local field unit. -/
theorem mem_localNormGroup_iff (u : (v.adicCompletion K)ˣ) :
    u ∈ localNormGroup K L v w ↔
      ∃ x : (w.adicCompletion L)ˣ,
        letI := completionAlgebra K L v w
        Units.map (Algebra.norm (v.adicCompletion K) :
          w.adicCompletion L →* v.adicCompletion K) x = u := by
  exact Iff.rfl

attribute [local instance] completionAlgebra completion_finiteDimensional
  completionIntegerFieldAlgebra completionIntegerAlgebra
  completion_integerField_isScalarTower completion_integerRing_isScalarTower
  completion_integers_isIntegralClosure completion_integers_finite
  completion_integer_isLocalHom completion_maximal_liesOver

/-- The restricted embedding makes the upstairs local integers torsion-free. -/
theorem completion_integers_isTorsionFree :
    Module.IsTorsionFree (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  letI := completion_valuation_hasExtension K L v w
  exact Valuation.HasExtension.instIsTorsionFreeInteger

attribute [local instance] completion_integers_isTorsionFree

/-- The integral determinant norm agrees with the chosen completed field norm. -/
theorem completion_integer_norm_eq (a : w.adicCompletionIntegers L) :
    (Algebra.intNorm (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) a :
      v.adicCompletion K) = Algebra.norm (v.adicCompletion K) (a : w.adicCompletion L) := by
  exact Algebra.algebraMap_intNorm (A := v.adicCompletionIntegers K)
    (B := w.adicCompletionIntegers L) (K := v.adicCompletion K) (L := w.adicCompletion L) a

/-- Janusz I.8.4: the norm of the local prime is the base prime to the residue degree. -/
theorem completion_relNorm_maximal :
    Ideal.relNorm (v.adicCompletionIntegers K) (maximalIdeal (w.adicCompletionIntegers L)) =
      maximalIdeal (v.adicCompletionIntegers K) ^ Ideal.inertiaDeg v.asIdeal w.asIdeal := by
  haveI : CharZero (v.adicCompletionIntegers K) := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective (𝓞 K) (v.adicCompletionIntegers K))
  haveI : CharZero (FractionRing (v.adicCompletionIntegers K)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (v.adicCompletionIntegers K)
      (FractionRing (v.adicCompletionIntegers K)))
  rw [Ideal.relNorm_eq_pow_of_isMaximal (maximalIdeal (w.adicCompletionIntegers L))
    (maximalIdeal (v.adicCompletionIntegers K)), completion_inertiaDeg_eq]

omit hvw in
/-- The normalized completed uniformizer is irreducible in the local integer ring. -/
theorem completion_uniformizer_irreducible (π : w.adicCompletionIntegers L)
    (hπ : Valued.v (π : w.adicCompletion L) = WithZero.exp (-1 : ℤ)) :
    Irreducible π := by
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr
    (completed_maximalIdeal_eq_span L w π hπ)

/-- Janusz II.3.4: the norm of a uniformizer has base valuation equal to the residue degree. -/
theorem completion_norm_uniformizer (π : w.adicCompletionIntegers L)
    (hπ : Valued.v (π : w.adicCompletion L) = WithZero.exp (-1 : ℤ)) :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (Algebra.norm (v.adicCompletion K) (π : w.adicCompletion L)) =
        WithZero.exp (-(Ideal.inertiaDeg v.asIdeal w.asIdeal : ℤ)) := by
  obtain ⟨ρ, hρ⟩ := exists_completed_uniformizer K v
  have hspan : Ideal.span {Algebra.intNorm (v.adicCompletionIntegers K)
      (w.adicCompletionIntegers L) π} =
      Ideal.span {ρ ^ Ideal.inertiaDeg v.asIdeal w.asIdeal} := by
    rw [← Ideal.relNorm_singleton, ← completed_maximalIdeal_eq_span L w π hπ,
      completion_relNorm_maximal, completed_maximalIdeal_eq_span K v ρ hρ,
      Ideal.span_singleton_pow]
  have hρf : Valued.v (((ρ ^ Ideal.inertiaDeg v.asIdeal w.asIdeal :
      v.adicCompletionIntegers K)) : v.adicCompletion K) =
        WithZero.exp (-(Ideal.inertiaDeg v.asIdeal w.asIdeal : ℤ)) := by
    rw [SubmonoidClass.coe_pow, map_pow, hρ, ← WithZero.exp_nsmul]
    congr 1
    simp
  rw [← completion_integer_norm_eq, ← hρf]
  apply le_antisymm
  · have h1 : Algebra.intNorm (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π ∈
        Ideal.span {ρ ^ Ideal.inertiaDeg v.asIdeal w.asIdeal} := by
      rw [← hspan]
      exact Ideal.mem_span_singleton_self _
    exact (completed_mem_span_iff K v _ _).mp h1
  · have h1 : ρ ^ Ideal.inertiaDeg v.asIdeal w.asIdeal ∈ Ideal.span {Algebra.intNorm
        (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π} := by
      rw [hspan]
      exact Ideal.mem_span_singleton_self _
    exact (completed_mem_span_iff K v _ _).mp h1

/-- Janusz II.3.4: the norm of an integral unit is an integral unit. -/
theorem completion_norm_integerUnit (u : (w.adicCompletionIntegers L)ˣ) :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (Algebra.norm (v.adicCompletion K) (u : w.adicCompletion L)) = 1 := by
  rw [← completion_integer_norm_eq]
  exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp
    ((u.isUnit).map (Algebra.intNorm _ _))

/-- The normalized additive valuation of a local norm is multiplied by the residue
degree, expressed here in the multiplicative integer-value group. -/
theorem valuation_local_norm (x : w.adicCompletion L) :
    letI := completionAlgebra K L v w
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
        (Algebra.norm (v.adicCompletion K) x) =
      (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰) x ^
        Ideal.inertiaDeg v.asIdeal w.asIdeal := by
  change Valued.v (Algebra.norm (v.adicCompletion K) x) =
    Valued.v x ^ Ideal.inertiaDeg v.asIdeal w.asIdeal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hf0 : Ideal.inertiaDeg v.asIdeal w.asIdeal ≠ 0 :=
    (Ideal.inertiaDeg_pos v.asIdeal w.asIdeal).ne'
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Algebra.norm_zero, map_zero, map_zero, zero_pow hf0]
  obtain ⟨π, hπ⟩ := exists_completed_uniformizer L w
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (K := w.adicCompletion L) (completion_uniformizer_irreducible L w π hπ) hx
  have hπ0 : (π : w.adicCompletion L) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hu1 : Valued.v ((u : w.adicCompletionIntegers L) : w.adicCompletion L) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp u.isUnit
  let U : (w.adicCompletion L)ˣ := Units.mk0 _ hπ0
  have hpow : algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) π ^ n =
      ((U ^ n : (w.adicCompletion L)ˣ) : w.adicCompletion L) := by
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  have hu' : algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
      (u : w.adicCompletionIntegers L) =
        ((u : w.adicCompletionIntegers L) : w.adicCompletion L) := rfl
  rw [Units.smul_def, Algebra.smul_def, hpow, hu', map_mul, map_mul, map_mul,
    completion_norm_integerUnit K L v w u, hu1, one_mul, one_mul]
  have hN : Algebra.norm (v.adicCompletion K) ((U ^ n : (w.adicCompletion L)ˣ) :
      w.adicCompletion L) = ((Units.map (Algebra.norm (v.adicCompletion K) :
        w.adicCompletion L →* v.adicCompletion K) U) ^ n : (v.adicCompletion K)ˣ) := by
    rw [← map_zpow]
    rfl
  rw [hN, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀]
  change (Valued.v (Algebra.norm (v.adicCompletion K) (π : w.adicCompletion L))) ^ n =
    (Valued.v (π : w.adicCompletion L) ^ n) ^ Ideal.inertiaDeg v.asIdeal w.asIdeal
  rw [completion_norm_uniformizer K L v w π hπ, hπ, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul,
    ← WithZero.exp_nsmul]
  congr 1
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

/-- Janusz V.3.3: the actual local field norm is continuous. -/
theorem continuous_local_norm :
    Continuous (Algebra.norm (v.adicCompletion K) : w.adicCompletion L → v.adicCompletion K) := by
  letI : NontriviallyNormedField (v.adicCompletion K) :=
    Valued.toNontriviallyNormedField (v.adicCompletion K) ℤᵐ⁰
  haveI := completion_continuousSMul K L v w
  exact continuous_algebraNorm (v.adicCompletion K) (w.adicCompletion L)

end Cox.ClassFieldTheory
