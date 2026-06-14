/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.SqrtTwo.Embeddings
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Canonical embedding of `ℚ(√2)`

This file records the canonical-embedding statements that underlie the concrete
rounding argument in `Euclidean.lean`.
-/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField nonZeroDivisors Real ENNReal QuadraticAlgebra

open Module NumberField Polynomial

namespace NumberField.SqrtTwo

/-- The canonical embedding evaluates at each complex embedding by definition. -/
theorem canonicalEmbedding_apply_sqrtTwoRoot (σ : K →+* ℂ) :
    NumberField.canonicalEmbedding K sqrtTwoRoot σ = σ sqrtTwoRoot := by
  rfl

private theorem complexEmbedding_norm_sqrtTwoRoot (φ : K →+* ℂ) :
    ‖φ sqrtTwoRoot‖ = Real.sqrt 2 := by
  simpa using infinitePlace_apply_sqrtTwoRoot (NumberField.InfinitePlace.mk φ)

/-- The canonical embedding of `√2` has house/norm equal to the positive square root `√2`. -/
theorem canonicalEmbedding_norm_sqrtTwoRoot :
    ‖NumberField.canonicalEmbedding K sqrtTwoRoot‖ = Real.sqrt 2 := by
  apply le_antisymm
  · rw [NumberField.canonicalEmbedding.norm_le_iff]
    intro φ
    rw [complexEmbedding_norm_sqrtTwoRoot φ]
  · obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    calc
      Real.sqrt 2 = ‖NumberField.canonicalEmbedding K sqrtTwoRoot φ‖ := by
        rw [NumberField.canonicalEmbedding.apply_at, complexEmbedding_norm_sqrtTwoRoot φ]
      _ ≤ ‖NumberField.canonicalEmbedding K sqrtTwoRoot‖ := norm_le_pi_norm _ φ

/-- The integral generator maps into the canonical integer lattice. -/
theorem canonicalEmbedding_sqrtTwoInteger_mem_integerLattice :
    NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K sqrtTwoInteger) ∈
      NumberField.canonicalEmbedding.integerLattice K := by
  change NumberField.canonicalEmbedding K (algebraMap (𝓞 K) K sqrtTwoInteger) ∈
    (RingHom.range (algebraMap (𝓞 K) K)).map (NumberField.canonicalEmbedding K)
  exact ⟨algebraMap (𝓞 K) K sqrtTwoInteger, ⟨sqrtTwoInteger, rfl⟩, rfl⟩

/-- The fundamental unit has archimedean coordinates `1 + √2` and `1 - √2`. -/
theorem canonicalEmbedding_fundamentalUnit_coordinates :
    ∃ σ τ : K →+* ℂ,
      σ (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K)) =
          (1 + Real.sqrt 2 : ℝ) ∧
        τ (algebraMap (𝓞 K) K (sqrtTwoFundamentalUnit : 𝓞 K)) =
          (1 - Real.sqrt 2 : ℝ) := by
  obtain ⟨σ, hσ⟩ := exists_realEmbedding_pos
  obtain ⟨τ, hτ⟩ := exists_realEmbedding_neg
  refine ⟨Complex.ofRealHom.comp σ.toRingHom, Complex.ofRealHom.comp τ.toRingHom, ?_, ?_⟩
  · change ↑(σ (sqrtTwoRoot + 1)) = ((1 + Real.sqrt 2 : ℝ) : ℂ)
    rw [map_add, hσ]
    norm_num [add_comm]
  · change ↑(τ (sqrtTwoRoot + 1)) = ((1 - Real.sqrt 2 : ℝ) : ℂ)
    rw [map_add, hτ, map_one]
    ring_nf

end NumberField.SqrtTwo
