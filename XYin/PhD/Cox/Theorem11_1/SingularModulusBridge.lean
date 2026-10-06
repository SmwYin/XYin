/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.SingularModuli
import XYin.PhD.Cox.Theorem11_1.OrderForms

/-!
# Ideal invariants are singular moduli

The invariant of an invertible fractional ideal of an imaginary quadratic order is the analytic
`j`-value at an imaginary quadratic point. This connects the ideal-theoretic statement of Cox
Theorem 11.1 with the integrality of singular moduli already proved in
`XYin.PhD.Cox.SingularModuli`.
-/

open NumberField
open scoped nonZeroDivisors Pointwise

noncomputable section

namespace Cox.Order

variable {K : IntermediateField ℚ ℂ} [hNF : NumberField K]
variable (O : Subalgebra ℤ K) [hO : IsOrder O] [hIQ : IsImaginaryQuadraticField K]

include hNF hO hIQ

/-- Source: Cox, Proposition 7.4 and Lemma 7.5, pp. 135–136 (normalized basis `[1, τ]`), with
Theorem 10.9, p. 207 (homothety invariance of `j`). -/
theorem idealJ_isSingularModulus (I : (FractionalIdeal O⁰ K)ˣ) :
    IsSingularModulus (idealJ O I) := by
  obtain ⟨α, τ₀, A, B₀, C, hA, hlin₀, hq₀, hprim₀, hcoord₀⟩ :=
    exists_positive_normalized_relation O I
  have hD₀ := normalized_discriminant_neg τ₀ A B₀ C hA.ne' hlin₀ hq₀
  have him₀ : ((τ₀ : K) : ℂ).im ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ := (real_mem_iff_rat τ₀).mp h
    rw [LinearIndependent.pair_iff] at hlin₀
    have h5 := hlin₀ q (-1) (by rw [hq]; simp [Rat.smul_def])
    norm_num at h5
  obtain ⟨τ, B, him, hq, hD, hprim, hcoord⟩ : ∃ (τ : K) (B : ℤ), 0 < (τ : ℂ).im ∧
      (A : K) * τ ^ 2 + B * τ + C = 0 ∧ B ^ 2 - 4 * A * C < 0 ∧
      Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1 ∧
      ((I : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
        (α : K) • Submodule.span ℤ ({1, τ} : Set K) := by
    rcases him₀.lt_or_gt with hlt | hgt
    · refine ⟨-τ₀, -B₀, by simpa using hlt, by push_cast; linear_combination hq₀,
        by simpa using hD₀, by simpa using hprim₀, ?_⟩
      rw [hcoord₀]
      congr 1
      apply le_antisymm <;> rw [Submodule.span_le] <;> intro z hz <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz <;>
        rcases hz with h | h <;> subst z
      · exact Submodule.subset_span (by simp)
      · simpa using Submodule.neg_mem _
          (Submodule.subset_span (by simp : -τ₀ ∈ ({1, -τ₀} : Set K)))
      · exact Submodule.subset_span (by simp)
      · exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
    · exact ⟨τ₀, B₀, hgt, hq₀, hD₀, hprim₀, hcoord₀⟩
  let τH : UpperHalfPlane := ⟨(τ : ℂ), him⟩
  have hαC : ((α : K) : ℂ) ≠ 0 := by simp
  let a : ℂˣ := Units.mk0 ((α : K) : ℂ) hαC
  have hL : (a • UpperHalfPlane.periodPair τH).lattice =
      complexLattice O (I : FractionalIdeal O⁰ K) := by
    rw [PeriodPair.lattice, complexLattice, hcoord, Submodule.smul_span, Set.smul_set_insert,
      Set.smul_set_singleton, Submodule.map_span, Set.image_pair]
    simp [a, τH, UpperHalfPlane.periodPair]
  refine ⟨τH, ⟨⟨A, B, C, ?_, hD, hprim⟩⟩, ?_⟩
  · simpa using congrArg (fun w : K => (w : ℂ)) hq
  · rw [idealJ_eq_of_lattice_eq O I _ hL, PeriodPair.j_smul, j_eq_periodPair_j]

end Cox.Order
