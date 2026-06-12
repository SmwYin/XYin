import XYin.NumberField.FieldExamples.SqrtNegSixQuadraticAlgebra.UniqueFactorization

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace XYin.NumberField.New.SqrtNegSixQuadraticAlgebra

/-! ## 9. Galois group -/

/-- The identity automorphism of `ℚ(√-6)`. -/
noncomputable def idAut : K ≃ₐ[ℚ] K := AlgEquiv.refl

/-- The nontrivial conjugation automorphism, sending `θ` to `-θ` (complex conjugation under
any embedding into `ℂ`). -/
noncomputable def conjugation : K ≃ₐ[ℚ] K := by
  exact conj'

/-- The conjugation automorphism sends `θ` to `-θ`. -/
theorem conjugation_apply_theta : conjugation θ = -θ := by
  exact conj'_omega

/-- Quadratic extensions are Galois: `ℚ(√-6)/ℚ` is a Galois extension. -/
instance : Algebra.IsQuadraticExtension ℚ K where
  finrank_eq_two' := degree_eq_two

theorem isGalois : IsGalois ℚ K := by
  infer_instance

/-- Every `ℚ`-automorphism of `K` is the identity or the conjugation. -/
theorem aut_eq_or (σ : K ≃ₐ[ℚ] K) : σ = idAut ∨ σ = conjugation := by
  have hsq : (σ θ) ^ 2 = (-6 : K) := by
    rw [← map_pow, theta_sq]
    rw [show (-6 : K) = algebraMap ℚ K (-6) by norm_num]
    exact σ.commutes (-6)
  have hfactor : (σ θ - θ) * (σ θ + θ) = 0 := by
    have hθ := theta_sq
    linear_combination hsq - hθ
  have hext : ∀ τ : K ≃ₐ[ℚ] K, σ θ = τ θ → σ = τ := by
    intro τ h
    have hgen : (σ : K →ₐ[ℚ] K) = (τ : K →ₐ[ℚ] K) := QuadraticAlgebra.algHom_ext h
    exact AlgEquiv.ext fun x => AlgHom.congr_fun hgen x
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (hext idAut (by rw [sub_eq_zero] at h; exact h))
  · refine Or.inr (hext conjugation ?_)
    rw [conjugation_apply_theta]
    linear_combination h

/-- The Galois group of `ℚ(√-6)/ℚ` is cyclic of order `2`. -/
theorem galoisGroupStructure : Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2)) := by
  have hconj_ne : conjugation ≠ idAut := by
    intro h
    have h1 : conjugation θ = θ := by rw [h]; rfl
    rw [conjugation_apply_theta] at h1
    have h2 : (2 : K) * θ = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · norm_num at h3
    · have h4 := theta_sq
      rw [h3] at h4
      norm_num at h4
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨idAut, conjugation, Ne.symm hconj_ne, ?_⟩
    ext σ
    simp [aut_eq_or σ]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨mulEquivOfPrimeCardEq hcard (by
    rw [show Nat.card (Multiplicative (ZMod 2)) = Nat.card (ZMod 2) from rfl, Nat.card_zmod])⟩


end XYin.NumberField.New.SqrtNegSixQuadraticAlgebra
