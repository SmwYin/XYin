import XYin.NumberField.FieldExamples.SqrtNegSix.UniqueFactorization

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors QuadraticAlgebra

namespace NumberField.SqrtNegSix

/-! ## 9. Galois group -/

/-- The identity automorphism of `ℚ(√-6)`. -/
noncomputable def idAut : K ≃ₐ[ℚ] K := AlgEquiv.refl

/-- The conjugation `θ ↦ -θ` as an algebra map, via the universal property. -/
private noncomputable def conjugationHom : K →ₐ[ℚ] K :=
  QuadraticAlgebra.lift ⟨-QuadraticAlgebra.omega, by
    have h := QuadraticAlgebra.omega_mul_omega_eq_add
      (R := ℚ) (a := (-6 : ℚ)) (b := (0 : ℚ))
    simpa [neg_mul_neg] using h⟩

private theorem conjugationHom_omega : conjugationHom θ = -θ := by
  change (QuadraticAlgebra.omega : K).re • (1 : K) +
    (QuadraticAlgebra.omega : K).im • (-QuadraticAlgebra.omega) = -θ
  simp

private theorem conjugationHom_conjugationHom :
    conjugationHom.comp conjugationHom = AlgHom.id ℚ K := by
  apply QuadraticAlgebra.algHom_ext
  change conjugationHom (conjugationHom θ) = θ
  rw [conjugationHom_omega, map_neg, conjugationHom_omega, neg_neg]

/-- The nontrivial conjugation automorphism, sending `θ` to `-θ` (complex conjugation under
any embedding into `ℂ`). -/
noncomputable def conjugation : K ≃ₐ[ℚ] K :=
  AlgEquiv.ofAlgHom conjugationHom conjugationHom
    conjugationHom_conjugationHom conjugationHom_conjugationHom

/-- The conjugation automorphism sends `θ` to `-θ`. -/
theorem conjugation_apply_theta : conjugation θ = -θ := by
  exact conjugationHom_omega

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

private theorem conjugation_ne_id : conjugation ≠ idAut := by
  intro h
  have h1 : conjugation θ = θ := by rw [h]; rfl
  rw [conjugation_apply_theta] at h1
  have h2 : (2 : K) * θ = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · have h4 := theta_sq
    rw [h3] at h4
    norm_num at h4

theorem prod_auts (z : K) : ∏ σ : K ≃ₐ[ℚ] K, σ z = z * conjugation z := by
  classical
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) =
      insert idAut {conjugation} := by
    symm
    rw [Finset.eq_univ_iff_forall]
    intro σ
    rcases aut_eq_or σ with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [huniv, Finset.prod_insert (Finset.notMem_singleton.mpr (Ne.symm conjugation_ne_id)),
    Finset.prod_singleton]
  rfl

/-- The Galois group of `ℚ(√-6)/ℚ` is cyclic of order `2`. -/
theorem galoisGroupStructure : Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2)) := by
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨idAut, conjugation, Ne.symm conjugation_ne_id, ?_⟩
    ext σ
    simp [aut_eq_or σ]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨mulEquivOfPrimeCardEq hcard (by
    rw [show Nat.card (Multiplicative (ZMod 2)) = Nat.card (ZMod 2) from rfl, Nat.card_zmod])⟩


end NumberField.SqrtNegSix
