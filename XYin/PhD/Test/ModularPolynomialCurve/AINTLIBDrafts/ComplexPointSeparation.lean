/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Algebraically closed points separate reduced algebras of finite type

The proof uses standard finite-type and reducedness classes. No hypothesis about a
particular polynomial relation or a domain structure is introduced.
-/

@[expose] public section

universe u v

namespace ModularPolynomialCurveTest.AINTLIB

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/-- Every maximal residue field of a finite-type algebra gives a point over the base field. -/
theorem exists_algHom_ker_eq_of_isMaximal (m : Ideal A) [m.IsMaximal] :
    ∃ φ : A →ₐ[k] k, RingHom.ker φ.toRingHom = m := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have : Algebra.IsAlgebraic k (A ⧸ m) := Algebra.IsAlgebraic.of_finite k (A ⧸ m)
  let ψ : (A ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext x
  change ψ (Ideal.Quotient.mk m x) = 0 ↔ x ∈ m
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact ψ.injective.eq_iff' (map_zero ψ)

/-- Algebraically closed points detect zero in every reduced finite-type algebra. -/
theorem eq_zero_of_forall_algHom_eq_zero [IsReduced A] (x : A)
    (h : ∀ φ : A →ₐ[k] k, φ x = 0) : x = 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  have hx : x ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    intro m hm
    have : m.IsMaximal := hm.2
    obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq_of_isMaximal (k := k) m
    rw [← hφ]
    exact h φ
  have hbot : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out (inferInstance : IsJacobsonRing A) Ideal.isRadical_bot
  rw [hbot] at hx
  exact Ideal.mem_bot.mp hx

/-- Equality of regular functions can be checked at all algebraically closed points. -/
theorem eq_of_forall_algHom_eq [IsReduced A] (x y : A)
    (h : ∀ φ : A →ₐ[k] k, φ x = φ y) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_forall_algHom_eq_zero (k := k)
  intro φ
  simp only [map_sub, h φ, sub_self]

/-- The complex specialization, without a domain or nontriviality assumption. -/
theorem eq_zero_of_forall_complex_algHom_eq_zero
    {A : Type v} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [IsReduced A]
    (x : A) (h : ∀ φ : A →ₐ[ℂ] ℂ, φ x = 0) : x = 0 :=
  eq_zero_of_forall_algHom_eq_zero x h

/-- A product sanity check: the separation result does not require a domain. -/
example (x : ℂ × ℂ) (h : ∀ φ : (ℂ × ℂ) →ₐ[ℂ] ℂ, φ x = 0) : x = 0 :=
  eq_zero_of_forall_complex_algHom_eq_zero x h

#print axioms exists_algHom_ker_eq_of_isMaximal
#print axioms eq_zero_of_forall_algHom_eq_zero
#print axioms eq_of_forall_algHom_eq
#print axioms eq_zero_of_forall_complex_algHom_eq_zero

end ModularPolynomialCurveTest.AINTLIB
