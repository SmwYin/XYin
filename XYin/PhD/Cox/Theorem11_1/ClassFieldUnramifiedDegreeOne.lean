/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.NumberTheory.RamificationInertia.Basic

/-! # Completed generators and unramified radical extensions

Source: Janusz V.9.3 and its Hensel/local-degree prerequisites.
-/

noncomputable section
namespace Cox.ClassFieldTheory

/-- A degree-one extension of fraction fields has ramification index one. -/
theorem ramificationIdx_eq_one_of_finrank_eq_one
    (R S K L : Type*) [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (I : Ideal R) [I.IsMaximal] (hI : I ≠ ⊥)
    (J : Ideal S) [J.IsPrime] [J.LiesOver I]
    (hdegree : Module.finrank K L = 1) :
    Ideal.ramificationIdx I J = 1 := by
  haveI := FaithfulSMul.of_field_isFractionRing R S K L
  haveI : NoZeroSMulDivisors R S := ⟨fun {c x} h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h => FaithfulSMul.algebraMap_injective R S (by rwa [map_zero])) id⟩
  have hle : Ideal.ramificationIdx I J ≤ Module.finrank K L :=
    Ideal.ramificationIdx_le_finrank (S := S) (K := K) (L := L) J
  have hne := Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver J hI
  rw [hdegree] at hle
  omega

end Cox.ClassFieldTheory
