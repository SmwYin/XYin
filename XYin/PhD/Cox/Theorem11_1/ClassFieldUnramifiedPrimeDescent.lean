/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Ramification descends along an integral tower
-/

noncomputable section
namespace Cox.ClassFieldTheory

/-- If every upper prime over p is unramified, so is the given intermediate prime. -/
theorem ramificationIdx_eq_one_of_forall_liesOver
    (R S T : Type*) [CommRing R] [IsDomain R] [CommRing S] [CommRing T]
    [IsDedekindDomain S] [IsDedekindDomain T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree S T] [Algebra.IsIntegral S T]
    (p : Ideal R) (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hT : ∀ Q : Ideal T, Q.IsPrime → Q.LiesOver p → Ideal.ramificationIdx p Q = 1) :
    Ideal.ramificationIdx p P = 1 := by
  obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_primesOver (S := T) P
  haveI := hQ.1
  haveI := hQ.2
  haveI : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have htower := Ideal.ramificationIdx_algebra_tower' p P Q
  rw [hT Q hQ.1 inferInstance] at htower
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

end Cox.ClassFieldTheory
