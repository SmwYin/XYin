/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealGroups
import XYin.PhD.Cox.Theorem11_1.Chebotarev
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-!
# Surjectivity from Frobenius prime values

Janusz IV.5.3, printed p.136, selects a Frobenius generator outside a finite set of primes. Here the
existing exact-conjugacy-class infinitude child supplies the selected prime. The finite exceptional
set is constructed from the nonzero modulus.
-/

open NumberField IsDedekindDomain Cox.Chebotarev
open scoped nonZeroDivisors IsMulCommutative
noncomputable section
namespace Cox.ClassFieldTheory

/-- In a ring with finite quotients, a nonzero ideal has finitely many overideals. -/
theorem finite_ideals_above {R : Type*} [CommRing R] [Ring.HasFiniteQuotients R]
    (m : Ideal R) (hm : m ≠ ⊥) : Set.Finite {I : Ideal R | m ≤ I} := by
  obtain ⟨x, hxm, hx0⟩ := (Submodule.ne_bot_iff m).mp hm
  exact (Ring.HasFiniteQuotients.finite_setOf_mem x hx0).subset fun I hI => hI hxm

/-- A prescribed Frobenius class occurs at a prime coprime to any nonzero modulus. -/
theorem exists_coprime_frobenius_class
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (C : ConjClasses Gal(L/K)) :
    ∃ q : Ideal (𝓞 K), q.IsPrime ∧ UnramifiedIn K L q ∧ q ⊔ m = ⊤ ∧
      frobeniusClass K L q = C := by
  obtain ⟨q, ⟨hqP, hqU, hqC⟩, hqm⟩ :=
    ((infinite_setOf_frobenius_class K L C).diff (finite_ideals_above m hm)).nonempty
  refine ⟨q, hqP, hqU, ?_, hqC⟩
  by_contra hne
  have hq : q = q ⊔ m := (hqP.isMaximal hqU.1).eq_of_le hne le_sup_left
  exact hqm (le_sup_right.trans hq.symm.le)

/-- A homomorphism with the arithmetic Frobenius prime values is surjective. -/
theorem surjective_of_frobenius_prime_values
    (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (φ : coprimeIdeals K m →* Gal(L/K))
    (hφ : ∀ (q : Ideal (𝓞 K)), q.IsPrime → q ≠ ⊥ →
      ∀ u : coprimeIdeals K m,
        ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q →
        φ u = (frobeniusClass K L q).out) : Function.Surjective φ := by
  intro σ
  obtain ⟨q, hqP, hqU, hqm, hqC⟩ :=
    exists_coprime_frobenius_class K L m hm (ConjClasses.mk σ)
  obtain ⟨u, hu⟩ := exists_coprimeIdealUnit K m q hqU.1 hqm
  refine ⟨u, ?_⟩
  rw [hφ q hqP hqU.1 u hu]
  apply ConjClasses.mk_injective
  rw [← hqC]
  exact Quotient.out_eq _

end Cox.ClassFieldTheory
