/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Scalar multiplication on a finite ideal quotient

Cox, Lemma 7.18(i), printed p. 143, uses surjectivity and bijectivity of multiplication by the
conductor on the finite additive group of an ideal quotient. These are the general algebraic facts
used by that argument.
-/

namespace Cox.OrderCoprimality

/-- The necessity in the finite-group criterion used in Cox, Lemma 7.18(i).
Cauchy's theorem provides the obstruction if a prime divides both integers. -/
theorem coprime_card_of_injective_nsmul {A : Type*} [AddGroup A] [Finite A]
    (n : ℕ) (h : Function.Injective (fun x : A ↦ n • x)) :
    (Nat.card A).Coprime n := by
  refine Nat.coprime_of_dvd fun p hp hpA hpn => ?_
  haveI := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hpA
  have hnx : n • x = n • (0 : A) := by
    rw [smul_zero]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (hx ▸ hpn)
  have hx0 : x = 0 := h hnx
  rw [hx0, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

/-- The finite-group automorphism criterion in Cox, Lemma 7.18(i). -/
theorem bijective_nsmul_iff_coprime_card {A : Type*} [AddGroup A] [Finite A]
    (n : ℕ) : Function.Bijective (fun x : A ↦ n • x) ↔ (Nat.card A).Coprime n := by
  refine ⟨fun h => coprime_card_of_injective_nsmul n h.1, fun h => ?_⟩
  have e : (fun x : A ↦ n • x) = nsmulCoprime h := funext fun x => (nsmulCoprime_apply h x).symm
  rw [e]
  exact (nsmulCoprime h).bijective

/-- The first equivalence in Cox's proof of Lemma 7.18(i), generalized to any
commutative ring and any scalar. -/
theorem sup_span_eq_top_iff_surjective_mul {R : Type*} [CommRing R]
    (I : Ideal R) (r : R) : I ⊔ Ideal.span {r} = ⊤ ↔
      Function.Surjective (fun x : R ⧸ I ↦ Ideal.Quotient.mk I r * x) := by
  constructor
  · intro h y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨i, hi, s, hs, his⟩ := Submodule.mem_sup.mp (h.symm ▸ Submodule.mem_top : (1 : R) ∈ _)
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    refine ⟨Ideal.Quotient.mk I (t * z), ?_⟩
    have hmk : Ideal.Quotient.mk I i = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hi
    have h1 : Ideal.Quotient.mk I (i + t * r) = 1 := by rw [his, map_one]
    rw [map_add, hmk, zero_add] at h1
    calc Ideal.Quotient.mk I r * Ideal.Quotient.mk I (t * z)
        = Ideal.Quotient.mk I (t * r) * Ideal.Quotient.mk I z := by
          simp only [← map_mul]
          ring_nf
      _ = Ideal.Quotient.mk I z := by rw [h1, one_mul]
  · intro h
    obtain ⟨x, hx⟩ := h 1
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    dsimp only at hx
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hx
    rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
    have h1 : (1 : R) = r * s - (r * s - 1) := by ring
    rw [h1]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right (Ideal.mul_mem_right s _
      (Ideal.subset_span rfl))) (Submodule.mem_sup_left hx)

/-- Cox, Lemma 7.18(i): the scalar ideal-sum criterion for a finite quotient. -/
theorem sup_span_natCast_eq_top_iff_coprime_card {R : Type*} [CommRing R]
    (I : Ideal R) [Finite (R ⧸ I)] (n : ℕ) :
    I ⊔ Ideal.span {(n : R)} = ⊤ ↔ (Nat.card (R ⧸ I)).Coprime n := by
  rw [sup_span_eq_top_iff_surjective_mul, Finite.surjective_iff_bijective,
    ← bijective_nsmul_iff_coprime_card]
  have e : (fun x : R ⧸ I ↦ Ideal.Quotient.mk I (n : R) * x) = fun x ↦ n • x := by
    funext x
    rw [map_natCast, nsmul_eq_mul]
  rw [e]

end Cox.OrderCoprimality
