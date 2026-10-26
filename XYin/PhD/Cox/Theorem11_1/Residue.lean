/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Module.Lattice
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Over

/-!
# Finite index and residue fields in Cox Theorem 11.1

These declarations state the finite-index argument of Exercise 11.21 and the finite exception
argument on pp. 238–239.
-/

open NumberField

noncomputable section

namespace Cox

/-- The field denoted `K(j(a))` by Cox, p. 238, with a general generator. -/
def generatedField (K : IntermediateField ℚ ℂ) (x : ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ((K : Set ℂ) ∪ {x})

/-- Source: Cox, p. 238, definition of `M = K(j(a))`. -/
theorem le_generatedField (K : IntermediateField ℚ ℂ) (x : ℂ) :
    K ≤ generatedField K x :=
  fun _ hy => IntermediateField.subset_adjoin ℚ _ (Or.inl hy)

/-- Source: Cox, p. 238, definition of `M = K(j(a))`. -/
theorem mem_generatedField (K : IntermediateField ℚ ℂ) (x : ℂ) :
    x ∈ generatedField K x :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr rfl)

/-- Source: Cox, p. 238, generated-field universal property. -/
theorem generatedField_le_iff (K L : IntermediateField ℚ ℂ) (x : ℂ) :
    generatedField K x ≤ L ↔ K ≤ L ∧ x ∈ L := by
  rw [generatedField, IntermediateField.adjoin_le_iff, Set.union_subset_iff,
    Set.singleton_subset_iff]
  rfl

/-- Source: Cox, p. 238, adjoining one generator to `K`. -/
theorem generatedField_eq_sup (K : IntermediateField ℚ ℂ) (x : ℂ) :
    generatedField K x = K ⊔ IntermediateField.adjoin ℚ {x} := by
  refine le_antisymm ((generatedField_le_iff _ _ _).mpr ⟨le_sup_left, ?_⟩)
    (sup_le (le_generatedField K x) ((IntermediateField.adjoin_le_iff).mpr
      (Set.singleton_subset_iff.mpr (mem_generatedField K x))))
  exact (le_sup_right : IntermediateField.adjoin ℚ {x} ≤ _)
    (IntermediateField.subset_adjoin ℚ _ rfl)

/-- Source: Cox, pp. 237–238, integrality implies finiteness of the generated field. -/
theorem generatedField_numberField (K : IntermediateField ℚ ℂ) [NumberField K]
    (x : ℂ) (hx : IsIntegral ℤ x) : NumberField (generatedField K x) := by
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
    IntermediateField.adjoin.finiteDimensional (hx.tower_top (A := ℚ))
  rw [generatedField_eq_sup]
  exact { }

/-- The suborder `O_K[x]` inside `O_(K(x))`; Cox, Exercise 11.21(a), p. 248. -/
def generatedIntegerOrder (K : IntermediateField ℚ ℂ) (x : ℂ) :
    Subalgebra ℤ (𝓞 (generatedField K x)) :=
  Algebra.adjoin ℤ {z | (((z : generatedField K x) : ℂ) ∈ K) ∨
    (((z : generatedField K x) : ℂ) = x)}

/-- Source: Cox, Exercise 11.21(a), p. 248, generators of `O_K[x]`. -/
theorem mem_generatedIntegerOrder (K : IntermediateField ℚ ℂ) (x : ℂ)
    (z : 𝓞 (generatedField K x))
    (hz : (((z : generatedField K x) : ℂ) ∈ K) ∨
      (((z : generatedField K x) : ℂ) = x)) :
    z ∈ generatedIntegerOrder K x :=
  Algebra.subset_adjoin hz

/-- Source: Cox, Exercise 11.21(a), p. 248: regard the suborder as a lattice in its field. -/
def generatedIntegerLattice (K : IntermediateField ℚ ℂ) (x : ℂ) :
    Submodule ℤ (generatedField K x) :=
  (generatedIntegerOrder K x).toSubmodule.map
    (algebraMap (𝓞 (generatedField K x)) (generatedField K x)).toAddMonoidHom.toIntLinearMap

/-- Source: Cox, Exercise 11.21(a), p. 248: the suborder is a finitely generated subgroup. -/
theorem generatedIntegerLattice_fg (K : IntermediateField ℚ ℂ) (x : ℂ)
    [NumberField (generatedField K x)] : (generatedIntegerLattice K x).FG :=
  (IsNoetherian.noetherian _).map _

/-- Source: Cox, Exercise 11.21(a), p. 248: rational generation by the integral generators. -/
theorem generatedIntegerOrder_adjoin (K : IntermediateField ℚ ℂ) [NumberField K]
    (x : ℂ) (hx : IsIntegral ℤ x) [NumberField (generatedField K x)] :
    Algebra.adjoin ℚ ((algebraMap (𝓞 (generatedField K x)) (generatedField K x)) ''
      (generatedIntegerOrder K x : Set (𝓞 (generatedField K x)))) = ⊤ := by
  set L := generatedField K x
  set T := Algebra.adjoin ℚ ((algebraMap (𝓞 L) L) '' (generatedIntegerOrder K x : Set (𝓞 L)))
  have hgen : ∀ z : L, ((z : ℂ) ∈ K ∨ (z : ℂ) = x) → z ∈ T := by
    intro z hz
    rcases hz with hzK | hzx
    · obtain ⟨d, hd0, hdint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr
        (Algebra.IsAlgebraic.isAlgebraic z)).exists_integral_multiple
      let w : 𝓞 L := ⟨d • z, hdint⟩
      have hw : w ∈ generatedIntegerOrder K x := mem_generatedIntegerOrder K x w (Or.inl (by
        change ((d • z : L) : ℂ) ∈ K
        simpa using K.zsmul_mem hzK d))
      have hdz : (d : ℚ) • z ∈ T := by
        have h1 : algebraMap (𝓞 L) L w ∈ T := Algebra.subset_adjoin (Set.mem_image_of_mem _ hw)
        have h2 : algebraMap (𝓞 L) L w = (d : ℚ) • z := by
          change d • z = (d : ℚ) • z
          rw [Int.cast_smul_eq_zsmul]
        rwa [h2] at h1
      have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
      simpa [smul_smul, inv_mul_cancel₀ hd0'] using T.smul_mem hdz (d : ℚ)⁻¹
    · have hzint : IsIntegral ℤ z :=
        (isIntegral_algHom_iff (L.val.restrictScalars ℤ) Subtype.val_injective (x := z)).mp
          (by simpa [hzx] using hx)
      exact Algebra.subset_adjoin (Set.mem_image_of_mem _
        (mem_generatedIntegerOrder K x ⟨z, hzint⟩ (Or.inr hzx)))
  have halg : ∀ c ∈ (K : Set ℂ) ∪ {x}, IsAlgebraic ℚ c := by
    rintro c (hc | rfl)
    · exact (Algebra.IsAlgebraic.isAlgebraic (⟨c, hc⟩ : K)).algHom K.val
    · exact (hx.tower_top (A := ℚ)).isAlgebraic
  have hL : L.toSubalgebra = Algebra.adjoin ℚ ((K : Set ℂ) ∪ {x}) :=
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg
  have hLsub : L.toSubalgebra ≤ T.map L.val := by
    rw [hL]
    refine Algebra.adjoin_le ?_
    rintro c (hc | rfl)
    · exact ⟨⟨c, le_generatedField K _ hc⟩, hgen _ (Or.inl hc), rfl⟩
    · exact ⟨⟨_, mem_generatedField K _⟩, hgen _ (Or.inr rfl), rfl⟩
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨t, ht, htz⟩ := hLsub z.2
  rwa [← Subtype.val_injective htz]

/-- Source: Cox, Exercise 11.21(a), p. 248: rational algebra generation equals rational span. -/
theorem generatedIntegerLattice_span_eq_adjoin (K : IntermediateField ℚ ℂ) (x : ℂ) :
    Submodule.span ℚ (generatedIntegerLattice K x : Set (generatedField K x)) =
      (Algebra.adjoin ℚ ((algebraMap (𝓞 (generatedField K x)) (generatedField K x)) ''
        (generatedIntegerOrder K x : Set (𝓞 (generatedField K x))))).toSubmodule := by
  rw [Algebra.adjoin_eq_span]
  congr 1
  have h : (algebraMap (𝓞 (generatedField K x)) (generatedField K x)) ''
      (generatedIntegerOrder K x : Set (𝓞 (generatedField K x))) =
      (((generatedIntegerOrder K x).toSubmonoid.map
        (algebraMap (𝓞 (generatedField K x)) (generatedField K x)) :
          Submonoid (generatedField K x)) : Set (generatedField K x)) := by
    rw [Submonoid.coe_map]
    rfl
  rw [h, Submonoid.closure_eq, ← h, generatedIntegerLattice, Submodule.map_coe]
  rfl

/-- Source: Cox, Exercise 11.21(a), p. 248: rational powers of the generator span `K(x)`. -/
theorem generatedIntegerLattice_span (K : IntermediateField ℚ ℂ) [NumberField K]
    (x : ℂ) (hx : IsIntegral ℤ x) [NumberField (generatedField K x)] :
    Submodule.span ℚ (generatedIntegerLattice K x : Set (generatedField K x)) = ⊤ := by
  rw [generatedIntegerLattice_span_eq_adjoin, generatedIntegerOrder_adjoin K x hx,
    Algebra.top_toSubmodule]

/-- Source: Cox, Exercise 11.21(a), p. 248, full rank of `O_K[x]`. -/
theorem generatedIntegerOrder_finrank (K : IntermediateField ℚ ℂ) [NumberField K]
    (x : ℂ) (hx : IsIntegral ℤ x) [NumberField (generatedField K x)] :
    Module.finrank ℤ (generatedIntegerOrder K x) =
      Module.finrank ℤ (𝓞 (generatedField K x)) := by
  haveI : Submodule.IsLattice ℚ (generatedIntegerLattice K x) :=
    ⟨generatedIntegerLattice_fg K x, generatedIntegerLattice_span K x hx⟩
  have h := congrArg Cardinal.toNat
    (Submodule.IsLattice.rank' (K := ℚ) (generatedIntegerLattice K x))
  rw [← Module.finrank, ← Module.finrank] at h
  rw [NumberField.RingOfIntegers.rank, ← h]
  exact (Submodule.equivMapOfInjective _ (IsFractionRing.injective (𝓞 (generatedField K x))
    (generatedField K x)) (generatedIntegerOrder K x).toSubmodule).finrank_eq

/-- Source: Cox, Exercise 11.21(a), p. 248, full rank gives finite index. -/
theorem finite_quotient_generatedIntegerOrder (K : IntermediateField ℚ ℂ)
    [NumberField K] (x : ℂ) (hx : IsIntegral ℤ x)
    [NumberField (generatedField K x)] :
    Finite ((𝓞 (generatedField K x)) ⧸ (generatedIntegerOrder K x).toSubmodule) := by
  exact Submodule.finiteQuotientOfFreeOfRankEq _ (generatedIntegerOrder_finrank K x hx)

/-- Source: Cox, Exercise 11.21(b), p. 248, the index annihilates the quotient. -/
theorem exists_pos_nsmul_mem (A : Type*) [CommRing A] (S : Subalgebra ℤ A)
    [Finite (A ⧸ S.toSubmodule)] :
    ∃ d : ℕ, 0 < d ∧ ∀ x : A, d • x ∈ S := by
  haveI : Finite (A ⧸ S.toSubmodule.toAddSubgroup) := ‹Finite (A ⧸ S.toSubmodule)›
  exact ⟨S.toSubmodule.toAddSubgroup.index,
    Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite,
    fun x => S.toSubmodule.toAddSubgroup.nsmul_index_mem x⟩

/-- Source: Cox, Exercise 11.21(b), p. 248, extend Frobenius from generators. -/
theorem pow_eq_on_adjoin {A F : Type*} [CommRing A] [CommRing F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (f : A →+* F) (s : Set A)
    (hs : ∀ x ∈ s, (f x) ^ p = f x) :
    ∀ x ∈ Algebra.adjoin ℤ s, (f x) ^ p = f x := by
  have hint : ∀ n : ℤ, (n : F) ^ p = n := fun n => by
    rw [← map_intCast (ZMod.castHom (dvd_refl p) F) n, ← map_pow, ZMod.pow_card]
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap n => simpa using hint n
  | add x y _ _ hx hy => rw [map_add, add_pow_char, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, mul_pow, hx, hy]

/-- Source: Cox, Exercise 11.21(b), p. 248, cancel an index prime to `p`. -/
theorem pow_eq_of_nsmul_mem {A F : Type*} [CommRing A] [Field F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (f : A →+* F) (S : Subalgebra ℤ A)
    (d : ℕ) (hd : ¬ p ∣ d) (hS : ∀ x ∈ S, (f x) ^ p = f x)
    (hindex : ∀ x : A, d • x ∈ S) (x : A) : (f x) ^ p = f x := by
  have hint : ∀ n : ℕ, (n : F) ^ p = n := fun n => by
    rw [← map_natCast (ZMod.castHom (dvd_refl p) F) n, ← map_pow, ZMod.pow_card]
  have hd0 : (d : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F p]
    exact hd
  have h := hS _ (hindex x)
  rw [nsmul_eq_mul, map_mul, map_natCast, mul_pow, hint] at h
  exact mul_left_cancel₀ hd0 h

/-- Source: Cox, p. 238, paragraph after (11.30): the residue field is `F_p`. -/
theorem card_eq_prime_of_forall_pow_eq (F : Type*) [Field F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hF : ∀ x : F, x ^ p = x) :
    Nat.card F = p := by
  classical
  have hp := (Fact.out : p.Prime)
  set q : Polynomial F := Polynomial.X ^ p - Polynomial.X with hq
  have hq0 : q ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hp.one_lt
  have hroots : ∀ x : F, x ∈ q.roots := fun x => by
    rw [Polynomial.mem_roots hq0, Polynomial.IsRoot, hq, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hF, sub_self]
  have hfin : (Set.univ : Set F).Finite :=
    q.roots.toFinset.finite_toSet.subset fun x _ => Multiset.mem_toFinset.mpr (hroots x)
  haveI : Finite F := Set.finite_univ_iff.mp hfin
  haveI : Fintype F := Fintype.ofFinite F
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    calc Fintype.card F ≤ q.roots.toFinset.card :=
          Finset.card_le_card_of_injOn id (fun x _ => Multiset.mem_toFinset.mpr (hroots x))
            (fun _ _ _ _ h => h)
      _ ≤ q.roots.card := Multiset.toFinset_card_le _
      _ ≤ q.natDegree := Polynomial.card_roots' q
      _ = p := FiniteField.X_pow_card_sub_X_natDegree_eq F hp.one_lt
  · have h := Nat.card_le_card_of_injective (ZMod.castHom (dvd_refl p) F)
      (ZMod.castHom (dvd_refl p) F).injective
    rwa [Nat.card_zmod] at h

/-- Source: Cox, p. 238, exclude the prime divisors of the finite index. -/
theorem finite_prime_divisors (d : ℕ) (hd : d ≠ 0) :
    {p : ℕ | p.Prime ∧ p ∣ d}.Finite :=
  (Nat.primeFactors d).finite_toSet.subset fun _ hp => Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, hd⟩

/-- Source: Cox, p. 239, finitely many prime ideals divide a nonzero difference. -/
theorem finite_ideals_containing_difference (L : IntermediateField ℚ ℂ) [NumberField L]
    (x y : 𝓞 L) (hxy : x ≠ y) : {P : Ideal (𝓞 L) | x - y ∈ P}.Finite := by
  have hN : Algebra.norm ℤ (x - y) ≠ 0 :=
    (Algebra.norm_ne_zero_iff).mpr (sub_ne_zero.mpr hxy)
  refine (Ideal.finite_setOf_absNorm_le (Algebra.norm ℤ (x - y)).natAbs).subset fun P hP => ?_
  have h := Ideal.absNorm_dvd_norm_of_mem hP
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hN) (Int.natCast_dvd.mp h)

/-- Source: Cox, p. 239; the norm of the contracted rational prime ideal is `p`. -/
theorem absNorm_under_eq_prime (L : IntermediateField ℚ ℂ) [NumberField L]
    (p : ℕ) (_hp : p.Prime) (P : Ideal (𝓞 L))
    (hP : P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L)) :
    Ideal.absNorm (P.under ℤ) = p := by
  haveI := hP.2
  rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}), Ideal.absNorm_span_singleton]
  simp

/-- Source: Cox, p. 239: a finite family of prime ideals lies over finitely many rational primes. -/
theorem finite_primes_below_finite_ideals (L : IntermediateField ℚ ℂ) [NumberField L]
    (s : Set (Ideal (𝓞 L))) (hs : s.Finite) :
    {p : ℕ | p.Prime ∧ ∃ P ∈ s,
      P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L)}.Finite := by
  refine (hs.image fun P => Ideal.absNorm (P.under ℤ)).subset ?_
  rintro p ⟨hp, P, hPs, hP⟩
  exact ⟨P, hPs, absNorm_under_eq_prime L p hp P hP⟩

/-- Source: Cox, p. 239, choose one finite exceptional set for all pairs of class values. -/
theorem finite_collision_primes (L : IntermediateField ℚ ℂ) [NumberField L]
    {ι : Type*} [Finite ι] (j : ι → 𝓞 L) (hj : Function.Injective j) :
    ∃ e : Set ℕ, e.Finite ∧ ∀ p ∉ e, p.Prime →
      ∀ P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L),
        Function.Injective (fun i ↦ Ideal.Quotient.mk P (j i)) := by
  let S : Set (Ideal (𝓞 L)) := ⋃ (i : ι) (k : ι) (_ : i ≠ k), {P | j i - j k ∈ P}
  have hS : S.Finite := Set.finite_iUnion fun i => Set.finite_iUnion fun k =>
    Set.finite_iUnion fun hik => finite_ideals_containing_difference L _ _ (hj.ne hik)
  refine ⟨_, finite_primes_below_finite_ideals L S hS, fun p hpe hp P hP i k hik => ?_⟩
  by_contra hne
  exact hpe ⟨hp, P, Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr
    ⟨hne, Ideal.Quotient.eq.mp hik⟩⟩⟩, hP⟩

end Cox
