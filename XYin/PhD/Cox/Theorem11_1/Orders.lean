/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.Algebra.Module.Lattice
import Mathlib.Data.Nat.Squarefree
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Ideal.Basis
import XYin.PhD.Cox.Arithmetic
import XYin.PhD.Cox.Theorem11_1.OrderArithmetic
import XYin.PhD.Cox.Theorem11_1.OrderCoprimality

/-!
# Quadratic orders and their ideal lattices

The definitions record orders as actual subalgebras and properness by the multiplier-ring
condition. The class group is Mathlib's group of invertible fractional ideals modulo principal
ideals. No Dedekind-domain assumption is imposed on a nonmaximal order.

The conductor-generator declarations from `discr_neg` to `exists_nonsquare_diagonal_root` are
deferred and still use `sorry`.
-/

open scoped nonZeroDivisors Pointwise NumberField

noncomputable section

namespace Cox

/-- An embedded imaginary quadratic field; Cox, §7, pp. 133–134. -/
class IsImaginaryQuadraticField (K : IntermediateField ℚ ℂ) : Prop where
  finrank_eq_two : Module.finrank ℚ K = 2
  exists_nonreal : ∃ z : K, (z : ℂ).im ≠ 0

/-- Cox, p. 103: an imaginary quadratic field is in particular a quadratic extension. -/
instance IsImaginaryQuadraticField.isQuadraticExtension (K : IntermediateField ℚ ℂ)
    [IsImaginaryQuadraticField K] : Algebra.IsQuadraticExtension ℚ K :=
  ⟨IsImaginaryQuadraticField.finrank_eq_two⟩

/-- An order is a finite integral lattice spanning its ambient field; Cox, §7.A, p. 133. -/
class IsOrder {K : IntermediateField ℚ ℂ} (O : Subalgebra ℤ K) : Prop where
  fg : O.toSubmodule.FG
  span_eq_top : Submodule.span ℚ (O : Set K) = ⊤

namespace Order

variable {K : IntermediateField ℚ ℂ}

/-- Cox, definition of an order, p. 133, condition (ii). -/
instance moduleFinite (O : Subalgebra ℤ K) [NumberField K]
    [hO' : IsOrder O] : Module.Finite ℤ O :=
  Module.Finite.of_fg hO'.fg

/-- Cox, definition of an order, p. 133, torsion-free lattice observation. -/
instance moduleFree (O : Subalgebra ℤ K) [NumberField K]
    [IsOrder O] : Module.Free ℤ O :=
  Module.free_of_finite_type_torsion_free'

section DenominatorContext

variable [hNF : NumberField K]
variable (O : Subalgebra ℤ K) [hO : IsOrder O]
variable [hIQ : IsImaginaryQuadraticField K]

include hNF hO
omit hIQ

omit hNF in
/-- Cox, the fraction-field observation following the order definition, p. 133:
clear the denominators of a rational spanning expression. -/
theorem exists_pos_nat_mul_mem (x : K) : ∃ n : ℕ, 0 < n ∧ (n : K) * x ∈ O := by
  have hx : x ∈ Submodule.span ℚ (O : Set K) := by rw [hO.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by simpa using hy⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hmy⟩ := hy
    obtain ⟨n, hn, hnz⟩ := hz
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have h : ((m * n : ℕ) : K) * (y + z) = (n : K) * ((m : K) * y) + (m : K) * ((n : K) * z) := by
      push_cast; ring
    rw [h]
    exact O.add_mem (O.mul_mem (natCast_mem O n) hmy) (O.mul_mem (natCast_mem O m) hnz)
  | smul q y _ hy =>
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨n * q.den, Nat.mul_pos hn q.den_pos, ?_⟩
    have hd : (q.den : K) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have h : ((n * q.den : ℕ) : K) * (q • y) = (q.num : K) * ((n : K) * y) := by
      rw [Rat.smul_def, Rat.cast_def]
      push_cast
      field_simp
    rw [h]
    exact O.mul_mem (intCast_mem O q.num) hny

end DenominatorContext

/-- Cox, definition of an order, p. 133, fraction-field observation. -/
instance isFractionRing (O : Subalgebra ℤ K) [NumberField K]
    [IsOrder O] : IsFractionRing O K :=
  IsFractionRing.of_field O K fun z => by
    obtain ⟨n, hn, hz⟩ := exists_pos_nat_mul_mem O z
    refine ⟨⟨_, hz⟩, (n : O), ?_⟩
    have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp [Subalgebra.algebraMap_eq, hn']

/-- Cox, p. 133, rational localization of the integral order lattice. -/
instance isLocalizationIntegers (O : Subalgebra ℤ K) [NumberField K]
    [IsOrder O] :
    IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ)) K := by
  refine (isLocalization_iff _ _).mpr ⟨?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · rintro ⟨_, m, hm, rfl⟩
    exact IsUnit.mk0 _ (by simpa using nonZeroDivisors.ne_zero hm)
  · obtain ⟨n, hn, hz⟩ := exists_pos_nat_mul_mem O z
    refine ⟨(⟨_, hz⟩, ⟨(n : O), (n : ℤ), ?_, by simp⟩), ?_⟩
    · exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')
    · simp [Subalgebra.algebraMap_eq, mul_comm]
  · simpa [Subalgebra.algebraMap_eq] using h

section LatticeContext

variable [hNF : NumberField K]
variable (O : Subalgebra ℤ K) [hO : IsOrder O]
variable [hIQ : IsImaginaryQuadraticField K]

include hNF hO
omit hIQ

omit hNF in
/-- Cox, Exercise 7.2, cited on p. 133: every order element is integral. -/
theorem isIntegral_of_mem {x : K} (hx : x ∈ O) : IsIntegral ℤ x :=
  IsIntegral.of_mem_of_fg O hO.fg x hx

omit hNF in
/-- The full order lattice has the ambient rational degree as its integer rank;
Cox, the rank assertion in the order definition, p.133, before specializing to degree two. -/
theorem finrank_eq_degree : Module.finrank ℤ O = Module.finrank ℚ K := by
  haveI : Submodule.IsLattice ℚ O.toSubmodule := ⟨hO.fg, hO.span_eq_top⟩
  exact congrArg Cardinal.toNat (Submodule.IsLattice.rank' (K := ℚ) O.toSubmodule)

omit hNF in
/-- Cox, Exercise 7.1, cited on p. 133: a quadratic order has rank two. -/
theorem finrank [Algebra.IsQuadraticExtension ℚ K] : Module.finrank ℤ O = 2 := by
  rw [finrank_eq_degree O, Algebra.IsQuadraticExtension.finrank_eq_two]

/-- Properness is equality with the multiplier ring of a nonzero fractional ideal;
Cox, §7.A, pp. 134–135. -/
def IsProper (I : FractionalIdeal O⁰ K) : Prop :=
  I ≠ 0 ∧ ∀ x : K, (∀ y ∈ I, x * y ∈ I) ↔ x ∈ O

omit hNF hO in
/-- Cox, definition of fractional ideals and properness, p. 135. -/
theorem IsProper.ne_zero {I : FractionalIdeal O⁰ K} (hI : IsProper O I) : I ≠ 0 :=
  hI.1

omit hNF hO in
/-- Cox, multiplier-ring characterization of properness, pp. 134–135. -/
theorem IsProper.multiplier_iff {I : FractionalIdeal O⁰ K} (hI : IsProper O I) (x : K) :
    (∀ y ∈ I, x * y ∈ I) ↔ x ∈ O :=
  hI.2 x

omit hNF hO in
/-- Cox, Proposition 7.4, p. 135, invertibility implies properness. -/
theorem isProper_of_isUnit {I : FractionalIdeal O⁰ K} (hI : IsUnit I) : IsProper O I := by
  obtain ⟨u, rfl⟩ := hI
  refine ⟨u.ne_zero, fun x => ⟨fun hx => ?_, fun hx y hy => ?_⟩⟩
  · have h1 : (1 : K) ∈ ((u : Submodule O K) * (↑u⁻¹ : FractionalIdeal O⁰ K) : Submodule O K) := by
      rw [← FractionalIdeal.coe_mul, u.mul_inv]
      exact FractionalIdeal.one_mem_one _
    have h2 : x * 1 ∈ ((u : Submodule O K) * (↑u⁻¹ : FractionalIdeal O⁰ K) : Submodule O K) := by
      refine Submodule.mul_induction_on (C := fun z => x * z ∈
        ((u : Submodule O K) * (↑u⁻¹ : FractionalIdeal O⁰ K) : Submodule O K)) h1 ?_ ?_
      · intro a ha b hb
        rw [← mul_assoc]
        exact Submodule.mul_mem_mul (hx a ha) hb
      · intro a b ha hb
        rw [mul_add]
        exact Submodule.add_mem _ ha hb
    rw [mul_one, ← FractionalIdeal.coe_mul, u.mul_inv] at h2
    obtain ⟨x', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h2
    simp [Subalgebra.algebraMap_eq]
  · simpa [Algebra.smul_def, Subalgebra.algebraMap_eq] using
      Submodule.smul_mem (u : Submodule O K) (⟨x, hx⟩ : O) hy

omit hNF hO in
/-- Cox, Lemma 7.5, pp. 135–136, the multiplier calculation for a normalized lattice. -/
theorem normalized_multiplier_iff (τ : K) (hτ : LinearIndependent ℚ ![1, τ])
    (A B C : ℤ) (_hA : A ≠ 0) (hq : (A : K) * τ ^ 2 + B * τ + C = 0)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1) (x : K) :
    (∀ y ∈ Submodule.span ℤ ({1, τ} : Set K),
      x * y ∈ Submodule.span ℤ ({1, τ} : Set K)) ↔
      x ∈ Submodule.span ℤ ({1, (A : K) * τ} : Set K) := by
  constructor
  · intro hx
    have h1 := hx 1 (Submodule.subset_span (by simp))
    rw [mul_one] at h1
    obtain ⟨m, n, hmn⟩ := Submodule.mem_span_pair.mp h1
    have hx' : x = (m : K) + n * τ := by rw [← hmn]; simp [zsmul_eq_mul]
    have h2 := hx τ (Submodule.subset_span (by simp))
    rw [hx'] at h2
    obtain ⟨k, rfl⟩ := OrderArithmetic.dvd_of_primitive_triple A B C n hprim
      (OrderArithmetic.dvd_linear_of_mul_tau_mem τ hτ A B C m n hq h2)
      (OrderArithmetic.dvd_constant_of_mul_tau_mem τ hτ A B C m n hq h2)
    refine Submodule.mem_span_pair.mpr ⟨m, k, ?_⟩
    rw [hx']
    push_cast
    simp only [zsmul_eq_mul, mul_one]
    ring
  · intro hx y hy
    obtain ⟨m, k, hmk⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hy
    have hx' : x = (m : K) + ((A * k : ℤ) : K) * τ := by
      rw [← hmk]
      push_cast
      simp only [zsmul_eq_mul, mul_one]
      ring
    have hxτ := OrderArithmetic.mul_tau_mem_of_dvd τ A B C m (A * k) hq (dvd_mul_right A k)
    rw [← hx'] at hxτ
    have hxs : x ∈ Submodule.span ℤ ({1, τ} : Set K) :=
      Submodule.mem_span_pair.mpr ⟨m, A * k, by rw [hx']; simp [zsmul_eq_mul]⟩
    have hxy : x * y = a • x + b • (x * τ) := by
      rw [← hab]
      simp only [zsmul_eq_mul, mul_one]
      ring
    rw [hxy]
    exact Submodule.add_mem _ (Submodule.smul_mem _ a hxs) (Submodule.smul_mem _ b hxτ)

omit hNF hO in
/-- Cox, Proposition 7.4, p. 136, expansion of the product in equation (7.6). -/
theorem normalized_span_mul_generators (τ : K) (A B C : ℤ) (hA : A ≠ 0)
    (hq : (A : K) * τ ^ 2 + B * τ + C = 0) :
    (A : K) • (Submodule.span ℤ ({1, τ} : Set K) *
      Submodule.span ℤ ({1, -(B : K) / A - τ} : Set K)) =
        Submodule.span ℤ ({(A : K), (A : K) * τ, -(B : K), (C : K)} : Set K) := by
  have hA' : (A : K) ≠ 0 := Int.cast_ne_zero.mpr hA
  set τ' : K := -(B : K) / A - τ with hτ'
  have e1 : (A : K) * (1 * τ') = -(B : K) - A * τ := by rw [hτ']; field_simp
  have e2 : (A : K) * (τ * τ') = C := by
    rw [hτ']; field_simp; linear_combination -hq
  rw [Submodule.span_mul_span, Submodule.smul_span]
  have mem : ∀ s ∈ ({1, τ} : Set K), ∀ u ∈ ({1, τ'} : Set K),
      (A : K) * (s * u) ∈ Submodule.span ℤ ((A : K) • (({1, τ} : Set K) * {1, τ'})) :=
    fun s hs u hu => Submodule.subset_span (Set.smul_mem_smul_set (Set.mul_mem_mul hs hu))
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hz
    obtain ⟨s, hs, u, hu, rfl⟩ := Set.mem_mul.mp hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hu
    rw [smul_eq_mul, SetLike.mem_coe]
    rcases hs with hs | hs <;> rcases hu with hu | hu <;> subst s <;> subst u
    · simpa using Submodule.subset_span (R := ℤ) (by simp : (A : K) ∈
        ({(A : K), (A : K) * τ, -(B : K), (C : K)} : Set K))
    · rw [e1]
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
    · simpa using Submodule.subset_span (R := ℤ) (by simp : (A : K) * τ ∈
        ({(A : K), (A : K) * τ, -(B : K), (C : K)} : Set K))
    · rw [e2]
      exact Submodule.subset_span (by simp)
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · simpa using mem 1 (by simp) 1 (by simp)
    · simpa using mem τ (by simp) 1 (by simp)
    · have h := Submodule.add_mem _ (mem 1 (by simp) τ' (by simp)) (mem τ (by simp) 1 (by simp))
      rwa [e1, mul_one, sub_add_cancel] at h
    · simpa [e2] using mem τ (by simp) τ' (by simp)

omit hNF hO in
/-- Cox, Proposition 7.4, p. 136, the primitive-coefficient step in equation (7.6). -/
theorem primitive_normalized_span (τ : K) (A B C : ℤ)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1) :
    Submodule.span ℤ ({(A : K), (A : K) * τ, -(B : K), (C : K)} : Set K) =
      Submodule.span ℤ ({1, (A : K) * τ} : Set K) := by
  have hg : Int.gcd (Int.gcd A B : ℤ) C = 1 := by simpa [Int.gcd] using hprim
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, (Int.gcd A B : ℤ) = A * a + B * b :=
    ⟨_, _, Int.gcd_eq_gcd_ab A B⟩
  obtain ⟨c, d, hcd⟩ : ∃ c d : ℤ, (1 : ℤ) = (Int.gcd A B : ℤ) * c + C * d :=
    ⟨_, _, by rw [← Int.gcd_eq_gcd_ab, hg, Nat.cast_one]⟩
  rw [hab] at hcd
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Submodule.mem_span_pair.mpr ⟨A, 0, by simp⟩
    · exact Submodule.subset_span (by simp)
    · exact Submodule.mem_span_pair.mpr ⟨-B, 0, by simp⟩
    · exact Submodule.mem_span_pair.mpr ⟨C, 0, by simp⟩
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have h1 : (1 : K) = (a * c) • (A : K) + (-(b * c)) • (-(B : K)) + d • (C : K) := by
        have h := congrArg (fun z : ℤ => (z : K)) hcd
        push_cast at h
        rw [h]
        simp only [zsmul_eq_mul]
        push_cast
        ring
      rw [SetLike.mem_coe, h1]
      exact Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · exact Submodule.subset_span (by simp)

omit hNF hO in
/-- Cox, Proposition 7.4, p. 136, expansion of the product in equation (7.6). -/
theorem normalized_span_mul (τ : K) (A B C : ℤ) (hA : A ≠ 0)
    (hq : (A : K) * τ ^ 2 + B * τ + C = 0)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1) :
    Submodule.span ℤ ({1, τ} : Set K) *
        Submodule.span ℤ ({1, -(B : K) / A - τ} : Set K) =
      (A : K)⁻¹ • Submodule.span ℤ ({1, (A : K) * τ} : Set K) := by
  rw [← primitive_normalized_span τ A B C hprim, ← normalized_span_mul_generators τ A B C hA hq,
    inv_smul_smul₀ (Int.cast_ne_zero.mpr hA)]

end LatticeContext

/-- Cox, Exercises 7.4 and 7.7, p. 135: a bounded-denominator ideal is a finite integer module. -/
instance fractionalIdeal_moduleFinite (O : Subalgebra ℤ K) [NumberField K]
    [IsOrder O]
    (I : FractionalIdeal O⁰ K) :
    Module.Finite ℤ (I : Submodule O K) := by
  haveI : IsNoetherianRing O := isNoetherian_of_tower ℤ inferInstance
  letI : Module O (I : Submodule O K) := (I : Submodule O K).module
  haveI : IsNoetherian O (I : Submodule O K) := FractionalIdeal.isNoetherian I
  exact Module.Finite.trans O (I : Submodule O K)

/-- Cox, Exercise 7.8, p. 136: an ideal is torsion free over the integers. -/
instance fractionalIdeal_moduleFree (O : Subalgebra ℤ K) [NumberField K]
    [IsOrder O]
    (I : FractionalIdeal O⁰ K) :
    Module.Free ℤ (I : Submodule O K) :=
  Module.free_of_finite_type_torsion_free'

section RemainingOrderContext

variable [hNF : NumberField K]
variable (O : Subalgebra ℤ K) [hO : IsOrder O]
variable [hIQ : IsImaginaryQuadraticField K]

include hNF hO
omit hIQ

omit hNF in
/-- Cox, Exercise 7.8, used on p. 136: a nonzero ideal spans its fraction field. -/
theorem fractionalIdeal_span (I : FractionalIdeal O⁰ K) (hI : I ≠ 0) :
    Submodule.span ℚ (I : Set K) = ⊤ := by
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
  rw [eq_top_iff]
  intro y _
  have h1 : x⁻¹ * y ∈ Submodule.span ℚ (O : Set K) := by rw [hO.span_eq_top]; trivial
  have h2 := Submodule.smul_mem_pointwise_smul _ x _ h1
  rw [Submodule.smul_span, smul_eq_mul, mul_inv_cancel_left₀ hx0] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨o, ho, rfl⟩
  have := Submodule.smul_mem (I : Submodule O K) (⟨o, ho⟩ : O) hxI
  simpa [Algebra.smul_def, Subalgebra.algebraMap_eq, mul_comm] using this

/-- Cox, Exercise 7.8, used in the proof of Proposition 7.4 on p. 136. -/
theorem fractionalIdeal_finrank [Algebra.IsQuadraticExtension ℚ K]
    (I : FractionalIdeal O⁰ K) (hI : I ≠ 0) :
    Module.finrank ℤ (I : Submodule O K) = 2 := by
  haveI : Submodule.IsLattice ℚ ((I : Submodule O K).restrictScalars ℤ) :=
    ⟨Module.Finite.iff_fg.mp (fractionalIdeal_moduleFinite O I), fractionalIdeal_span O I hI⟩
  have h := Submodule.IsLattice.rank' (K := ℚ) ((I : Submodule O K).restrictScalars ℤ)
  have h2 := congrArg Cardinal.toNat h
  rw [← Module.finrank, ← Module.finrank, Algebra.IsQuadraticExtension.finrank_eq_two] at h2
  exact h2

/-- Cox, Proposition 7.4, p. 136: normalize a rank-two ideal basis by its first vector. -/
theorem exists_normalized_basis [Algebra.IsQuadraticExtension ℚ K]
    (I : FractionalIdeal O⁰ K) (hI : I ≠ 0) :
    ∃ (a : Kˣ) (τ : K), LinearIndependent ℚ ![1, τ] ∧
      (I : Submodule O K).restrictScalars ℤ =
        (a : K) • Submodule.span ℤ ({1, τ} : Set K) := by
  let b : Module.Basis (Fin 2) ℤ (I : Submodule O K) :=
    Module.finBasisOfFinrankEq ℤ _ (fractionalIdeal_finrank O I hI)
  set α : K := (b 0 : K) with hα_def
  set β : K := (b 1 : K) with hβ_def
  have hα : α ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
  let f : (I : Submodule O K) →ₗ[ℤ] K :=
    { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hZ : LinearIndependent ℤ ![α, β] := by
    have h := b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr fun _ _ h => Subtype.ext h)
    convert h using 1
    ext i; fin_cases i <;> rfl
  refine ⟨Units.mk0 α hα, α⁻¹ * β, ?_, ?_⟩
  · have hQ : LinearIndependent ℚ ![α, β] := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ
    have h := hQ.map' (LinearMap.mulLeft ℚ α⁻¹)
      (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ (inv_ne_zero hα)))
    convert h using 1
    ext i; fin_cases i <;> simp [hα]
  · have hspan : (I : Submodule O K).restrictScalars ℤ = Submodule.span ℤ ({α, β} : Set K) := by
      apply le_antisymm
      · intro x hx
        have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        simp only [Fin.sum_univ_two, Submodule.coe_add] at h
        rw [← h]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [hα_def])))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [hβ_def])))
      · rw [Submodule.span_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact (b 0).2
        · exact (b 1).2
    rw [hspan, Units.val_mk0, Submodule.smul_span, Set.smul_set_insert, Set.smul_set_singleton,
      smul_eq_mul, smul_eq_mul, mul_one, mul_inv_cancel_left₀ hα]

omit hNF hO in
/-- Cox, Lemma 7.5, p. 135: first express the square of a quadratic generator rationally. -/
theorem exists_rational_quadratic_relation [Algebra.IsQuadraticExtension ℚ K]
    (τ : K) (hτ : LinearIndependent ℚ ![1, τ]) :
    ∃ u v : ℚ, τ ^ 2 = (u : K) + v * τ := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ K := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]; rfl
  let bs := basisOfLinearIndependentOfCardEqFinrank hτ hcard
  refine ⟨bs.repr (τ ^ 2) 0, bs.repr (τ ^ 2) 1, ?_⟩
  have h := bs.sum_repr (τ ^ 2)
  rw [Fin.sum_univ_two] at h
  simp only [bs, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one, Rat.smul_def, mul_one] at h
  exact h.symm

omit hNF hO in
/-- Cox, Lemma 7.5, p. 135: clear the two rational denominators before normalization. -/
theorem exists_integer_quadratic_relation {F : Type*} [Field F] [CharZero F]
    (τ : F) (u v : ℚ) (hτ : τ ^ 2 = (u : F) + v * τ) :
    ∃ A B C : ℤ, A ≠ 0 ∧ (A : F) * τ ^ 2 + B * τ + C = 0 := by
  refine ⟨u.den * v.den, -(v.num * u.den), -(u.num * v.den), by positivity, ?_⟩
  have hud : (u.den : F) ≠ 0 := Nat.cast_ne_zero.mpr u.den_nz
  have hvd : (v.den : F) ≠ 0 := Nat.cast_ne_zero.mpr v.den_nz
  have hu : (u.den : F) * u = u.num := by rw [Rat.cast_def]; field_simp
  have hv : (v.den : F) * v = v.num := by rw [Rat.cast_def]; field_simp
  push_cast
  rw [hτ]
  linear_combination (v.den : F) * hu + ((u.den : F) * τ) * hv

omit hNF hO in
/-- Cox, Lemma 7.5, p. 135: the common gcd divides each of the three coefficients. -/
theorem gcd_triple_dvd (A B C x : ℤ) (hx : x ∈ ({A, B, C} : Set ℤ)) :
    (Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs : ℤ) ∣ x := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> rw [Int.natCast_dvd]
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  · exact Nat.gcd_dvd_right _ _

omit hNF hO in
/-- Cox, Lemma 7.5, p. 135: divide the integer coefficients by their positive common gcd. -/
theorem primitive_triple_div_gcd (A B C : ℤ) (hA : A ≠ 0) :
    let d : ℤ := Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs
    Nat.gcd (Nat.gcd (A / d).natAbs (B / d).natAbs) (C / d).natAbs = 1 := by
  intro d
  have hgAB : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs ∣ Nat.gcd A.natAbs B.natAbs :=
    Nat.gcd_dvd_left _ _
  have hgA := hgAB.trans (Nat.gcd_dvd_left _ _)
  have hgB := hgAB.trans (Nat.gcd_dvd_right A.natAbs B.natAbs)
  have hgC : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs ∣ C.natAbs := Nat.gcd_dvd_right _ _
  have hgpos : 0 < Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs :=
    Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hA))
  simp only [d, Int.natAbs_ediv_of_dvd (Int.natCast_dvd.mpr hgA),
    Int.natAbs_ediv_of_dvd (Int.natCast_dvd.mpr hgB),
    Int.natAbs_ediv_of_dvd (Int.natCast_dvd.mpr hgC), Int.natAbs_natCast]
  rw [Nat.gcd_div hgA hgB, Nat.gcd_div hgAB hgC, Nat.div_self hgpos]

omit hNF hO in
/-- Cox, Lemma 7.5, p. 135: the normalized primitive coefficients share one positive factor. -/
theorem exists_primitive_triple (A B C : ℤ) (hA : A ≠ 0) :
    ∃ (d : ℕ) (a b c : ℤ), 0 < d ∧ A = d * a ∧ B = d * b ∧ C = d * c ∧
      a ≠ 0 ∧ Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs = 1 := by
  have hgAB : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs ∣ Nat.gcd A.natAbs B.natAbs :=
    Nat.gcd_dvd_left _ _
  have hgA := Int.natCast_dvd.mpr (hgAB.trans (Nat.gcd_dvd_left _ _))
  have hgB := Int.natCast_dvd.mpr (hgAB.trans (Nat.gcd_dvd_right A.natAbs B.natAbs))
  have hgC := Int.natCast_dvd.mpr
    (Nat.gcd_dvd_right (Nat.gcd A.natAbs B.natAbs) C.natAbs)
  refine ⟨_, _, _, _, Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _
    (Int.natAbs_pos.mpr hA)), (Int.mul_ediv_cancel' hgA).symm, (Int.mul_ediv_cancel' hgB).symm,
    (Int.mul_ediv_cancel' hgC).symm, ?_, primitive_triple_div_gcd A B C hA⟩
  intro h
  apply hA
  rw [← Int.mul_ediv_cancel' hgA, h, mul_zero]

omit hNF hO in
/-- Cox, Lemma 7.5 and Proposition 7.4, pp. 135–136, primitive quadratic relation. -/
theorem exists_primitive_quadratic_relation [Algebra.IsQuadraticExtension ℚ K]
    (τ : K) (hτ : LinearIndependent ℚ ![1, τ]) :
    ∃ A B C : ℤ, A ≠ 0 ∧ (A : K) * τ ^ 2 + B * τ + C = 0 ∧
      Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1 := by
  obtain ⟨u, v, huv⟩ := exists_rational_quadratic_relation τ hτ
  obtain ⟨A, B, C, hA, hq⟩ := exists_integer_quadratic_relation τ u v huv
  obtain ⟨d, a, b, c, hd, rfl, rfl, rfl, ha, hprim⟩ := exists_primitive_triple A B C hA
  refine ⟨a, b, c, ha, ?_, hprim⟩
  have hd' : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have h : (d : K) * ((a : K) * τ ^ 2 + b * τ + c) = 0 := by
    push_cast at hq
    linear_combination hq
  exact (mul_eq_zero.mp h).resolve_left hd'

/-- Cox, Proposition 7.4, p. 136, the inverse supplied by equation (7.6). -/
theorem exists_inverse_of_isProper [Algebra.IsQuadraticExtension ℚ K]
    (I : FractionalIdeal O⁰ K) (hI : IsProper O I) :
    ∃ J : FractionalIdeal O⁰ K, I * J = 1 := by
  obtain ⟨a, τ, hτ, hIspan⟩ := exists_normalized_basis O I hI.ne_zero
  obtain ⟨A, B, C, hA, hq, hprim⟩ := exists_primitive_quadratic_relation τ hτ
  have hA' : (A : K) ≠ 0 := Int.cast_ne_zero.mpr hA
  have ha : (a : K) ≠ 0 := a.ne_zero
  -- membership in a scaled pair lattice
  have hpair : ∀ c t y : K, c ≠ 0 → (y ∈ Submodule.span ℤ ({c, c * t} : Set K) ↔
      c⁻¹ * y ∈ Submodule.span ℤ ({1, t} : Set K)) := by
    intro c t y hc
    simp only [Submodule.mem_span_pair, zsmul_eq_mul]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp⟩
    · rintro ⟨m, n, h⟩
      exact ⟨m, n, by rw [← mul_inv_cancel_left₀ hc y, ← h]; ring⟩
  have hIsp : (I : Submodule O K).restrictScalars ℤ =
      Submodule.span ℤ ({(a : K), a * τ} : Set K) := by
    rw [hIspan, Submodule.smul_span, Set.smul_set_insert, Set.smul_set_singleton, smul_eq_mul,
      smul_eq_mul, mul_one]
  have hmemI : ∀ y : K, y ∈ I ↔ (a : K)⁻¹ * y ∈ Submodule.span ℤ ({1, τ} : Set K) := by
    intro y
    rw [← hpair _ _ _ ha, ← hIsp]
    rfl
  -- properness identifies the order with the multiplier ring `[1, Aτ]`
  have hO_eq : ∀ x : K, x ∈ O ↔ x ∈ Submodule.span ℤ ({1, (A : K) * τ} : Set K) := by
    intro x
    rw [← IsProper.multiplier_iff O hI x, ← normalized_multiplier_iff τ hτ A B C hA hq hprim x]
    constructor
    · intro h z hz
      have h1 := h (a * z) ((hmemI _).mpr (by rwa [inv_mul_cancel_left₀ ha]))
      rw [hmemI] at h1
      convert h1 using 1
      field_simp
    · intro h y hy
      rw [hmemI] at hy ⊢
      convert h _ hy using 1
      ring
  -- the conjugate root
  set τ' : K := -(B : K) / A - τ with hτ'
  have hq' : (A : K) * τ' ^ 2 + B * τ' + C = 0 := by
    rw [hτ']
    field_simp
    linear_combination (A : K) * hq
  have hτ'lin : LinearIndependent ℚ ![1, τ'] := by
    rw [LinearIndependent.pair_iff] at hτ ⊢
    intro s t hst
    have h := hτ (s - t * (B / A)) (-t) (by
      rw [hτ'] at hst
      simp only [Rat.smul_def, mul_one] at hst ⊢
      push_cast
      linear_combination hst)
    have ht : t = 0 := neg_eq_zero.mp h.2
    refine ⟨?_, ht⟩
    simpa [ht] using h.1
  have hstable : ∀ x ∈ O, ∀ z ∈ Submodule.span ℤ ({1, τ'} : Set K),
      x * z ∈ Submodule.span ℤ ({1, τ'} : Set K) := by
    intro x hx
    refine (normalized_multiplier_iff τ' hτ'lin A B C hA hq' hprim x).mpr ?_
    obtain ⟨m, n, hmn⟩ := Submodule.mem_span_pair.mp ((hO_eq x).mp hx)
    refine Submodule.mem_span_pair.mpr ⟨m - n * B, -n, ?_⟩
    rw [← hmn, hτ']
    simp only [zsmul_eq_mul, mul_one]
    push_cast
    field_simp
    ring
  -- the inverse lattice `β [1, τ']`, with `β = A / a`
  set β : K := (a : K)⁻¹ * A with hβdef
  have hβ : β ≠ 0 := mul_ne_zero (inv_ne_zero ha) hA'
  let Jsub : Submodule O K :=
    { carrier := {y | β⁻¹ * y ∈ Submodule.span ℤ ({1, τ'} : Set K)}
      add_mem' := fun {y z} hy hz => by
        simp only [Set.mem_setOf_eq, mul_add] at hy hz ⊢
        exact Submodule.add_mem _ hy hz
      zero_mem' := by simp
      smul_mem' := fun c y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        change β⁻¹ * ((c : K) * y) ∈ _
        convert hstable (c : K) c.2 _ hy using 1
        ring }
  have hJsp : Jsub.restrictScalars ℤ = Submodule.span ℤ ({β, β * τ'} : Set K) := by
    ext y
    rw [hpair _ _ _ hβ]
    rfl
  have hfrac : IsFractional O⁰ Jsub := by
    refine FractionalIdeal.isFractional_of_le (J := ⟨Submodule.span O ({β, β * τ'} : Set K),
      FractionalIdeal.isFractional_of_fg (Submodule.fg_span (by simp))⟩) ?_
    intro y hy
    have hy' : y ∈ Submodule.span ℤ ({β, β * τ'} : Set K) := by
      rw [← hJsp]
      exact hy
    exact Submodule.span_le_restrictScalars ℤ O _ hy'
  have hone : (1 : Submodule O K).restrictScalars ℤ =
      Submodule.span ℤ ({1, (A : K) * τ} : Set K) := by
    ext x
    rw [Submodule.restrictScalars_mem, Submodule.mem_one, ← hO_eq]
    constructor
    · rintro ⟨y, rfl⟩
      simp [Subalgebra.algebraMap_eq]
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have p1 : (a : K) * β = A := by rw [hβdef]; field_simp
  have p2 : (a : K) * (β * τ') = -(B : K) - A * τ := by rw [hβdef, hτ']; field_simp
  have p3 : (a : K) * τ * β = A * τ := by rw [hβdef]; field_simp
  have p4 : (a : K) * τ * (β * τ') = C := by
    rw [hβdef, hτ']
    field_simp
    linear_combination -hq
  let J : FractionalIdeal O⁰ K := ⟨Jsub, hfrac⟩
  refine ⟨J, FractionalIdeal.coeToSubmodule_injective ?_⟩
  refine (FractionalIdeal.coe_mul I J).trans (Eq.trans ?_ FractionalIdeal.coe_one.symm)
  change (I : Submodule O K) * Jsub = (1 : Submodule O K)
  apply Submodule.restrictScalars_injective ℤ O K
  rw [Submodule.restrictScalars_mul]
  change (I : Submodule O K).restrictScalars ℤ * Jsub.restrictScalars ℤ = _
  rw [hIsp, hJsp, Submodule.span_mul_span, hone, ← primitive_normalized_span τ A B C hprim]
  have mem : ∀ s ∈ ({(a : K), a * τ} : Set K), ∀ u ∈ ({β, β * τ'} : Set K),
      s * u ∈ Submodule.span ℤ (({(a : K), a * τ} : Set K) * {β, β * τ'}) :=
    fun s hs u hu => Submodule.subset_span (Set.mul_mem_mul hs hu)
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    obtain ⟨s, hs, u, hu, rfl⟩ := Set.mem_mul.mp hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hu
    rw [SetLike.mem_coe]
    rcases hs with hs | hs <;> rcases hu with hu | hu <;> subst s <;> subst u
    · rw [p1]
      exact Submodule.subset_span (by simp)
    · rw [p2]
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
    · rw [p3]
      exact Submodule.subset_span (by simp)
    · rw [p4]
      exact Submodule.subset_span (by simp)
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · have h := mem (a : K) (by simp) β (by simp)
      rwa [p1] at h
    · have h := mem ((a : K) * τ) (by simp) β (by simp)
      rwa [p3] at h
    · have h := Submodule.add_mem _ (mem (a : K) (by simp) (β * τ') (by simp))
        (mem ((a : K) * τ) (by simp) β (by simp))
      rwa [p2, p3, sub_add_cancel] at h
    · have h := mem ((a : K) * τ) (by simp) (β * τ') (by simp)
      rwa [p4] at h

/-- Cox, Proposition 7.4, pp. 135–136, properness implies invertibility. -/
theorem isUnit_of_isProper [Algebra.IsQuadraticExtension ℚ K] {I : FractionalIdeal O⁰ K}
    (hI : IsProper O I) : IsUnit I := by
  obtain ⟨J, hJ⟩ := exists_inverse_of_isProper O I hI
  exact IsUnit.of_mul_eq_one J hJ

/-- Cox, Proposition 7.4, pp. 135–136. -/
theorem isProper_iff_isUnit [Algebra.IsQuadraticExtension ℚ K] (I : FractionalIdeal O⁰ K) :
    IsProper O I ↔ IsUnit I :=
  ⟨isUnit_of_isProper O, isProper_of_isUnit O⟩

/-- The complex lattice underlying a fractional ideal; Cox, Exercise 10.11(a), p. 217. -/
def complexLattice (I : FractionalIdeal O⁰ K) : Submodule ℤ ℂ :=
  ((I : Submodule O K).restrictScalars ℤ).map (K.val.toLinearMap.restrictScalars ℤ)

omit hNF hO in
/-- Cox, the embedding of a fractional ideal into the complex plane, Exercise 10.11(a), p. 217. -/
theorem mem_complexLattice (I : FractionalIdeal O⁰ K) (z : ℂ) :
    z ∈ complexLattice O I ↔ ∃ x : K, x ∈ I ∧ (x : ℂ) = z := by
  simp [complexLattice, Submodule.mem_map]

omit hNF hO in
/-- Cox, the quadratic-field description preceding (5.12), p. 103:
a nonreal generator gives an independent rational pair. -/
theorem nonreal_linearIndependent (x : K) (hx : (x : ℂ).im ≠ 0) :
    LinearIndependent ℚ ![1, x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h : (s : ℂ) + (t : ℂ) * (x : ℂ) = 0 := by
    have := congrArg (fun y : K => (y : ℂ)) hst
    simpa [Rat.smul_def] using this
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ratCast_im, Complex.mul_im, Complex.ratCast_re, zero_mul,
    add_zero, zero_add, Complex.zero_im, mul_eq_zero, Rat.cast_eq_zero] at him
  have ht : t = 0 := him.resolve_right hx
  subst ht
  refine ⟨?_, rfl⟩
  simpa using h

omit hNF hO in
include hIQ in
/-- Cox, the description `K = Q(sqrt N)` preceding (5.12), p. 103:
complete the square in a quadratic relation of a nonreal element. -/
theorem exists_negative_square_generator :
    ∃ (D : ℤ) (r : K), D < 0 ∧ r ^ 2 = (D : K) ∧
      LinearIndependent ℚ ![1, r] := by
  haveI := IsImaginaryQuadraticField.isQuadraticExtension K
  obtain ⟨z, hz⟩ := IsImaginaryQuadraticField.exists_nonreal (K := K)
  obtain ⟨A, B, C, hA, hq, -⟩ :=
    exists_primitive_quadratic_relation z (nonreal_linearIndependent z hz)
  have hr : (2 * A * z + B) ^ 2 = ((B ^ 2 - 4 * A * C : ℤ) : K) := by
    push_cast
    linear_combination (4 * (A : K)) * hq
  set w : ℂ := ((2 * A * z + B : K) : ℂ) with hw
  have hwe : w = 2 * (A : ℂ) * (z : ℂ) + (B : ℂ) := by
    rw [hw]
    push_cast
    rfl
  have him : w.im ≠ 0 := by
    have hA' : (A : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hA
    rw [hwe]
    simpa [hA'] using hz
  refine ⟨B ^ 2 - 4 * A * C, 2 * A * z + B, ?_, hr, nonreal_linearIndependent _ him⟩
  have hwsq : w ^ 2 = ((B ^ 2 - 4 * A * C : ℤ) : ℂ) := by
    have h := congrArg (fun y : K => (y : ℂ)) hr
    simp only [IntermediateField.coe_pow] at h
    rw [hw, h]
    push_cast
    rfl
  have hre : w.re ^ 2 - w.im ^ 2 = ((B ^ 2 - 4 * A * C : ℤ) : ℝ) := by
    have h := congrArg Complex.re hwsq
    rw [sq, Complex.mul_re, Complex.intCast_re] at h
    rw [← h]
    ring
  have him2 : 2 * w.re * w.im = 0 := by
    have h := congrArg Complex.im hwsq
    rw [sq, Complex.mul_im, Complex.intCast_im] at h
    linarith
  have hwre : w.re = 0 := by
    rcases mul_eq_zero.mp him2 with h | h
    · linarith
    · exact absurd h him
  have hD : ((B ^ 2 - 4 * A * C : ℤ) : ℝ) < 0 := by
    rw [← hre, hwre]
    nlinarith [sq_pos_of_ne_zero him]
  exact_mod_cast hD

omit hNF hO in
/-- Cox, the squarefree radicand description preceding (5.12), p. 103, remove an integer square. -/
theorem exists_negative_squarefree_factor (D : ℤ) (hD : D < 0) :
    ∃ N b : ℤ, N < 0 ∧ Squarefree N ∧ 0 < b ∧ D = N * b ^ 2 := by
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree D.natAbs
  have hD0 : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD.ne
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hD0 (by simpa using hab.symm)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hD0 (by simpa using hab.symm)
  refine ⟨-(a : ℤ), b, by have := Nat.pos_of_ne_zero ha0; omega, ?_, by
    have := Nat.pos_of_ne_zero hb0; omega, ?_⟩
  · rw [← Int.squarefree_natAbs]
    simpa using ha
  · have h1 : |D| = -D := abs_of_neg hD
    have h2 : ((b ^ 2 * a : ℕ) : ℤ) = (D.natAbs : ℤ) := by rw [hab]
    push_cast at h2
    linear_combination h2 + h1

omit hNF hO in
include hIQ in
/-- Cox, the squarefree radicand description preceding (5.12), p. 103. -/
theorem exists_squarefree_generator :
    ∃ (N : ℤ) (r : K), N < 0 ∧ Squarefree N ∧ r ^ 2 = (N : K) ∧
      LinearIndependent ℚ ![1, r] ∧ (r : ℂ) = Complex.sqrt (N : ℂ) := by
  obtain ⟨D, r0, hD, hr0, hlin0⟩ := exists_negative_square_generator (K := K)
  obtain ⟨N, b, hN, hsq, hb, rfl⟩ := exists_negative_squarefree_factor D hD
  have hb' : (b : K) ≠ 0 := Int.cast_ne_zero.mpr hb.ne'
  have hr1sq : (r0 / b) ^ 2 = (N : K) := by
    rw [div_pow, hr0]
    push_cast
    field_simp
  have hlin1 : LinearIndependent ℚ ![1, r0 / b] := by
    rw [LinearIndependent.pair_iff] at hlin0 ⊢
    intro s t hst
    have h := hlin0 s (t / b) (by
      simp only [Rat.smul_def, mul_one] at hst ⊢
      push_cast
      rw [← hst]
      field_simp)
    refine ⟨h.1, ?_⟩
    have hb'' : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb.ne'
    simpa [hb''] using h.2
  have hsqrt : (Complex.sqrt (N : ℂ)) ^ 2 = (N : ℂ) := Complex.cpow_ofNat_inv_pow _ 2
  have hr1C : (((r0 / b : K)) : ℂ) ^ 2 = (N : ℂ) := by
    have h := congrArg (fun y : K => (y : ℂ)) hr1sq
    simpa using h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hr1C.trans hsqrt.symm) with h | h
  · exact ⟨N, r0 / b, hN, hsq, hr1sq, hlin1, h⟩
  · refine ⟨N, -(r0 / b), hN, hsq, by rw [neg_sq, hr1sq], ?_, ?_⟩
    · rw [LinearIndependent.pair_iff] at hlin1 ⊢
      intro s t hst
      have h' := hlin1 s (-t) (by rw [neg_smul, ← smul_neg]; exact hst)
      exact ⟨h'.1, neg_eq_zero.mp h'.2⟩
    · rw [IntermediateField.coe_neg, h, neg_neg]

omit hNF hO in
include hIQ in
/-- Cox, the imaginary quadratic field description, p. 103: its real elements are rational. -/
theorem real_mem_iff_rat (x : K) :
    (x : ℂ).im = 0 ↔ ∃ q : ℚ, x = (q : K) := by
  constructor
  · intro hx
    obtain ⟨D, r, hD, hr, hlin⟩ := exists_negative_square_generator (K := K)
    have hcard : Fintype.card (Fin 2) = Module.finrank ℚ K := by
      rw [IsImaginaryQuadraticField.finrank_eq_two]; rfl
    let bs := basisOfLinearIndependentOfCardEqFinrank hlin hcard
    have hsum := bs.sum_repr x
    rw [Fin.sum_univ_two] at hsum
    simp only [bs, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
      Matrix.cons_val_one, Rat.smul_def, mul_one] at hsum
    have hrim : (r : ℂ).im ≠ 0 := by
      intro h0
      have h := congrArg (fun y : K => (y : ℂ)) hr
      simp only [IntermediateField.coe_pow] at h
      have hre := congrArg Complex.re h
      rw [sq, Complex.mul_re, h0] at hre
      have hD' : ((D : K) : ℂ).re = D := by simp
      rw [hD'] at hre
      have hDr : (D : ℝ) < 0 := by exact_mod_cast hD
      nlinarith [mul_self_nonneg (r : ℂ).re]
    refine ⟨bs.repr x 0, ?_⟩
    have him := congrArg (fun y : K => (y : ℂ).im) hsum
    simp only [IntermediateField.coe_add, IntermediateField.coe_mul, Complex.add_im,
      Complex.mul_im, hx] at him
    have h1 : ((((bs.repr x 1 : ℚ) : K) : ℂ)) = ((bs.repr x 1 : ℚ) : ℂ) := by simp
    have h0 : ((((bs.repr x 0 : ℚ) : K) : ℂ)) = ((bs.repr x 0 : ℚ) : ℂ) := by simp
    rw [h1, h0] at him
    simp only [Complex.ratCast_im, Complex.ratCast_re, zero_mul, zero_add, add_zero] at him
    have hb1 : bs.repr x 1 = 0 := by
      have := mul_eq_zero.mp him
      rcases this with h | h
      · exact_mod_cast h
      · exact absurd h hrim
    have hsum' : ((bs.repr x 0 : ℚ) : K) + ((bs.repr x 1 : ℚ) : K) * r = x := hsum
    rw [hb1] at hsum'
    simpa using hsum'.symm
  · rintro ⟨q, rfl⟩
    simp

omit hNF hO in
/-- Cox, Exercise 10.11(a), p. 217: an ideal basis gives real-independent periods. -/
theorem basis_complex_linearIndependent [IsImaginaryQuadraticField K]
    (I : FractionalIdeal O⁰ K) (b : Module.Basis (Fin 2) ℤ (I : Submodule O K)) :
    LinearIndependent ℝ (fun i ↦ ((b i : K) : ℂ)) := by
  let f : (I : Submodule O K) →ₗ[ℤ] K :=
    { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hZ : LinearIndependent ℤ ![(b 0 : K), (b 1 : K)] := by
    have h := b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr fun _ _ h => Subtype.ext h)
    convert h using 1
    ext i; fin_cases i <;> rfl
  have hQ := LinearIndependent.pair_iff.mp ((LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ)
  have hu : ((b 0 : K) : ℂ) ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext (Subtype.ext h))
  have hfun : (fun i ↦ ((b i : K) : ℂ)) = ![((b 0 : K) : ℂ), ((b 1 : K) : ℂ)] := by
    ext i; fin_cases i <;> rfl
  rw [hfun, LinearIndependent.pair_iff]
  intro s t hst
  simp only [Complex.real_smul] at hst
  by_cases ht : t = 0
  · subst ht
    simp only [Complex.ofReal_zero, zero_mul, add_zero, mul_eq_zero, Complex.ofReal_eq_zero] at hst
    exact ⟨hst.resolve_right hu, rfl⟩
  · exfalso
    have hw : (((b 1 : K) / (b 0 : K) : K) : ℂ).im = 0 := by
      have hv : ((b 1 : K) : ℂ) = -((s : ℂ) / t) * ((b 0 : K) : ℂ) := by
        have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        field_simp
        linear_combination hst
      rw [IntermediateField.coe_div, hv, mul_div_assoc, div_self hu, mul_one]
      simp [← Complex.ofReal_div]
    obtain ⟨q, hq⟩ := (real_mem_iff_rat _).mp hw
    have hu' : (b 0 : K) ≠ 0 := fun h => hu (by rw [h]; rfl)
    have h := hQ q (-1) (by
      rw [div_eq_iff hu'] at hq
      simp only [Rat.smul_def, neg_one_smul, hq]
      ring)
    exact one_ne_zero (neg_eq_zero.mp h.2)

/-- Cox, Exercise 10.11(a), p. 217, applied to a nonzero ideal lattice. -/
theorem exists_periodPair [IsImaginaryQuadraticField K]
    (I : FractionalIdeal O⁰ K) (hI : I ≠ 0) :
    ∃ L : PeriodPair, L.lattice = complexLattice O I := by
  let b : Module.Basis (Fin 2) ℤ (I : Submodule O K) :=
    Module.finBasisOfFinrankEq ℤ _ (fractionalIdeal_finrank O I hI)
  have hind := basis_complex_linearIndependent O I b
  have hfun : (fun i ↦ ((b i : K) : ℂ)) = ![((b 0 : K) : ℂ), ((b 1 : K) : ℂ)] := by
    ext i; fin_cases i <;> rfl
  rw [hfun] at hind
  refine ⟨⟨_, _, hind⟩, ?_⟩
  have hspan : (I : Submodule O K).restrictScalars ℤ =
      Submodule.span ℤ ({(b 0 : K), (b 1 : K)} : Set K) := by
    apply le_antisymm
    · intro x hx
      have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      simp only [Fin.sum_univ_two, Submodule.coe_add] at h
      rw [← h]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [Submodule.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact (b 0).2
      · exact (b 1).2
  rw [PeriodPair.lattice, complexLattice, hspan, Submodule.map_span, Set.image_pair]
  rfl

omit hNF hO in
/-- Cox, Exercise 5.7(a), p. 117, the trace in square-root coordinates. -/
theorem quadratic_trace [Algebra.IsQuadraticExtension ℚ K] (N : ℤ) (r : K) (hr : r ^ 2 = (N : K))
    (hlin : LinearIndependent ℚ ![1, r]) (a b : ℚ) :
    Algebra.trace ℚ K ((a : K) + b * r) = 2 * a := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ K := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]; rfl
  let bs := basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hb0 : bs 0 = 1 := by simp [bs]
  have hb1 : bs 1 = r := by simp [bs]
  have hrepr : ∀ c d : ℚ, bs.repr ((c : K) + d * r) = Finsupp.single 0 c + Finsupp.single 1 d := by
    intro c d
    have h : (c : K) + d * r = c • bs 0 + d • bs 1 := by rw [hb0, hb1]; simp [Rat.smul_def]
    rw [h, map_add, map_smul, map_smul, bs.repr_self, bs.repr_self]
    simp
  have e2 : ((a : K) + b * r) * r = ((b * N : ℚ) : K) + a * r := by
    push_cast
    linear_combination (b : K) * hr
  have e1 : ((a : K) + b * r) * 1 = (a : K) + b * r := mul_one _
  rw [Algebra.trace_eq_matrix_trace bs, Matrix.trace_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, e1, e2, hrepr]
  simp
  ring

omit hNF hO in
/-- Cox, Exercise 5.7(a), p. 117, the norm in square-root coordinates. -/
theorem quadratic_norm [Algebra.IsQuadraticExtension ℚ K] (N : ℤ) (r : K) (hr : r ^ 2 = (N : K))
    (hlin : LinearIndependent ℚ ![1, r]) (a b : ℚ) :
    Algebra.norm ℚ ((a : K) + b * r) = a ^ 2 - N * b ^ 2 := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ K := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]; rfl
  let bs := basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hb0 : bs 0 = 1 := by simp [bs]
  have hb1 : bs 1 = r := by simp [bs]
  have hrepr : ∀ c d : ℚ, bs.repr ((c : K) + d * r) = Finsupp.single 0 c + Finsupp.single 1 d := by
    intro c d
    have h : (c : K) + d * r = c • bs 0 + d • bs 1 := by rw [hb0, hb1]; simp [Rat.smul_def]
    rw [h, map_add, map_smul, map_smul, bs.repr_self, bs.repr_self]
    simp
  have e2 : ((a : K) + b * r) * r = ((b * N : ℚ) : K) + a * r := by
    push_cast
    linear_combination (b : K) * hr
  have e1 : ((a : K) + b * r) * 1 = (a : K) + b * r := mul_one _
  rw [Algebra.norm_eq_matrix_det bs, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, e1, e2, hrepr]
  simp
  ring

omit hNF hO in
include hIQ in
/-- Cox, Exercise 5.7(b), p. 117, the monic equation formed from trace and norm. -/
theorem quadratic_characteristic_relation (x : K) :
    x ^ 2 - (Algebra.trace ℚ K x : K) * x + (Algebra.norm ℚ x : K) = 0 := by
  obtain ⟨D, r, -, hr, hlin⟩ := exists_negative_square_generator (K := K)
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ K := by
    rw [IsImaginaryQuadraticField.finrank_eq_two]; rfl
  let bs := basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hsum := bs.sum_repr x
  rw [Fin.sum_univ_two] at hsum
  simp only [bs, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one, Rat.smul_def, mul_one] at hsum
  rw [← hsum, quadratic_trace D r hr hlin, quadratic_norm D r hr hlin]
  push_cast
  linear_combination ((bs.repr x 1 : ℚ) : K) ^ 2 * hr

omit hO in
include hIQ in
/-- Cox, Exercise 5.7(b), p. 117: integral trace and norm characterize quadratic integers. -/
theorem isIntegral_iff_trace_norm_int (x : K) :
    IsIntegral ℤ x ↔
      (∃ t : ℤ, Algebra.trace ℚ K x = (t : ℚ)) ∧
      (∃ n : ℤ, Algebra.norm ℚ x = (n : ℚ)) := by
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (L := ℚ) hx)
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm ℚ hx)
    exact ⟨⟨t, by rw [← ht]; simp⟩, ⟨n, by rw [← hn]; simp⟩⟩
  · rintro ⟨⟨t, ht⟩, ⟨n, hn⟩⟩
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, by monicity!, ?_⟩
    have h := quadratic_characteristic_relation x
    rw [ht, hn] at h
    rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow, eq_intCast, eq_intCast]
    simpa using h

omit hNF hO in
/-- Cox, Exercise 5.7(c), p. 117, denominator divisibility before applying squarefreeness. -/
theorem rat_den_sq_dvd_of_sq_mul_int (N : ℤ) (q : ℚ)
    (hq : ∃ m : ℤ, q ^ 2 * N = (m : ℚ)) : (q.den : ℤ) ^ 2 ∣ N := by
  obtain ⟨m, hm⟩ := hq
  have h1 : (q.num : ℚ) ^ 2 * N = m * (q.den : ℚ) ^ 2 := by
    rw [← Rat.mul_den_eq_num]
    linear_combination (q.den : ℚ) ^ 2 * hm
  have h2 : q.num ^ 2 * N = m * (q.den : ℤ) ^ 2 := by exact_mod_cast h1
  have hcop : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    refine IsCoprime.pow ?_
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.coprime_comm] using q.reduced
  exact hcop.dvd_of_dvd_mul_right ⟨m, by linear_combination h2⟩

omit hNF hO in
/-- Cox, Exercise 5.7(c), p. 117, squarefreeness forces a unit rational denominator. -/
theorem rat_den_eq_one_of_squarefree (N : ℤ) (hN : Squarefree N) (q : ℚ)
    (hq : (q.den : ℤ) ^ 2 ∣ N) : q.den = 1 := by
  have h := hN (q.den : ℤ) (by rwa [← sq])
  rw [Int.isUnit_iff_natAbs_eq] at h
  simpa using h

omit hNF hO in
/-- Cox, Exercise 5.7(c), p. 117: squarefreeness clears the remaining denominator. -/
theorem rat_int_of_sq_mul_squarefree_int (N : ℤ) (hN : Squarefree N) (q : ℚ)
    (hq : ∃ m : ℤ, q ^ 2 * N = (m : ℚ)) : ∃ n : ℤ, q = (n : ℚ) :=
  ⟨q.num, (Rat.coe_int_num_of_den_eq_one
    (rat_den_eq_one_of_squarefree N hN q (rat_den_sq_dvd_of_sq_mul_int N q hq))).symm⟩

omit hO in
include hIQ in
/-- Cox, Exercise 5.7(c), p. 117: an integer is `(u + v sqrt N)/2` with a parity constraint. -/
theorem integral_half_coordinates (N : ℤ) (hN : Squarefree N) (r : K)
    (hr : r ^ 2 = (N : K)) (hlin : LinearIndependent ℚ ![1, r])
    (x : K) (hx : IsIntegral ℤ x) :
    ∃ u v : ℤ, x = ((u : K) + v * r) / 2 ∧ 4 ∣ u ^ 2 - N * v ^ 2 := by
  obtain ⟨⟨t, ht⟩, ⟨n, hn⟩⟩ := (isIntegral_iff_trace_norm_int x).mp hx
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ K := by
    rw [IsImaginaryQuadraticField.finrank_eq_two]; rfl
  let bs := basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hsum := bs.sum_repr x
  rw [Fin.sum_univ_two] at hsum
  simp only [bs, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one, Rat.smul_def, mul_one] at hsum
  have hsum' : ((bs.repr x 0 : ℚ) : K) + ((bs.repr x 1 : ℚ) : K) * r = x := hsum
  set a := bs.repr x 0
  set b := bs.repr x 1
  rw [← hsum', quadratic_trace N r hr hlin] at ht
  rw [← hsum', quadratic_norm N r hr hlin] at hn
  obtain ⟨v, hv⟩ := rat_int_of_sq_mul_squarefree_int N hN (2 * b)
    ⟨t ^ 2 - 4 * n, by push_cast; rw [← ht, ← hn]; ring⟩
  refine ⟨t, v, ?_, ⟨n, ?_⟩⟩
  · have htK : (t : K) = 2 * (a : K) := by
      have h := congrArg (fun q : ℚ => (q : K)) ht
      push_cast at h
      rw [← h]
    have hvK : (v : K) = 2 * (b : K) := by
      have h := congrArg (fun q : ℚ => (q : K)) hv
      push_cast at h
      rw [← h]
    rw [← hsum', htK, hvK]
    ring
  · have h : ((t ^ 2 - N * v ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
      push_cast
      rw [← ht, ← hn, ← hv]
      ring
    exact_mod_cast h

omit hNF hO in
/-- Cox, Exercise 5.7(c), p. 117: reduce the integrality constraint modulo four. -/
theorem half_coordinates_parity (N u v : ℤ) (hN : Squarefree N)
    (h : 4 ∣ u ^ 2 - N * v ^ 2) :
    if N % 4 = 1 then Even (u - v) else Even u ∧ Even v := by
  have hN4 : N % 4 ≠ 0 := by
    intro h0
    have h2 := hN 2 (by norm_num; exact Int.dvd_of_emod_eq_zero h0)
    rcases Int.isUnit_iff.mp h2 with h | h <;> norm_num at h
  have hdecomp := Int.emod_add_mul_ediv N 4
  have hs0 := Int.emod_nonneg N (by norm_num : (4 : ℤ) ≠ 0)
  have hs4 := Int.emod_lt_of_pos N (by norm_num : (0 : ℤ) < 4)
  generalize N % 4 = s at *
  generalize N / 4 = m at *
  subst hdecomp
  split_ifs with hs1
  · subst hs1
    rw [Int.even_iff]
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' u <;> obtain ⟨l, rfl | rfl⟩ := Int.even_or_odd' v <;>
      ring_nf at h ⊢ <;> omega
  · rw [Int.even_iff, Int.even_iff]
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' u <;> obtain ⟨l, rfl | rfl⟩ := Int.even_or_odd' v <;>
      interval_cases s <;> ring_nf at h ⊢ <;> omega

omit hO in
include hIQ in
/-- Cox, equation (5.13), p. 103, proved in Exercise 5.7(c), p. 117. -/
theorem isIntegral_iff_squarefree_coordinates (N : ℤ) (hN : Squarefree N)
    (r : K) (hr : r ^ 2 = (N : K)) (hlin : LinearIndependent ℚ ![1, r]) (x : K) :
    IsIntegral ℤ x ↔ ∃ a b : ℤ,
      x = (a : K) + b * (if N % 4 = 1 then (1 + r) / 2 else r) := by
  constructor
  · intro hx
    obtain ⟨u, v, rfl, h4⟩ := integral_half_coordinates N hN r hr hlin x hx
    have hpar := half_coordinates_parity N u v hN h4
    split_ifs at hpar ⊢ with h1
    · obtain ⟨c, hc⟩ := hpar
      refine ⟨c, v, ?_⟩
      have hu : (u : K) = 2 * c + v := by
        have h := congrArg (fun z : ℤ => (z : K)) hc
        push_cast at h
        linear_combination h
      rw [hu]
      ring
    · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hpar
      refine ⟨a, b, ?_⟩
      subst ha hb
      push_cast
      ring
  · rintro ⟨a, b, rfl⟩
    have hω : IsIntegral ℤ (if N % 4 = 1 then (1 + r) / 2 else r) := by
      split_ifs with h1
      · obtain ⟨c, hc⟩ : ∃ c : ℤ, N = 4 * c + 1 := ⟨N / 4, by omega⟩
        refine ⟨Polynomial.X ^ 2 - Polynomial.X - Polynomial.C c, by monicity!, ?_⟩
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_X,
          Polynomial.eval₂_X_pow, eq_intCast]
        rw [hc] at hr
        push_cast at hr
        linear_combination (1 / 4 : K) * hr
      · refine ⟨Polynomial.X ^ 2 - Polynomial.C N, by monicity!, ?_⟩
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, eq_intCast, hr,
          sub_self]
    have hint : ∀ z : ℤ, IsIntegral ℤ (z : K) := fun z => by
      simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := z)
    exact (hint a).add ((hint b).mul hω)

omit hO in
include hIQ in
/-- Cox, equation (5.13), p. 103: the displayed generators are an integral basis. -/
theorem exists_integralBasis_of_squarefree (N : ℤ) (hN : Squarefree N)
    (r : K) (hr : r ^ 2 = (N : K)) (hlin : LinearIndependent ℚ ![1, r]) :
    ∃ b : Module.Basis (Fin 2) ℤ (𝓞 K),
      (b 0 : K) = 1 ∧ (b 1 : K) = if N % 4 = 1 then (1 + r) / 2 else r := by
  set ω : K := if N % 4 = 1 then (1 + r) / 2 else r with hωdef
  have hωint : IsIntegral ℤ ω :=
    (isIntegral_iff_squarefree_coordinates N hN r hr hlin ω).mpr ⟨0, 1, by simp [hωdef]⟩
  let ω' : 𝓞 K := ⟨ω, hωint⟩
  have hQ : LinearIndependent ℚ ![(1 : K), ω] := by
    rw [LinearIndependent.pair_iff] at hlin ⊢
    intro s t hst
    rw [hωdef] at hst
    split_ifs at hst
    · have h := hlin (s + t / 2) (t / 2) (by
        simp only [Rat.smul_def, mul_one] at hst ⊢
        push_cast
        linear_combination hst)
      constructor <;> linarith [h.1, h.2]
    · exact hlin s t hst
  let f : 𝓞 K →ₗ[ℤ] K :=
    { toFun := fun y => (y : K), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hZ : LinearIndependent ℤ ![(1 : 𝓞 K), ω'] := by
    refine LinearIndependent.of_comp f ?_
    have h : f ∘ ![(1 : 𝓞 K), ω'] = ![(1 : K), ω] := by
      ext i; fin_cases i <;> rfl
    rw [h]
    exact LinearIndependent.restrict_scalars' (R := ℤ) hQ
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), ω']) := by
    rintro y -
    obtain ⟨a, b, hab⟩ := (isIntegral_iff_squarefree_coordinates N hN r hr hlin y).mp
      (NumberField.RingOfIntegers.isIntegral_coe y)
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
    refine Submodule.mem_span_pair.mpr ⟨a, b, NumberField.RingOfIntegers.ext ?_⟩
    have e : ((a • (1 : 𝓞 K) + b • ω' : 𝓞 K) : K) = (a : K) + b * ω := by
      simp only [map_add, zsmul_eq_mul, mul_one]
      rfl
    rw [e, hab, hωdef]
  exact ⟨Module.Basis.mk hZ hsp, by simp, by simp [ω']; rfl⟩

omit hO in
include hIQ in
/-- Cox, equation (5.12), p. 103, compared with the integral trace-basis discriminant. -/
theorem discr_eq_of_squarefree (N : ℤ) (hN : Squarefree N)
    (r : K) (hr : r ^ 2 = (N : K)) (hlin : LinearIndependent ℚ ![1, r]) :
    NumberField.discr K = if N % 4 = 1 then N else 4 * N := by
  obtain ⟨b, hb0, hb1⟩ := exists_integralBasis_of_squarefree N hN r hr hlin
  have hb0' : algebraMap (𝓞 K) K (b 0) = 1 := hb0
  have hb1' : algebraMap (𝓞 K) K (b 1) = if N % 4 = 1 then (1 + r) / 2 else r := hb1
  have htr := quadratic_trace N r hr hlin
  rw [← NumberField.discr_eq_discr K b]
  apply Int.cast_injective (α := ℚ)
  rw [← eq_intCast (algebraMap ℤ ℚ) (Algebra.discr ℤ b),
    ← Algebra.discr_localizationLocalization ℤ ℤ⁰ K b, Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    Module.Basis.localizationLocalization_apply, hb0', hb1']
  split_ifs
  · have e00 : (1 : K) * 1 = ((1 : ℚ) : K) + ((0 : ℚ) : K) * r := by push_cast; ring
    have e01 : (1 : K) * ((1 + r) / 2) = ((1 / 2 : ℚ) : K) + ((1 / 2 : ℚ) : K) * r := by
      push_cast; ring
    have e10 : (1 + r) / 2 * (1 : K) = ((1 / 2 : ℚ) : K) + ((1 / 2 : ℚ) : K) * r := by
      push_cast; ring
    have e11 : (1 + r) / 2 * ((1 + r) / 2) =
        (((1 + N) / 4 : ℚ) : K) + ((1 / 2 : ℚ) : K) * r := by
      push_cast; linear_combination (1 / 4 : K) * hr
    rw [e00, e01, e10, e11]
    simp only [htr]
    ring
  · have e00 : (1 : K) * 1 = ((1 : ℚ) : K) + ((0 : ℚ) : K) * r := by push_cast; ring
    have e01 : (1 : K) * r = ((0 : ℚ) : K) + ((1 : ℚ) : K) * r := by push_cast; ring
    have e10 : r * (1 : K) = ((0 : ℚ) : K) + ((1 : ℚ) : K) * r := by push_cast; ring
    have e11 : r * r = ((N : ℚ) : K) + ((0 : ℚ) : K) * r := by
      push_cast; linear_combination hr
    rw [e00, e01, e10, e11]
    simp only [htr]
    push_cast; ring

/-- A choice of period pair for an invertible fractional ideal; Cox, Exercise 10.11(a), p. 217. -/
def periodPair (I : (FractionalIdeal O⁰ K)ˣ) : PeriodPair :=
  (exists_periodPair O (I : FractionalIdeal O⁰ K) I.ne_zero).choose

include hIQ in
/-- Cox, Exercise 10.11(a), p. 217, the lattice of the chosen period pair. -/
theorem periodPair_lattice (I : (FractionalIdeal O⁰ K)ˣ) :
    (periodPair O I).lattice = complexLattice O (I : FractionalIdeal O⁰ K) :=
  (exists_periodPair O (I : FractionalIdeal O⁰ K) I.ne_zero).choose_spec

/-- The ideal class in Mathlib's quotient by principal fractional ideals; Cox, p. 136. -/
def idealClass (I : (FractionalIdeal O⁰ K)ˣ) : ClassGroup O :=
  ClassGroup.mk K I

/-- The lattice invariant of an invertible fractional ideal; Cox, Theorem 11.1, p. 237. -/
def idealJ (I : (FractionalIdeal O⁰ K)ˣ) : ℂ := (periodPair O I).j

include hIQ in
/-- Cox, Theorem 10.9 and Exercise 10.11(a): the ideal invariant is basis independent. -/
theorem idealJ_eq_of_lattice_eq (I : (FractionalIdeal O⁰ K)ˣ) (L : PeriodPair)
    (hL : L.lattice = complexLattice O (I : FractionalIdeal O⁰ K)) :
    idealJ O I = L.j :=
  PeriodPair.j_congr ((periodPair_lattice O I).trans hL.symm)

omit hNF hO in
/-- Cox, Exercise 10.11(a), p. 217: the embedded lattice determines the fractional ideal. -/
theorem complexLattice_injective : Function.Injective (complexLattice O) := by
  intro I J h
  apply FractionalIdeal.coeToSubmodule_injective
  apply Submodule.restrictScalars_injective ℤ
  exact Submodule.map_injective_of_injective
    (f := K.val.toLinearMap.restrictScalars ℤ) Subtype.val_injective h

include hIQ in
/-- Cox, Theorem 10.9, p. 207: scaling the period pair of `I` by a field element gives the
lattice of the product with the corresponding principal ideal. -/
theorem smul_periodPair_lattice (I : (FractionalIdeal O⁰ K)ˣ) (a : Kˣ) (u : ℂˣ)
    (hu : (u : ℂ) = ((a : K) : ℂ)) :
    (u • periodPair O I).lattice =
      complexLattice O ((I * toPrincipalIdeal O K a : (FractionalIdeal O⁰ K)ˣ) :
        FractionalIdeal O⁰ K) := by
  ext z
  rw [PeriodPair.mem_smul_lattice, mem_complexLattice, Units.val_mul, coe_toPrincipalIdeal,
    mul_comm, periodPair_lattice]
  simp only [FractionalIdeal.mem_singleton_mul, mem_complexLattice]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(a : K) * x, ⟨x, hx, rfl⟩, by simp [hu]⟩
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(x : ℂ), ⟨x, hx, rfl⟩, by simp [hu]⟩

include hIQ in
/-- Cox, Theorem 10.9: multiplication by a nonzero field element preserves the invariant. -/
theorem idealJ_mul_principal (I : (FractionalIdeal O⁰ K)ˣ) (a : Kˣ) :
    idealJ O (I * toPrincipalIdeal O K a) = idealJ O I := by
  have ha : ((a : K) : ℂ) ≠ 0 := by simp
  rw [idealJ_eq_of_lattice_eq O _ _
    (smul_periodPair_lattice O I a (Units.mk0 _ ha) rfl), PeriodPair.j_smul]
  rfl

include hIQ in
/-- Cox, Exercise 10.11(a): a homothety between nonzero ideals has scalar in the field. -/
theorem homothety_scalar_mem (I J : (FractionalIdeal O⁰ K)ˣ) (a : ℂˣ)
    (ha : (a • periodPair O I).lattice = (periodPair O J).lattice) :
    (a : ℂ) ∈ K := by
  obtain ⟨x, hx0, hxI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger I.ne_zero
  have hy0 : algebraMap O K x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hx0
  have hmem : (a : ℂ) * ((algebraMap O K x : K) : ℂ) ∈ (periodPair O J).lattice := by
    rw [← ha, PeriodPair.mem_smul_lattice]
    exact ⟨_, by rw [periodPair_lattice, mem_complexLattice]; exact ⟨_, hxI, rfl⟩, rfl⟩
  rw [periodPair_lattice, mem_complexLattice] at hmem
  obtain ⟨z, -, hz⟩ := hmem
  have hyC : ((algebraMap O K x : K) : ℂ) ≠ 0 := by simpa using hy0
  have h : (a : ℂ) = (z : ℂ) / ((algebraMap O K x : K) : ℂ) := by
    rw [hz]; field_simp
  rw [h]
  exact K.div_mem z.2 (algebraMap O K x).2

/-- Cox, Theorem 10.9 and the definition of ideal classes on p. 136. -/
theorem idealClass_eq_iff_exists_principal (I J : (FractionalIdeal O⁰ K)ˣ) :
    idealClass O I = idealClass O J ↔ ∃ a : Kˣ, I * toPrincipalIdeal O K a = J := by
  rw [idealClass, idealClass, ← (ClassGroup.equiv (R := O) K).injective.eq_iff,
    ClassGroup.equiv_mk, ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    QuotientGroup.mk'_eq_mk']
  simp only [MonoidHom.mem_range, exists_exists_eq_and]
  rfl

include hIQ in
/-- Cox, Theorem 10.9 and the ideal-class argument in Theorem 11.1, pp. 238–239. -/
theorem idealJ_eq_iff_idealClass_eq (I J : (FractionalIdeal O⁰ K)ˣ) :
    idealJ O I = idealJ O J ↔ idealClass O I = idealClass O J := by
  rw [idealClass_eq_iff_exists_principal]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := PeriodPair.j_eq_iff_homothetic.mp h
    set k : K := ⟨a, homothety_scalar_mem O I J a ha⟩ with hkdef
    have hk0 : k ≠ 0 := fun hk => a.ne_zero (by simpa [hkdef] using congrArg Subtype.val hk)
    refine ⟨Units.mk0 k hk0, Units.ext (complexLattice_injective O ?_)⟩
    rw [← smul_periodPair_lattice O I (Units.mk0 k hk0) a rfl, ha, periodPair_lattice]
  · rintro ⟨a, rfl⟩
    exact (idealJ_mul_principal O I a).symm

/-- The norm of an integral ideal is its additive index; Cox, p. 134. -/
def idealNorm (a : Ideal O) : ℕ := Nat.card (O ⧸ a)

/-- The absolute determinant norm of an order element; Cox, Lemma 7.14(i), p. 140. -/
def elementNorm (α : O) : ℕ := (Algebra.norm ℤ α).natAbs

/-- Cox, Proposition 7.4: package an integral invertible ideal as a unit fractional ideal. -/
def integralIdealUnit (a : Ideal O) (ha : IsUnit (a : FractionalIdeal O⁰ K)) :
    (FractionalIdeal O⁰ K)ˣ := ha.unit

omit hNF hO in
/-- Cox, Proposition 7.4, the underlying fractional ideal of an integral ideal. -/
theorem coe_integralIdealUnit (a : Ideal O) (ha : IsUnit (a : FractionalIdeal O⁰ K)) :
    (integralIdealUnit O a ha : FractionalIdeal O⁰ K) = a :=
  ha.unit_spec

/-- Cox, p. 134 and Exercise 7.4: a nonzero ideal has positive finite norm. -/
theorem idealNorm_pos (a : Ideal O) (ha : a ≠ ⊥) : 0 < idealNorm O a := by
  obtain ⟨α, hαa, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  let N : Submodule ℤ O := a.restrictScalars ℤ
  let g : O →ₗ[ℤ] N :=
    { toFun := fun x => ⟨α * x, a.mul_mem_right x hαa⟩
      map_add' := fun x y => Subtype.ext (mul_add α x y)
      map_smul' := fun n x => Subtype.ext (mul_smul_comm n α x) }
  have hg : Function.Injective g := fun x y h =>
    mul_left_cancel₀ hα0 (congrArg Subtype.val h)
  have hrank : Module.finrank ℤ N = Module.finrank ℤ O :=
    le_antisymm (Submodule.finrank_le N) (LinearMap.finrank_le_finrank_of_injective hg)
  haveI := Submodule.finiteQuotientOfFreeOfRankEq N hrank
  haveI : Finite (O ⧸ a) :=
    Finite.of_equiv _ (Submodule.Quotient.restrictScalarsEquiv ℤ a).toEquiv
  exact Nat.card_pos

/-- Cox, Lemma 7.14(i), p. 140. -/
theorem idealNorm_span_singleton (α : O) :
    idealNorm O (Ideal.span {α}) = elementNorm O α := by
  classical
  rcases eq_or_ne α 0 with rfl | hα
  · have hinf : Infinite O := Infinite.of_injective (fun n : ℕ => (n : O)) fun m n h => by
      have h' := congrArg (fun y : O => (y : K)) h
      simpa using h'
    rw [idealNorm, elementNorm, Set.singleton_zero, Ideal.span_zero,
      Nat.card_congr (RingEquiv.quotientBot O).toEquiv, Nat.card_eq_zero_of_infinite,
      Algebra.norm_zero, Int.natAbs_zero]
  · let b := Module.Free.chooseBasis ℤ O
    have h := Submodule.natAbs_det_basis_change b ((Ideal.span {α}).restrictScalars ℤ)
      (Ideal.basisSpanSingleton b hα)
    rw [idealNorm, ← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ
      (Ideal.span {α})).toEquiv, ← h, elementNorm]
    have hv : (Subtype.val ∘ Ideal.basisSpanSingleton b hα) = (Algebra.lmul ℤ O α) ∘ b := by
      ext i
      simp [Ideal.basisSpanSingleton_apply]
    have hdet : b.det ((Algebra.lmul ℤ O α) ∘ b) = Algebra.norm ℤ α := by
      rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one, Algebra.norm_apply]
    rw [← hdet, ← hv]
    rfl

omit hNF hO in
include hIQ in
/-- Cox, the quadratic norm calculation used in (7.6) and (7.16), pp. 136 and 140. -/
theorem fieldNorm_eq_mul_conj (x : K) :
    (Algebra.norm ℚ x : ℂ) = (x : ℂ) * star (x : ℂ) := by
  obtain ⟨D, r, hD, hr, hlin⟩ := exists_negative_square_generator (K := K)
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ K := by
    rw [IsImaginaryQuadraticField.finrank_eq_two]; rfl
  let bs := basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hsum := bs.sum_repr x
  rw [Fin.sum_univ_two] at hsum
  simp only [bs, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one, Rat.smul_def, mul_one] at hsum
  have hrC : ((r : K) : ℂ) ^ 2 = (D : ℂ) := by
    simpa using congrArg (fun w : K => (w : ℂ)) hr
  have hre : ((r : K) : ℂ).re = 0 := by
    have h1 := congrArg Complex.re hrC
    have h2 := congrArg Complex.im hrC
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im] at h1 h2
    by_contra hne
    have him : ((r : K) : ℂ).im = 0 :=
      (mul_eq_zero.mp (by linarith : ((r : K) : ℂ).re * ((r : K) : ℂ).im = 0)).resolve_left hne
    rw [him] at h1
    have hDneg : (D : ℝ) < 0 := by exact_mod_cast hD
    nlinarith [mul_self_nonneg ((r : K) : ℂ).re]
  have hconj : star ((r : K) : ℂ) = -((r : K) : ℂ) := by
    apply Complex.ext <;> simp [hre]
  rw [← hsum, quadratic_norm D r hr hlin]
  generalize bs.repr x 0 = a
  generalize bs.repr x 1 = b
  push_cast
  rw [star_add, star_mul', hconj]
  simp only [Complex.star_def, map_ratCast]
  linear_combination (b : ℂ) ^ 2 * hrC

include hIQ in
/-- Cox, Lemma 7.14(i), p. 140, compatibility with the quadratic field norm. -/
theorem elementNorm_eq_fieldNorm (α : O) :
    (elementNorm O α : ℚ) = Algebra.norm ℚ (α : K) := by
  have h := Algebra.norm_localization (R := ℤ) (S := O) (Rₘ := ℚ) (Sₘ := K) ℤ⁰ α
  have hnn : 0 ≤ Algebra.norm ℚ (α : K) := by
    have h2 := fieldNorm_eq_mul_conj (α : K)
    rw [Complex.star_def, Complex.mul_conj] at h2
    have h3 : ((Algebra.norm ℚ (α : K) : ℚ) : ℝ) = Complex.normSq ((α : K) : ℂ) := by
      exact_mod_cast h2
    have h4 : (0 : ℝ) ≤ ((Algebra.norm ℚ (α : K) : ℚ) : ℝ) := h3 ▸ Complex.normSq_nonneg _
    exact_mod_cast h4
  rw [elementNorm, Nat.cast_natAbs, Int.cast_abs, ← eq_intCast (algebraMap ℤ ℚ), ← h]
  exact abs_of_nonneg hnn

/-- Cox, equation (7.15), p. 140. -/
theorem idealNorm_principal_mul (α : O) (a : Ideal O) (hα : α ≠ 0) :
    idealNorm O (Ideal.span {α} * a) = elementNorm O α * idealNorm O a := by
  let Kα := (Ideal.span {α}).toAddSubgroup
  let H := (Ideal.span {α} * a).toAddSubgroup
  have hle : H ≤ Kα := Ideal.mul_le_left
  let φ : O →+ Kα :=
    { toFun := fun x => ⟨α * x, Ideal.mem_span_singleton'.mpr ⟨x, mul_comm x α⟩⟩
      map_zero' := Subtype.ext (mul_zero α)
      map_add' := fun x y => Subtype.ext (mul_add α x y) }
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    exact ⟨x, Subtype.ext (mul_comm α x)⟩
  have hcomap : (H.addSubgroupOf Kα).comap φ = a.toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf,
      Submodule.mem_toAddSubgroup]
    change α * x ∈ Ideal.span {α} * a ↔ x ∈ a
    rw [Ideal.mem_span_singleton_mul]
    constructor
    · rintro ⟨z, hz, hzx⟩
      rwa [mul_left_cancel₀ hα hzx] at hz
    · exact fun hx => ⟨x, hx, rfl⟩
  have hrel : H.relIndex Kα = idealNorm O a := by
    rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφ, hcomap,
      AddSubgroup.index_eq_card]
    rfl
  have hK : Kα.index = elementNorm O α := by
    rw [← idealNorm_span_singleton O α, AddSubgroup.index_eq_card]
    rfl
  have hH : idealNorm O (Ideal.span {α} * a) = H.index := by
    rw [AddSubgroup.index_eq_card]
    rfl
  rw [hH, ← AddSubgroup.relIndex_mul_index hle, hrel, hK, mul_comm]

/-- Inclusion of an order in the ring of integers; Cox, Exercise 7.2, p. 133. -/
def toRingOfIntegers : O →+* 𝓞 K where
  toFun x := ⟨(x : K), isIntegral_of_mem O x.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The conductor is the additive index in the maximal order; Cox, Lemma 7.2, pp. 133–134. -/
def conductor : ℕ := (toRingOfIntegers O).toAddMonoidHom.range.index

omit hNF in
/-- Cox, Exercise 7.2, the canonical inclusion of an order. -/
theorem toRingOfIntegers_injective : Function.Injective (toRingOfIntegers O) := by
  intro x y h
  exact Subtype.ext (congrArg NumberField.RingOfIntegers.val h)

/-- Cox, Lemma 7.2, p. 133: the conductor is positive. -/
theorem conductor_pos : 0 < conductor O := by
  let f : O →ₗ[ℤ] 𝓞 K := (toRingOfIntegers O).toAddMonoidHom.toIntLinearMap
  have hrank : Module.finrank ℤ (LinearMap.range f) = Module.finrank ℤ (𝓞 K) := by
    rw [LinearMap.finrank_range_of_inj (toRingOfIntegers_injective O), finrank_eq_degree O,
      NumberField.RingOfIntegers.rank]
  have h : Finite (𝓞 K ⧸ (LinearMap.range f).toAddSubgroup) :=
    Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range f) hrank
  have e : (LinearMap.range f).toAddSubgroup = (toRingOfIntegers O).toAddMonoidHom.range := rfl
  rw [e] at h
  exact Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite

omit hNF in
/-- Cox, Lemma 7.2, p. 133: the conductor times the maximal order lies in the order. -/
theorem conductor_mul_mem (x : 𝓞 K) : (conductor O : K) * (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := AddSubgroup.nsmul_index_mem (toRingOfIntegers O).toAddMonoidHom.range x
  have h : (y : K) = (conductor O : K) * (x : K) := by
    have h' := congrArg NumberField.RingOfIntegers.val hy
    simp only [nsmul_eq_mul, map_mul, map_natCast] at h'
    exact h'
  exact h ▸ y.2

omit hNF hO in
/-- The principal square root satisfies `√(4N) = 2√N` for a nonpositive integer `N`. -/
theorem sqrt_four_mul_intCast {N : ℤ} (hN : N ≤ 0) :
    Complex.sqrt ((4 * N : ℤ) : ℂ) = 2 * Complex.sqrt (N : ℂ) := by
  have hNR : (N : ℝ) ≤ 0 := by exact_mod_cast hN
  have h4R : ((4 * N : ℤ) : ℝ) ≤ 0 := by push_cast; linarith
  have e1 : ((4 * N : ℤ) : ℂ) = (((4 * N : ℤ) : ℝ) : ℂ) := by norm_cast
  have e2 : ((N : ℤ) : ℂ) = (((N : ℤ) : ℝ) : ℂ) := by norm_cast
  simp only [Complex.sqrt]
  rw [e1, e2, Complex.ofReal_cpow_of_nonpos h4R, Complex.ofReal_cpow_of_nonpos hNR]
  have e3 : -(((4 * N : ℤ) : ℝ) : ℂ) = ((4 : ℝ) : ℂ) * ((-(N : ℝ) : ℝ) : ℂ) := by
    push_cast; ring
  have e4 : -(((N : ℤ) : ℝ) : ℂ) = ((-(N : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [e3, e4, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by linarith)]
  have h2 : ((4 : ℝ) : ℂ) ^ (2⁻¹ : ℂ) = 2 := by
    rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (by norm_num),
      show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h2]
  ring

-- `O` and `hO` are parameters only so that `integerGenerator O` keeps its planned signature.
set_option linter.unusedSectionVars false in
include hIQ in
/-- Cox, equations (5.13)–(5.14) and (7.1), pp. 103 and 133. -/
theorem exists_integerGenerator :
    ∃ ω : 𝓞 K, ((ω : K) : ℂ) =
      ((NumberField.discr K : ℂ) + Complex.sqrt (NumberField.discr K : ℂ)) / 2 := by
  obtain ⟨N, r, hN, hsq, hr, hlin, hrC⟩ := exists_squarefree_generator (K := K)
  have hint := fun x => isIntegral_iff_squarefree_coordinates N hsq r hr hlin x
  have h2 : ((2 : K) : ℂ) = 2 := map_ofNat K.val 2
  rw [discr_eq_of_squarefree N hsq r hr hlin]
  split_ifs with h4
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, N = 2 * m + 1 := ⟨N / 2, by omega⟩
    refine ⟨⟨(m : K) + (1 + r) / 2, (hint _).mpr ⟨m, 1, by simp [h4]⟩⟩, ?_⟩
    rw [← hrC]
    change (((m : K) + (1 + r) / 2 : K) : ℂ) = _
    push_cast [h2, hm]
    ring
  · refine ⟨⟨(2 * N : K) + r, (hint _).mpr ⟨2 * N, 1, by simp [h4]⟩⟩, ?_⟩
    rw [sqrt_four_mul_intCast hN.le, ← hrC]
    change (((2 * N : K) + r : K) : ℂ) = _
    push_cast [h2]
    ring

/-- Cox's generator `(d_K + sqrt(d_K))/2`, equation (7.1), p. 133. -/
def integerGenerator : 𝓞 K := (exists_integerGenerator (O := O)).choose

include hIQ in
/-- Cox, equation (7.1), p. 133, the precise normalization of the generator. -/
theorem integerGenerator_coe : ((integerGenerator O : K) : ℂ) =
    ((NumberField.discr K : ℂ) + Complex.sqrt (NumberField.discr K : ℂ)) / 2 :=
  (exists_integerGenerator (O := O)).choose_spec

include hIQ in
/-- Cox, equation (7.1), p. 133, the integral basis of the maximal order. -/
theorem integerGenerator_span :
    Submodule.span ℤ ({1, integerGenerator O} : Set (𝓞 K)) = ⊤ := by
  obtain ⟨N, r, hN, hsq, hr, hlin, hrC⟩ := exists_squarefree_generator (K := K)
  obtain ⟨b, hb0, hb1⟩ := exists_integralBasis_of_squarefree N hsq r hr hlin
  have hg := integerGenerator_coe O
  have h2 : ((2 : K) : ℂ) = 2 := map_ofNat K.val 2
  rw [discr_eq_of_squarefree N hsq r hr hlin] at hg
  obtain ⟨c, hc⟩ : ∃ c : ℤ, integerGenerator O = (c : 𝓞 K) + b 1 := by
    split_ifs at hg hb1 with h4
    · obtain ⟨m, hm⟩ : ∃ m : ℤ, N = 2 * m + 1 := ⟨N / 2, by omega⟩
      have hb1' : algebraMap (𝓞 K) K (b 1) = (1 + r) / 2 := hb1
      refine ⟨m, NumberField.RingOfIntegers.ext (Subtype.ext ?_)⟩
      rw [hg, ← hrC]
      simp only [map_add, map_intCast, hb1']
      push_cast [h2, hm]
      ring
    · have hb1' : algebraMap (𝓞 K) K (b 1) = r := hb1
      refine ⟨2 * N, NumberField.RingOfIntegers.ext (Subtype.ext ?_)⟩
      rw [hg, sqrt_four_mul_intCast hN.le, ← hrC]
      simp only [map_add, map_intCast, hb1']
      push_cast [h2]
      ring
  have hb0' : b 0 = 1 := NumberField.RingOfIntegers.ext (by simpa using hb0)
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h1 : (1 : 𝓞 K) ∈ Submodule.span ℤ ({1, integerGenerator O} : Set (𝓞 K)) :=
    Submodule.subset_span (by simp)
  have hgm : integerGenerator O ∈ Submodule.span ℤ ({1, integerGenerator O} : Set (𝓞 K)) :=
    Submodule.subset_span (by simp)
  fin_cases i
  · simpa [hb0'] using h1
  · have e : b 1 = integerGenerator O - c • (1 : 𝓞 K) := by rw [hc]; simp
    simp only [Fin.mk_one, Fin.isValue]
    rw [e]
    exact Submodule.sub_mem _ hgm (Submodule.smul_mem _ _ h1)

include hIQ in
/-- Cox, Lemma 7.2, p. 133: `O = Z + f O_K`. -/
theorem mem_iff_int_add_conductor (x : K) :
    x ∈ O ↔ ∃ (a : ℤ) (b : 𝓞 K), x = a + (conductor O : K) * (b : K) := by
  constructor
  · intro hx
    let R := (toRingOfIntegers O).toAddMonoidHom.range
    have hR : ∀ a : ℤ, (a : 𝓞 K) ∈ R := fun a => ⟨(a : O), map_intCast (toRingOfIntegers O) a⟩
    have hspan : ∀ z : 𝓞 K, ∃ a b : ℤ, a • (1 : 𝓞 K) + b • integerGenerator O = z := fun z =>
      Submodule.mem_span_pair.mp (by rw [integerGenerator_span O]; trivial)
    have hmk : ∀ a b : ℤ, (QuotientAddGroup.mk (a • (1 : 𝓞 K) + b • integerGenerator O) :
        𝓞 K ⧸ R) = b • (QuotientAddGroup.mk (integerGenerator O) : 𝓞 K ⧸ R) := by
      intro a b
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr (by simpa using hR a),
        zero_add, QuotientAddGroup.mk_zsmul]
    have hord : addOrderOf (QuotientAddGroup.mk (integerGenerator O) : 𝓞 K ⧸ R) =
        conductor O := by
      rw [addOrderOf_eq_card_of_forall_mem_zmultiples, conductor, AddSubgroup.index_eq_card]
      intro y
      induction y using QuotientAddGroup.induction_on with
      | H z =>
        obtain ⟨a, b, rfl⟩ := hspan z
        exact ⟨b, (hmk a b).symm⟩
    obtain ⟨a, b, hab⟩ := hspan (toRingOfIntegers O ⟨x, hx⟩)
    have hb : b • (QuotientAddGroup.mk (integerGenerator O) : 𝓞 K ⧸ R) = 0 := by
      rw [← hmk a b, hab, QuotientAddGroup.eq_zero_iff]
      exact ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨k, hk⟩ := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hb
    rw [hord] at hk
    refine ⟨a, k • integerGenerator O, ?_⟩
    have hx' : x = ((toRingOfIntegers O ⟨x, hx⟩ : 𝓞 K) : K) := rfl
    rw [hx', ← hab, hk]
    simp only [map_add, zsmul_eq_mul, mul_one, map_intCast]
    push_cast
    ring
  · rintro ⟨a, b, rfl⟩
    exact O.add_mem (by simp) (conductor_mul_mem O b)

omit hNF hO in
include hIQ in
/-- Cox, Exercise 5.7(b), p. 117: complex conjugation on `K` is the trace minus the identity. -/
theorem star_coe_eq_trace_sub (x : K) :
    star ((x : K) : ℂ) = (((Algebra.trace ℚ K x : K) - x : K) : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h1 : ((x : K) : ℂ) ^ 2 - ((Algebra.trace ℚ K x : ℚ) : ℂ) * (x : ℂ) +
      ((Algebra.norm ℚ x : ℚ) : ℂ) = 0 := by
    simpa using congrArg (fun w : K => (w : ℂ)) (quadratic_characteristic_relation x)
  rw [fieldNorm_eq_mul_conj x] at h1
  have hxC : ((x : K) : ℂ) ≠ 0 := by simpa using hx
  have h2 : ((x : K) : ℂ) * ((x : ℂ) - ((Algebra.trace ℚ K x : ℚ) : ℂ) + star (x : ℂ)) = 0 := by
    linear_combination h1
  have h3 := (mul_eq_zero.mp h2).resolve_left hxC
  push_cast
  linear_combination h3

include hIQ in
/-- Cox, conjugation preserves an imaginary quadratic order, pp. 134–136. -/
theorem exists_conjugation :
    ∃ σ : O ≃+* O, ∀ x : O, ((σ x : K) : ℂ) = star ((x : K) : ℂ) := by
  have htr : ∀ x : O, ∃ t : ℤ, Algebra.trace ℚ K (x : K) = (t : ℚ) := fun x =>
    ((isIntegral_iff_trace_norm_int (x : K)).mp (isIntegral_of_mem O x.2)).1
  let f : O → O := fun x => ⟨(Algebra.trace ℚ K (x : K) : K) - x, by
    obtain ⟨t, ht⟩ := htr x
    rw [ht]
    exact O.sub_mem (by simp) x.2⟩
  have hf : ∀ x : O, ((f x : K) : ℂ) = star ((x : K) : ℂ) := fun x =>
    (star_coe_eq_trace_sub (x : K)).symm
  have hinj : ∀ y z : O, ((y : K) : ℂ) = ((z : K) : ℂ) → y = z := fun y z h =>
    Subtype.ext (Subtype.ext h)
  have hff : ∀ x, f (f x) = x := fun x => hinj _ _ (by rw [hf, hf, star_star])
  refine ⟨
    { toFun := f
      invFun := f
      left_inv := hff
      right_inv := hff
      map_mul' := fun x y => hinj _ _ ?_
      map_add' := fun x y => hinj _ _ ?_ }, hf⟩
  · rw [hf]
    push_cast
    rw [star_mul', hf, hf]
  · rw [hf]
    push_cast
    rw [star_add, hf, hf]

omit hNF hO in
/-- Membership in an integral ideal with normalized coordinates `α[1, τ]`, inside `K`. -/
theorem mem_coeIdeal_iff_of_coord (a : Ideal O) (α : Kˣ) (τ : K)
    (hcoord : ((a : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
      (α : K) • Submodule.span ℤ ({1, τ} : Set K)) (y : K) :
    y ∈ (a : FractionalIdeal O⁰ K) ↔ ∃ m n : ℤ, y = (α : K) * (m + n * τ) := by
  rw [← FractionalIdeal.mem_coe, ← Submodule.restrictScalars_mem ℤ, hcoord,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨m, n, rfl⟩ := Submodule.mem_span_pair.mp hz
    exact ⟨m, n, by simp [smul_eq_mul, zsmul_eq_mul]⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m + n * τ, Submodule.mem_span_pair.mpr ⟨m, n, by simp [zsmul_eq_mul]⟩, rfl⟩

omit hNF hO in
/-- Membership in an integral ideal with normalized coordinates `α[1, τ]`. -/
theorem mem_iff_of_coord (a : Ideal O) (α : Kˣ) (τ : K)
    (hcoord : ((a : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
      (α : K) • Submodule.span ℤ ({1, τ} : Set K)) (y : O) :
    y ∈ a ↔ ∃ m n : ℤ, (y : K) = (α : K) * (m + n * τ) := by
  rw [← mem_coeIdeal_iff_of_coord O a α τ hcoord, FractionalIdeal.mem_coeIdeal]
  exact ⟨fun hy => ⟨y, hy, rfl⟩, fun ⟨y', hy', e⟩ => by rwa [← Subtype.ext e]⟩

omit hNF hO in
/-- An element of the fractional ideal of an integral ideal lies in the order. -/
theorem mem_of_mem_coeIdeal (a : Ideal O) {y : K} (hy : y ∈ (a : FractionalIdeal O⁰ K)) :
    y ∈ O := by
  obtain ⟨y', -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
  exact y'.2

omit hNF hO in
/-- Cox, Lemma 7.5, pp. 135–136: the order of a proper lattice `α[1, τ]` is `[1, Aτ]`. -/
theorem toSubmodule_eq_normalized_span (a : FractionalIdeal O⁰ K) (ha : IsUnit a)
    (α : Kˣ) (τ : K) (A B C : ℤ) (hA : A ≠ 0) (hτ : LinearIndependent ℚ ![1, τ])
    (hq : (A : K) * τ ^ 2 + B * τ + C = 0)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1)
    (hcoord : (a : Submodule O K).restrictScalars ℤ =
      (α : K) • Submodule.span ℤ ({1, τ} : Set K)) :
    O.toSubmodule = Submodule.span ℤ ({1, (A : K) * τ} : Set K) := by
  have hmem : ∀ y : K, y ∈ a ↔ ∃ z ∈ Submodule.span ℤ ({1, τ} : Set K), (α : K) * z = y := by
    intro y
    rw [← FractionalIdeal.mem_coe, ← Submodule.restrictScalars_mem ℤ, hcoord,
      Submodule.mem_smul_pointwise_iff_exists]
    simp only [smul_eq_mul]
  ext x
  rw [Subalgebra.mem_toSubmodule, ← IsProper.multiplier_iff O (isProper_of_isUnit O ha) x,
    ← normalized_multiplier_iff τ hτ A B C hA hq hprim x]
  constructor
  · intro h z hz
    obtain ⟨w, hw, hw'⟩ := (hmem _).mp (h _ ((hmem _).mpr ⟨z, hz, rfl⟩))
    have e : x * z = w := mul_left_cancel₀ α.ne_zero (by rw [hw']; ring)
    rwa [e]
  · intro h y hy
    obtain ⟨z, hz, rfl⟩ := (hmem y).mp hy
    exact (hmem _).mpr ⟨x * z, h z hz, by ring⟩

include hIQ in
/-- Cox, equation (7.16), p. 140: compute a proper ideal norm in normalized coordinates. -/
theorem idealNorm_normalized (a : Ideal O) (ha : IsUnit (a : FractionalIdeal O⁰ K))
    (α : Kˣ) (τ : K) (A B C : ℤ) (hA : 0 < A)
    (hτ : LinearIndependent ℚ ![1, τ])
    (hq : (A : K) * τ ^ 2 + B * τ + C = 0)
    (hprim : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1)
    (hcoord : ((a : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
      (α : K) • Submodule.span ℤ ({1, τ} : Set K)) :
    (idealNorm O a : ℚ) = Algebra.norm ℚ (α : K) / A := by
  have hOspan := toSubmodule_eq_normalized_span O _ ha α τ A B C hA.ne' hτ hq hprim hcoord
  have hαK : (α : K) ≠ 0 := α.ne_zero
  have hrange : Set.range ![(1 : K), τ] = {1, τ} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  have hliZ : LinearIndependent ℤ ![(1 : K), τ] := LinearIndependent.restrict_scalars' (R := ℤ) hτ
  let S := Submodule.span ℤ (Set.range ![(1 : K), τ])
  let bs : Module.Basis (Fin 2) ℤ S := Module.Basis.span hliZ
  have hmemK := mem_coeIdeal_iff_of_coord O a α τ hcoord
  have hmemO := mem_iff_of_coord O a α τ hcoord
  have hinO : ∀ y : K, y ∈ (a : FractionalIdeal O⁰ K) → y ∈ O := fun y hy =>
    mem_of_mem_coeIdeal O a hy
  let α' : O := ⟨α, hinO _ ((hmemK _).mpr ⟨1, 0, by simp⟩)⟩
  let β : O := ⟨(α : K) * τ, hinO _ ((hmemK _).mpr ⟨0, 1, by simp⟩)⟩
  have hα'a : α' ∈ a := (hmemO α').mpr ⟨1, 0, by simp [α']⟩
  have hβa : β ∈ a := (hmemO β).mpr ⟨0, 1, by simp [β]⟩
  let φ : a.toAddSubgroup →+ S :=
    { toFun := fun y => ⟨(y.1 : K) / α, by
        obtain ⟨m, n, hmn⟩ := (hmemO y.1).mp y.2
        change _ ∈ Submodule.span ℤ (Set.range ![(1 : K), τ])
        rw [hmn, mul_div_cancel_left₀ _ hαK, hrange]
        exact Submodule.mem_span_pair.mpr ⟨m, n, by simp [zsmul_eq_mul]⟩⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun y z => Subtype.ext (by simp [add_div]) }
  let ψ : a.toAddSubgroup →+ ZMod A.natAbs :=
    (Int.castAddHom (ZMod A.natAbs)).comp ((bs.coord 1).toAddMonoidHom.comp φ)
  have hcoordval : ∀ (z : S) (m n : ℤ), (z : K) = m + n * τ → bs.repr z 1 = n := by
    intro z m n hz
    have e : z = m • bs 0 + n • bs 1 := by
      apply Subtype.ext
      rw [hz, Module.Basis.span_apply, Module.Basis.span_apply]
      simp [zsmul_eq_mul]
    rw [e, map_add, map_zsmul, map_zsmul, bs.repr_self, bs.repr_self]
    simp
  have hψ : ∀ (y : a.toAddSubgroup) (m n : ℤ), (y.1 : K) = (α : K) * (m + n * τ) →
      ψ y = n := by
    intro y m n hy
    have h := hcoordval (φ y) m n (by
      change (y.1 : K) / α = _
      rw [hy, mul_div_cancel_left₀ _ hαK])
    simp [ψ, Module.Basis.coord_apply, h]
  have hsurj : Function.Surjective ψ := by
    intro k
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective k
    refine ⟨k • ⟨β, hβa⟩, ?_⟩
    rw [map_zsmul, hψ ⟨β, hβa⟩ 0 1 (by simp [β])]
    simp
  have hker : ψ.ker = (Ideal.span {α'}).toAddSubgroup.addSubgroupOf a.toAddSubgroup := by
    ext ⟨y, hy⟩
    obtain ⟨m, n, hmn⟩ := (hmemO y).mp hy
    rw [AddMonoidHom.mem_ker, hψ ⟨y, hy⟩ m n hmn, AddSubgroup.mem_addSubgroupOf,
      Submodule.mem_toAddSubgroup, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨k, rfl⟩
      have hz : (m : K) + k * ((A : K) * τ) ∈ O := by
        rw [← Subalgebra.mem_toSubmodule, hOspan]
        exact Submodule.mem_span_pair.mpr ⟨m, k, by simp [zsmul_eq_mul]⟩
      refine ⟨⟨_, hz⟩, Subtype.ext ?_⟩
      change ((m : K) + k * ((A : K) * τ)) * α = (y : K)
      rw [hmn]
      push_cast
      ring
    · rintro ⟨z, hz⟩
      have hzO : (z : K) ∈ Submodule.span ℤ ({1, (A : K) * τ} : Set K) := by
        rw [← hOspan]
        exact z.2
      obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hzO
      have h1 : (z : K) * α = (y : K) := congrArg Subtype.val hz
      have h2 : m • (1 : K) + n • τ = p • (1 : K) + (q * A) • τ := by
        apply mul_left_cancel₀ hαK
        rw [← hpq] at h1
        simp only [zsmul_eq_mul, mul_one] at h1 ⊢
        push_cast
        linear_combination -hmn - h1
      exact ⟨q, by rw [(hliZ.eq_of_pair h2).2, mul_comm]⟩
  have hle : (Ideal.span {α'}).toAddSubgroup ≤ a.toAddSubgroup := by
    intro x hx
    exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hα'a)) hx
  have hmul := AddSubgroup.relIndex_mul_index hle
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj,
    AddSubgroup.card_top, Nat.card_zmod] at hmul
  have h1 : a.toAddSubgroup.index = idealNorm O a := by
    rw [AddSubgroup.index_eq_card]
    rfl
  have h2 : (Ideal.span {α'}).toAddSubgroup.index = elementNorm O α' := by
    rw [AddSubgroup.index_eq_card, ← idealNorm_span_singleton O α']
    rfl
  rw [h1, h2] at hmul
  have h3 : (elementNorm O α' : ℚ) = Algebra.norm ℚ (α : K) := elementNorm_eq_fieldNorm O α'
  have hAabs : (A.natAbs : ℚ) = A := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hA)]
  rw [eq_div_iff (by exact_mod_cast hA.ne' : (A : ℚ) ≠ 0), ← h3, ← hmul]
  push_cast
  rw [hAabs]
  ring

omit hNF hO in
include hIQ in
/-- Cox, Exercise 7.12: the trace of a normalized quadratic root is `-B/A`. -/
theorem trace_eq_of_quadratic (τ : K) (hτ : LinearIndependent ℚ ![1, τ]) (A B C : ℤ)
    (hA : A ≠ 0) (hq : (A : K) * τ ^ 2 + B * τ + C = 0) :
    Algebra.trace ℚ K τ = -(B : ℚ) / A := by
  have h1 := quadratic_characteristic_relation τ
  have hA' : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  rw [LinearIndependent.pair_iff] at hτ
  have h2 := hτ (C - A * Algebra.norm ℚ τ) (A * Algebra.trace ℚ K τ + B) (by
    simp only [Rat.smul_def, mul_one]
    push_cast
    linear_combination (-(A : K)) * h1 + hq)
  field_simp
  linarith [h2.2]

omit hNF hO in
include hIQ in
/-- Complex conjugation on `K`, written as trace minus identity, is multiplicative. -/
theorem trace_sub_mul (x y : K) :
    (Algebra.trace ℚ K (x * y) : K) - x * y =
      ((Algebra.trace ℚ K x : K) - x) * ((Algebra.trace ℚ K y : K) - y) := by
  apply Subtype.ext
  rw [← star_coe_eq_trace_sub, IntermediateField.coe_mul, IntermediateField.coe_mul,
    ← star_coe_eq_trace_sub, ← star_coe_eq_trace_sub, star_mul']

omit hNF hO in
/-- Trace minus identity is additive. -/
theorem trace_sub_add (x y : K) :
    (Algebra.trace ℚ K (x + y) : K) - (x + y) =
      ((Algebra.trace ℚ K x : K) - x) + ((Algebra.trace ℚ K y : K) - y) := by
  rw [map_add]
  push_cast
  ring

omit hNF hO in
include hIQ in
/-- Trace minus identity fixes the integers. -/
theorem trace_sub_intCast (m : ℤ) : (Algebra.trace ℚ K (m : K) : K) - m = m := by
  apply Subtype.ext
  rw [← star_coe_eq_trace_sub]
  simp

omit hNF hO in
include hIQ in
/-- Cox, (7.6): the field norm is `x` times its conjugate. -/
theorem norm_eq_mul_trace_sub (x : K) :
    ((Algebra.norm ℚ x : ℚ) : K) = x * ((Algebra.trace ℚ K x : K) - x) := by
  apply Subtype.ext
  rw [IntermediateField.coe_mul, ← star_coe_eq_trace_sub, ← fieldNorm_eq_mul_conj]
  simp

omit hNF hO in
/-- A principal ideal of the order, viewed as an integer lattice. -/
theorem restrictScalars_span_singleton (x : O) :
    (Submodule.span O {algebraMap O K x}).restrictScalars ℤ = (x : K) • O.toSubmodule := by
  ext y
  rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨o, rfl⟩
    exact ⟨o, o.2, by simp [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, by simp [Algebra.smul_def, mul_comm]⟩

omit hNF hO in
include hIQ in
/-- Cox, pp. 136 and 140: conjugating an ideal `α[1, τ]` gives `ᾱ[1, τ̄]`. -/
theorem restrictScalars_map_conj (a : Ideal O) (σ : O ≃+* O)
    (hσ : ∀ x : O, ((σ x : K) : ℂ) = star ((x : K) : ℂ)) (α : Kˣ) (τ : K)
    (hcoord : ((a : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
      (α : K) • Submodule.span ℤ ({1, τ} : Set K)) :
    ((a.map σ.toRingHom : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ =
      ((Algebra.trace ℚ K (α : K) : K) - α) •
        Submodule.span ℤ ({1, (Algebra.trace ℚ K τ : K) - τ} : Set K) := by
  have hσc : ∀ x : O, ((σ x : O) : K) = (Algebra.trace ℚ K (x : K) : K) - x := fun x =>
    Subtype.ext ((hσ x).trans (star_coe_eq_trace_sub _))
  ext y
  rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x', hx', rfl⟩
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective σ.toRingHom σ.surjective).mp hx'
    obtain ⟨m, n, hmn⟩ := (mem_iff_of_coord O a α τ hcoord x).mp hx
    refine ⟨m + n * ((Algebra.trace ℚ K τ : K) - τ),
      Submodule.mem_span_pair.mpr ⟨m, n, by simp [zsmul_eq_mul]⟩, ?_⟩
    change _ = ((σ x : O) : K)
    rw [hσc, hmn, smul_eq_mul, trace_sub_mul, trace_sub_add, trace_sub_mul, trace_sub_intCast,
      trace_sub_intCast]
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨m, n, rfl⟩ := Submodule.mem_span_pair.mp hz
    let x : O := ⟨(α : K) * (m + n * τ), mem_of_mem_coeIdeal O a
      ((mem_coeIdeal_iff_of_coord O a α τ hcoord _).mpr ⟨m, n, rfl⟩)⟩
    refine ⟨σ x, (Ideal.mem_map_iff_of_surjective σ.toRingHom σ.surjective).mpr
      ⟨x, (mem_iff_of_coord O a α τ hcoord x).mpr ⟨m, n, rfl⟩, rfl⟩, ?_⟩
    change ((σ x : O) : K) = _
    rw [hσc]
    simp only [x, trace_sub_mul, trace_sub_add, trace_sub_intCast, smul_eq_mul, zsmul_eq_mul,
      mul_one]

omit hNF hO in
/-- Scalars pull out of products of integer lattices in a field. -/
theorem smul_mul_smul_submodule {F : Type*} [Field F] (x y : F) (M N : Submodule ℤ F) :
    (x • M) * (y • N) = (x * y) • (M * N) := by
  rw [← Submodule.span_singleton_mul, ← Submodule.span_singleton_mul,
    ← Submodule.span_singleton_mul, mul_mul_mul_comm, Submodule.span_mul_span,
    Set.singleton_mul_singleton]

omit hNF hO in
/-- Successive scalings of an integer lattice in a field compose. -/
theorem smul_smul_submodule {F : Type*} [Field F] (x y : F) (M : Submodule ℤ F) :
    x • y • M = (x * y) • M :=
  smul_smul x y M

include hIQ in
/-- Cox, Lemma 7.14(iii), pp. 140–141, from (7.6) and (7.16). -/
theorem ideal_mul_conjugate (a : Ideal O) (ha : IsUnit (a : FractionalIdeal O⁰ K))
    (σ : O ≃+* O) (hσ : ∀ x : O, ((σ x : K) : ℂ) = star ((x : K) : ℂ)) :
    a * a.map σ.toRingHom = Ideal.span {(idealNorm O a : O)} := by
  obtain ⟨α, τ, hτ, hcoord⟩ := exists_normalized_basis O (a : FractionalIdeal O⁰ K) ha.ne_zero
  obtain ⟨A, B, C, hA, hq, hprim⟩ : ∃ A B C : ℤ, 0 < A ∧ (A : K) * τ ^ 2 + B * τ + C = 0 ∧
      Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1 := by
    obtain ⟨A, B, C, hA, hq, hprim⟩ := exists_primitive_quadratic_relation τ hτ
    rcases hA.lt_or_gt with hneg | hpos
    · exact ⟨-A, -B, -C, by omega, by push_cast; linear_combination -hq,
        by simpa only [Int.natAbs_neg] using hprim⟩
    · exact ⟨A, B, C, hpos, hq, hprim⟩
  have hnorm := idealNorm_normalized O a ha α τ A B C hA hτ hq hprim hcoord
  have hOspan := toSubmodule_eq_normalized_span O _ ha α τ A B C hA.ne' hτ hq hprim hcoord
  have hcτ : (Algebra.trace ℚ K τ : K) - τ = -(B : K) / A - τ := by
    rw [trace_eq_of_quadratic τ hτ A B C hA.ne' hq]
    push_cast
    ring
  have key : (α : K) * ((Algebra.trace ℚ K (α : K) : K) - α) * (A : K)⁻¹ =
      ((idealNorm O a : O) : K) := by
    have h : ((idealNorm O a : ℚ) : K) = ((Algebra.norm ℚ (α : K) / A : ℚ) : K) := by
      rw [hnorm]
    rw [← norm_eq_mul_trace_sub, show ((idealNorm O a : O) : K) = ((idealNorm O a : ℚ) : K) by
      simp, h]
    push_cast
    ring
  apply FractionalIdeal.coeIdeal_injective (K := K)
  change ((a * a.map σ.toRingHom : Ideal O) : FractionalIdeal O⁰ K) =
    ((Ideal.span {(idealNorm O a : O)} : Ideal O) : FractionalIdeal O⁰ K)
  rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton]
  apply Submodule.restrictScalars_injective ℤ
  rw [Submodule.restrictScalars_mul, hcoord, restrictScalars_map_conj O a σ hσ α τ hcoord,
    restrictScalars_span_singleton, hcτ, smul_mul_smul_submodule,
    normalized_span_mul τ A B C hA.ne' hq hprim, ← hOspan, smul_smul_submodule, key]

include hIQ in
/-- Cox, Lemma 7.14(i): the ideal generated by a natural number `n` has norm `n²`. -/
theorem idealNorm_span_natCast (n : ℕ) : idealNorm O (Ideal.span {(n : O)}) = n ^ 2 := by
  let b : Module.Basis (Fin 2) ℤ O := Module.finBasisOfFinrankEq ℤ O (finrank O)
  rw [idealNorm_span_singleton, elementNorm, show (n : O) = algebraMap ℤ O (n : ℤ) by simp,
    Algebra.norm_algebraMap_of_basis b, Fintype.card_fin]
  simp

include hIQ in
/-- Cox, Lemma 7.14(ii), pp. 140–141. -/
theorem idealNorm_mul (a b : Ideal O) (ha : IsUnit (a : FractionalIdeal O⁰ K))
    (hb : IsUnit (b : FractionalIdeal O⁰ K)) :
    idealNorm O (a * b) = idealNorm O a * idealNorm O b := by
  obtain ⟨σ, hσ⟩ := exists_conjugation O
  have hab : IsUnit ((a * b : Ideal O) : FractionalIdeal O⁰ K) := by
    rw [FractionalIdeal.coeIdeal_mul]
    exact ha.mul hb
  have h := ideal_mul_conjugate O (a * b) hab σ hσ
  rw [Ideal.map_mul, mul_mul_mul_comm, ideal_mul_conjugate O a ha σ hσ,
    ideal_mul_conjugate O b hb σ hσ, Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul] at h
  have h2 := congrArg (idealNorm O) h
  rw [idealNorm_span_natCast, idealNorm_span_natCast] at h2
  exact (Nat.pow_left_injective two_ne_zero h2).symm

/-- A primitive proper ideal has no nontrivial integral scalar factor; Cox, p. 236. -/
def IsPrimitiveIdeal (a : Ideal O) : Prop :=
  ∀ (d : ℕ) (b : Ideal O), 1 < d → IsUnit (b : FractionalIdeal O⁰ K) →
    a ≠ Ideal.span {(d : O)} * b

/-- A primitive order element has no nontrivial integral scalar factor; Cox, p. 237. -/
def IsPrimitiveElement (α : O) : Prop :=
  ∀ (d : ℕ) (β : O), 1 < d → α ≠ (d : O) * β

/-- Cox, the paragraph preceding Corollary 11.27, p. 237. -/
theorem isPrimitiveIdeal_span_singleton_iff (α : O) (hα : α ≠ 0) :
    IsPrimitiveIdeal O (Ideal.span {α}) ↔ IsPrimitiveElement O α := by
  constructor
  · intro h d β hd hαβ
    have hβ : (β : K) ≠ 0 := by
      rintro hβ
      apply hα
      rw [hαβ, show β = 0 from Subtype.ext hβ, mul_zero]
    refine h d (Ideal.span {β}) hd ?_ (by rw [hαβ, Ideal.span_singleton_mul_span_singleton])
    rw [FractionalIdeal.coeIdeal_span_singleton]
    exact ⟨toPrincipalIdeal O K (Units.mk0 _ hβ), coe_toPrincipalIdeal _⟩
  · intro h d b hd _ hab
    have hmem : α ∈ Ideal.span {(d : O)} * b := hab ▸ Ideal.mem_span_singleton_self α
    obtain ⟨z, -, hz⟩ := Ideal.mem_span_singleton_mul.mp hmem
    exact h d z hd hz.symm

include hIQ in
/-- Cox, the prime-norm observation in the proof of Theorem 11.1, p. 237. -/
theorem isPrimitiveIdeal_of_prime_norm (a : Ideal O)
    (_ha : IsUnit (a : FractionalIdeal O⁰ K)) (hp : (idealNorm O a).Prime) :
    IsPrimitiveIdeal O a := by
  intro d b hd hb hab
  have hd0 : ((d : O) : K) ≠ 0 := by
    have h : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have hdunit : IsUnit ((Ideal.span {(d : O)} : Ideal O) : FractionalIdeal O⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton]
    exact ⟨toPrincipalIdeal O K (Units.mk0 _ hd0), coe_toPrincipalIdeal _⟩
  have hN := idealNorm_mul O _ b hdunit hb
  rw [← hab, idealNorm_span_natCast] at hN
  have hdvd : d ∣ idealNorm O a := ⟨d * idealNorm O b, by rw [hN]; ring⟩
  rcases hp.eq_one_or_self_of_dvd d hdvd with h1 | h1
  · omega
  · have hpos : 0 < idealNorm O b := by
      rcases Nat.eq_zero_or_pos (idealNorm O b) with h0 | h0
      · rw [h0, mul_zero] at hN
        exact absurd hN hp.ne_zero
      · exact h0
    have : d ^ 2 * idealNorm O b > d := by
      calc d ^ 2 * idealNorm O b ≥ d ^ 2 := Nat.le_mul_of_pos_right _ hpos
        _ > d := by nlinarith
    omega

/-- The product ideal viewed inside the underlying integer module; Cox, Lemma 11.26, p. 236. -/
def productSubmodule (a : Ideal O) (I : (FractionalIdeal O⁰ K)ˣ) :
    Submodule ℤ (I : Submodule O K) :=
  ((((a : FractionalIdeal O⁰ K) * (I : FractionalIdeal O⁰ K) :
      FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ).comap
    (((I : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ).subtype

omit hNF hO in
/-- Cox, Lemma 11.26, p. 236, membership in the product viewed as a sublattice. -/
theorem mem_productSubmodule (a : Ideal O) (I : (FractionalIdeal O⁰ K)ˣ)
    (x : (I : Submodule O K)) :
    x ∈ productSubmodule O a I ↔
      (x : K) ∈ (a : FractionalIdeal O⁰ K) * (I : FractionalIdeal O⁰ K) :=
  Iff.rfl

omit hNF hO in
/-- Cox, Lemma 11.26, p. 236, inclusion of the product lattice. -/
theorem fractionalIdeal_mul_le (a : Ideal O) (I : (FractionalIdeal O⁰ K)ˣ) :
    (a : FractionalIdeal O⁰ K) * (I : FractionalIdeal O⁰ K) ≤ I :=
  (mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans_eq (one_mul _)

omit hNF hO in
/-- The norm of an integral ideal is its index in the order, as lattices of `K`. -/
theorem relIndex_coeIdeal (J : Ideal O) :
    ((J : FractionalIdeal O⁰ K) : Submodule O K).toAddSubgroup.relIndex
      O.toSubmodule.toAddSubgroup = idealNorm O J := by
  let f : O →+ K := O.val.toAddMonoidHom
  have hJ : J.toAddSubgroup.map f =
      ((J : FractionalIdeal O⁰ K) : Submodule O K).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_coeIdeal]
    rfl
  have hOK : (⊤ : AddSubgroup O).map f = O.toSubmodule.toAddSubgroup := by
    ext x
    simp [f]
  rw [← hJ, ← hOK, AddSubgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective,
    AddSubgroup.relIndex_top_right, AddSubgroup.index_eq_card]
  rfl

/-- Multiplying two lattices by the same nonzero scalar preserves their relative index. -/
theorem relIndex_spanSingleton_mul {c : K} (hc : c ≠ 0) (J₁ J₂ : FractionalIdeal O⁰ K) :
    ((FractionalIdeal.spanSingleton O⁰ c * J₁ : FractionalIdeal O⁰ K) :
        Submodule O K).toAddSubgroup.relIndex
      ((FractionalIdeal.spanSingleton O⁰ c * J₂ : FractionalIdeal O⁰ K) :
        Submodule O K).toAddSubgroup =
    ((J₁ : Submodule O K).toAddSubgroup).relIndex (J₂ : Submodule O K).toAddSubgroup := by
  let μ : K →+ K := AddMonoidHom.mulLeft c
  have hmap : ∀ J : FractionalIdeal O⁰ K, ((J : Submodule O K).toAddSubgroup).map μ =
      ((FractionalIdeal.spanSingleton O⁰ c * J : FractionalIdeal O⁰ K) :
        Submodule O K).toAddSubgroup := by
    intro J
    ext x
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_singleton_mul, μ, AddMonoidHom.coe_mulLeft]
    exact ⟨fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩, fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩⟩
  rw [← hmap, ← hmap, AddSubgroup.relIndex_map_map_of_injective _ _ (mul_right_injective₀ hc)]

include hIQ in
/-- Cox, Lemma 11.26, p. 236: `[b : ab] = N(a)` for invertible integral ideals. -/
theorem relIndex_coeIdeal_mul (a b : Ideal O) (ha : IsUnit (a : FractionalIdeal O⁰ K))
    (hb : IsUnit (b : FractionalIdeal O⁰ K)) :
    (((a * b : Ideal O) : FractionalIdeal O⁰ K) : Submodule O K).toAddSubgroup.relIndex
      ((b : FractionalIdeal O⁰ K) : Submodule O K).toAddSubgroup = idealNorm O a := by
  have hle1 : (((a * b : Ideal O) : FractionalIdeal O⁰ K) : Submodule O K).toAddSubgroup ≤
      ((b : FractionalIdeal O⁰ K) : Submodule O K).toAddSubgroup := by
    intro x hx
    change x ∈ ((a * b : Ideal O) : FractionalIdeal O⁰ K) at hx
    change x ∈ (b : FractionalIdeal O⁰ K)
    obtain ⟨x', hx', rfl⟩ := (FractionalIdeal.mem_coeIdeal O⁰ (I := a * b)).mp hx
    exact FractionalIdeal.mem_coeIdeal_of_mem O⁰ (Ideal.mul_le_right hx')
  have hle2 : ((b : FractionalIdeal O⁰ K) : Submodule O K).toAddSubgroup ≤
      O.toSubmodule.toAddSubgroup := by
    intro x hx
    change x ∈ (b : FractionalIdeal O⁰ K) at hx
    obtain ⟨x', _, hxx'⟩ := (FractionalIdeal.mem_coeIdeal O⁰ (I := b)).mp hx
    change x ∈ O
    rw [← hxx']
    exact x'.2
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  rw [relIndex_coeIdeal, relIndex_coeIdeal, idealNorm_mul O a b ha hb] at hmul
  have hb0 : b ≠ ⊥ := fun h => hb.ne_zero (FractionalIdeal.coeIdeal_eq_zero.mpr h)
  exact Nat.eq_of_mul_eq_mul_right (idealNorm_pos O b hb0) hmul

include hIQ in
/-- Cox, Lemma 11.26, p. 236, the index calculation. -/
theorem index_productSubmodule (a : Ideal O) (ha : IsUnit (a : FractionalIdeal O⁰ K))
    (I : (FractionalIdeal O⁰ K)ˣ) :
    (productSubmodule O a I).toAddSubgroup.index = idealNorm O a := by
  have hidx : (productSubmodule O a I).toAddSubgroup.index =
      (((a : FractionalIdeal O⁰ K) * I : FractionalIdeal O⁰ K) :
        Submodule O K).toAddSubgroup.relIndex ((I : FractionalIdeal O⁰ K) :
          Submodule O K).toAddSubgroup := rfl
  obtain ⟨c, b, hc0, hIb⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (I : FractionalIdeal O⁰ K)
  have hcK : algebraMap O K c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hc0
  have hcI : FractionalIdeal.spanSingleton O⁰ (algebraMap O K c) * I = b := by
    rw [hIb, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hcK,
      FractionalIdeal.spanSingleton_one, one_mul]
  have hcaI : FractionalIdeal.spanSingleton O⁰ (algebraMap O K c) *
      ((a : FractionalIdeal O⁰ K) * I) = ((a * b : Ideal O) : FractionalIdeal O⁰ K) := by
    rw [mul_left_comm, hcI, FractionalIdeal.coeIdeal_mul]
  have hb : IsUnit (b : FractionalIdeal O⁰ K) := by
    rw [← hcI]
    exact IsUnit.mul ⟨toPrincipalIdeal O K (Units.mk0 _ hcK), coe_toPrincipalIdeal _⟩ I.isUnit
  rw [hidx, ← relIndex_spanSingleton_mul O hcK, hcaI, hcI, relIndex_coeIdeal_mul O a b ha hb]

omit hNF hO in
/-- Cox, Exercise 11.16(a), used in Lemma 11.26, p. 236: a noncyclic rank-two quotient
has a common scalar divisor in its inclusion matrix. -/
theorem not_isAddCyclic_iff_exists_scalar {M : Type*} [AddCommGroup M] [Module ℤ M]
    (bM : Module.Basis (Fin 2) ℤ M) (N : Submodule ℤ M)
    (bN : Module.Basis (Fin 2) ℤ N) :
    ¬ IsAddCyclic (M ⧸ N) ↔
      ∃ d : ℕ, 1 < d ∧ ∀ x ∈ N, ∃ y : M, x = (d : ℤ) • y := by
  obtain rfl := Subsingleton.elim ‹Module ℤ M› (AddCommGroup.toIntModule M)
  classical
  let A := LinearMap.toMatrix bN bM N.subtype
  have hA : ∀ i j, A i j = bM.repr (bN j : M) i := fun i j => LinearMap.toMatrix_apply _ _ _ _ _
  rw [Module.Basis.quotient_isAddCyclic_iff_content_toMatrix_eq_one
    bM N bN]
  constructor
  · intro hne
    refine ⟨A.content, ?_, ?_⟩
    · rcases Nat.lt_or_ge 1 A.content with h | h
      · exact h
      · interval_cases hc : A.content
        · exfalso
          have hzero : ∀ i, bM.repr (bN 0 : M) i = 0 := fun i => by
            have := Matrix.content_dvd_entry A i 0
            rw [hc, zero_dvd_iff, Int.natAbs_eq_zero, hA] at this
            exact this
          have h0 : (bN 0 : M) = 0 := bM.repr.injective (Finsupp.ext fun i => by simp [hzero i])
          exact bN.ne_zero 0 (Subtype.ext h0)
        · exact absurd rfl hne
    · intro x hx
      have hdiv : ∀ i, (A.content : ℤ) ∣ bM.repr x i := by
        intro i
        have h : bM.repr x i = ∑ j, bN.repr ⟨x, hx⟩ j * A i j := by
          have hx' := congrArg (fun z : N => bM.repr (z : M) i) (bN.sum_repr ⟨x, hx⟩)
          simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul,
            Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul] at hx'
          rw [← hx']
          simp [hA]
        rw [h]
        exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right
          (Int.natCast_dvd.mpr (Matrix.content_dvd_entry A i j)) _
      refine ⟨∑ i, (bM.repr x i / A.content) • bM i, ?_⟩
      rw [Finset.smul_sum]
      conv_lhs => rw [← bM.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, Int.mul_ediv_cancel' (hdiv i)]
  · rintro ⟨d, hd, hN⟩ h1
    have hdvd : d ∣ A.content := Matrix.dvd_content fun i j => by
      obtain ⟨y, hy⟩ := hN (bN j : M) (bN j).2
      rw [← Int.natCast_dvd, hA, hy, map_zsmul, Finsupp.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    rw [h1, Nat.dvd_one] at hdvd
    omega

include hIQ in
/-- Cox, Lemma 11.26, p. 236: the product lattice `aI` has rank two. -/
theorem finrank_productSubmodule (a : Ideal O) (ha : a ≠ ⊥) (I : (FractionalIdeal O⁰ K)ˣ) :
    Module.finrank ℤ (productSubmodule O a I) = 2 := by
  have hne : (a : FractionalIdeal O⁰ K) * I ≠ 0 := fun h =>
    FractionalIdeal.coeIdeal_ne_zero.mpr ha ((Units.mul_left_eq_zero I).mp h)
  rw [← fractionalIdeal_finrank O _ hne]
  exact (Submodule.comapSubtypeEquivOfLe
    (p := (((a : FractionalIdeal O⁰ K) * I : FractionalIdeal O⁰ K) :
      Submodule O K).restrictScalars ℤ)
    (q := ((I : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ)
    fun x hx => fractionalIdeal_mul_le O a I hx).finrank_eq

include hIQ in
/-- Cox, Exercise 11.16(a) applied to `aI ⊆ I`: the quotient is noncyclic exactly when the
product lattice is divisible by a common integer `d > 1`. -/
theorem not_isAddCyclic_productSubmodule_iff (a : Ideal O) (ha : a ≠ ⊥)
    (I : (FractionalIdeal O⁰ K)ˣ) :
    ¬ IsAddCyclic ((I : Submodule O K) ⧸ productSubmodule O a I) ↔
      ∃ d : ℕ, 1 < d ∧ ∀ x ∈ productSubmodule O a I,
        ∃ y : (I : Submodule O K), x = (d : ℤ) • y := by
  haveI : Module.Finite ℤ (I : Submodule O K) := fractionalIdeal_moduleFinite O I
  haveI : Module.Free ℤ (I : Submodule O K) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite ℤ (productSubmodule O a I) :=
    Module.IsNoetherian.finite ℤ (productSubmodule O a I)
  haveI : Module.Free ℤ (productSubmodule O a I) := Module.free_of_finite_type_torsion_free'
  exact not_isAddCyclic_iff_exists_scalar
    (Module.finBasisOfFinrankEq ℤ _ (fractionalIdeal_finrank O I I.ne_zero)) _
    (Module.finBasisOfFinrankEq ℤ _ (finrank_productSubmodule O a ha I))

include hIQ in
/-- Cox, Lemma 11.26, pp. 236–237: cancellation of the invertible ideal gives
an integral proper scalar factor. -/
theorem exists_scalar_factor_of_not_cyclic (a : Ideal O)
    (ha : IsUnit (a : FractionalIdeal O⁰ K)) (I : (FractionalIdeal O⁰ K)ˣ)
    (h : ¬ IsAddCyclic ((I : Submodule O K) ⧸ productSubmodule O a I)) :
    ∃ (d : ℕ) (b : Ideal O), 1 < d ∧ IsUnit (b : FractionalIdeal O⁰ K) ∧
      a = Ideal.span {(d : O)} * b := by
  have ha0 : a ≠ ⊥ := fun h0 => ha.ne_zero (FractionalIdeal.coeIdeal_eq_zero.mpr h0)
  obtain ⟨d, hd, hdiv⟩ := (not_isAddCyclic_productSubmodule_iff O a ha0 I).mp h
  have hδ : algebraMap O K (d : O) = (d : K) := by simp
  have hδ0 : algebraMap O K (d : O) ≠ 0 := by
    rw [hδ]
    exact Nat.cast_ne_zero.mpr (by omega)
  have h1 : FractionalIdeal.spanSingleton O⁰ (algebraMap O K (d : O))⁻¹ *
      ((a : FractionalIdeal O⁰ K) * I) ≤ I := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hx
    obtain ⟨z, hz⟩ := hdiv ⟨y, fractionalIdeal_mul_le O a I hy⟩ hy
    have hyz : y = algebraMap O K (d : O) * z := by
      have := congrArg Subtype.val hz
      simpa [hδ] using this
    rw [hyz, ← mul_assoc, inv_mul_cancel₀ hδ0, one_mul]
    exact z.2
  have h2 : FractionalIdeal.spanSingleton O⁰ (algebraMap O K (d : O))⁻¹ *
      (a : FractionalIdeal O⁰ K) ≤ 1 := by
    have h3 := mul_le_mul_left h1 (↑I⁻¹ : FractionalIdeal O⁰ K)
    simpa only [mul_assoc, Units.mul_inv, mul_one] using h3
  obtain ⟨b, hb⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp h2
  refine ⟨d, b, hd, ?_, ?_⟩
  · rw [hb]
    exact IsUnit.mul ⟨toPrincipalIdeal O K (Units.mk0 _ (inv_ne_zero hδ0)),
      coe_toPrincipalIdeal _⟩ ha
  · apply (FractionalIdeal.coeIdeal_inj (K := K)).mp
    rw [FractionalIdeal.coeIdeal_mul, hb, FractionalIdeal.coeIdeal_span_singleton, ← mul_assoc,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hδ0,
      FractionalIdeal.spanSingleton_one, one_mul]

include hIQ in
/-- Cox, Exercise 11.19, p. 248: a scalar factor gives a quotient of `(Z/dZ)^2`. -/
theorem not_cyclic_of_scalar_factor (a b : Ideal O) (d : ℕ) (hd : 1 < d)
    (hb : IsUnit (b : FractionalIdeal O⁰ K))
    (hab : a = Ideal.span {(d : O)} * b) (I : (FractionalIdeal O⁰ K)ˣ) :
    ¬ IsAddCyclic ((I : Submodule O K) ⧸ productSubmodule O a I) := by
  have hd0 : ((d : O) : K) ≠ 0 := by
    have h : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have ha0 : a ≠ ⊥ := by
    rw [hab]
    intro h
    rcases Ideal.mul_eq_bot.mp h with h | h
    · exact hd0 (by simp [Ideal.span_singleton_eq_bot.mp h])
    · exact hb.ne_zero (FractionalIdeal.coeIdeal_eq_zero.mpr h)
  rw [not_isAddCyclic_productSubmodule_iff O a ha0 I]
  refine ⟨d, hd, fun x hx => ?_⟩
  rw [mem_productSubmodule, hab, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_span_singleton, mul_assoc, FractionalIdeal.mem_singleton_mul] at hx
  obtain ⟨z, hz, hxz⟩ := hx
  refine ⟨⟨z, fractionalIdeal_mul_le O b I hz⟩, Subtype.ext ?_⟩
  rw [hxz]
  simp

include hIQ in
/-- Cox, Lemma 11.26 and Exercise 11.19, pp. 236–237 and 248. -/
theorem quotient_isAddCyclic_iff (a : Ideal O)
    (ha : IsUnit (a : FractionalIdeal O⁰ K)) (I : (FractionalIdeal O⁰ K)ˣ) :
    IsAddCyclic ((I : Submodule O K) ⧸ productSubmodule O a I) ↔ IsPrimitiveIdeal O a := by
  constructor
  · intro hcyc d b hd hb hab
    exact not_cyclic_of_scalar_factor O a b d hd hb hab I hcyc
  · intro hprim
    by_contra hnot
    obtain ⟨d, b, hd, hb, hab⟩ := exists_scalar_factor_of_not_cyclic O a ha I hnot
    exact hprim d b hd hb hab

omit hNF hO in
/-- The product lattice `aI`, embedded back into `K`. -/
theorem map_subtype_productSubmodule (a : Ideal O) (I : (FractionalIdeal O⁰ K)ˣ) :
    (productSubmodule O a I).map
        (((I : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ).subtype =
      (((a : FractionalIdeal O⁰ K) * I : FractionalIdeal O⁰ K) :
        Submodule O K).restrictScalars ℤ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, fractionalIdeal_mul_le O a I hx⟩, hx, rfl⟩

include hIQ in
/-- Cox, Lemma 11.26, pp. 236–237, realization as a cyclic period sublattice. -/
theorem exists_cyclicSublattice (a : Ideal O) (ha : IsUnit (a : FractionalIdeal O⁰ K))
    (hprim : IsPrimitiveIdeal O a) (I : (FractionalIdeal O⁰ K)ˣ)
    (hpos : 0 < idealNorm O a) :
    ∃ S : PeriodPair.CyclicSublattice (periodPair O I) ⟨idealNorm O a, hpos⟩,
      S.j = idealJ O (integralIdealUnit O a ha * I) := by
  let IZ : Submodule ℤ K := ((I : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ
  let f : K →ₗ[ℤ] ℂ := K.val.toLinearMap.restrictScalars ℤ
  have hlatI : IZ.map f = (periodPair O I).lattice := (periodPair_lattice O I).symm
  let e : IZ ≃ₗ[ℤ] (periodPair O I).lattice :=
    (Submodule.equivMapOfInjective f Subtype.val_injective IZ).trans
      (LinearEquiv.ofEq _ _ hlatI)
  let carrier : Submodule ℤ (periodPair O I).lattice :=
    (productSubmodule O a I).map e.toLinearMap
  have hindex : carrier.toAddSubgroup.index = ((⟨idealNorm O a, hpos⟩ : ℕ+) : ℕ) := by
    exact (AddSubgroup.index_map_equiv (productSubmodule O a I).toAddSubgroup
      e.toAddEquiv).trans (index_productSubmodule O a ha I)
  have hcyc : IsAddCyclic ((periodPair O I).lattice ⧸ carrier) := by
    haveI : IsAddCyclic (IZ ⧸ productSubmodule O a I) :=
      (quotient_isAddCyclic_iff O a ha I).mpr hprim
    let q := Submodule.Quotient.equiv (productSubmodule O a I) carrier e rfl
    exact isAddCyclic_of_surjective q q.surjective
  refine ⟨⟨carrier, hindex, hcyc⟩, ?_⟩
  have hlat : (⟨carrier, hindex, hcyc⟩ : PeriodPair.CyclicSublattice (periodPair O I)
      ⟨idealNorm O a, hpos⟩).toPeriodPair.lattice =
      complexLattice O ((integralIdealUnit O a ha * I : (FractionalIdeal O⁰ K)ˣ) :
        FractionalIdeal O⁰ K) := by
    refine (PeriodPair.CyclicSublattice.toPeriodPair_lattice
      (m := (⟨idealNorm O a, hpos⟩ : ℕ+)) ⟨carrier, hindex, hcyc⟩).trans ?_
    change carrier.map (periodPair O I).lattice.subtype = _
    rw [Units.val_mul, coe_integralIdealUnit, complexLattice, ← map_subtype_productSubmodule]
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨(z : K), ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨e z, ⟨z, hz, rfl⟩, rfl⟩
  exact (idealJ_eq_of_lattice_eq O _ _ hlat).symm

include hIQ in
/-- Cox, Corollary 11.27, p. 237, the principal cyclic sublattice. -/
theorem exists_principal_cyclicSublattice (α : O) (hα : α ≠ 0)
    (hprim : IsPrimitiveElement O α) (I : (FractionalIdeal O⁰ K)ˣ)
    (hpos : 0 < elementNorm O α) :
    ∃ S : PeriodPair.CyclicSublattice (periodPair O I) ⟨elementNorm O α, hpos⟩,
      S.j = idealJ O I := by
  have hαK : (α : K) ≠ 0 := fun h => hα (Subtype.ext h)
  have hunit : IsUnit ((Ideal.span {α} : Ideal O) : FractionalIdeal O⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton]
    exact ⟨toPrincipalIdeal O K (Units.mk0 _ hαK), coe_toPrincipalIdeal _⟩
  have hN : idealNorm O (Ideal.span {α}) = elementNorm O α := idealNorm_span_singleton O α
  obtain ⟨S, hS⟩ := exists_cyclicSublattice O (Ideal.span {α}) hunit
    ((isPrimitiveIdeal_span_singleton_iff O α hα).mpr hprim) I (hN ▸ hpos)
  let S' : PeriodPair.CyclicSublattice (periodPair O I) ⟨elementNorm O α, hpos⟩ :=
    ⟨S.carrier, S.index_eq.trans hN, S.cyclic⟩
  have hunitEq : integralIdealUnit O (Ideal.span {α}) hunit =
      toPrincipalIdeal O K (Units.mk0 _ hαK) := by
    ext1
    rw [coe_integralIdealUnit, FractionalIdeal.coeIdeal_span_singleton, coe_toPrincipalIdeal]
    rfl
  refine ⟨S', ?_⟩
  have hj : S'.j = S.j := PeriodPair.j_congr
    ((PeriodPair.CyclicSublattice.toPeriodPair_lattice S').trans
      (PeriodPair.CyclicSublattice.toPeriodPair_lattice S).symm)
  rw [hj, hS, hunitEq, mul_comm, idealJ_mul_principal]

omit hNF in
/-- Cox, Exercise 7.2, p. 133: the inclusion preserves the underlying field element. -/
theorem toRingOfIntegers_coe (x : O) : (toRingOfIntegers O x : K) = (x : K) :=
  rfl

include hIQ in
/-- Cox, imaginary quadratic discriminant, pp. 103 and 134. -/
theorem discr_neg : NumberField.discr K < 0 := by
  sorry

/-- The second basis element `f w_K` of an order; Cox, Lemma 7.2, p. 133. -/
def conductorGenerator : O :=
  ⟨(conductor O : K) * (integerGenerator O : K), conductor_mul_mem O (integerGenerator O)⟩

include hIQ in
/-- Cox, Lemma 7.2, p. 133, the field value of the second order generator. -/
theorem conductorGenerator_coe :
    (conductorGenerator O : K) = (conductor O : K) * (integerGenerator O : K) := by
  sorry

include hIQ in
/-- Cox, Lemma 7.2, p. 133, the basis of the order. -/
theorem conductorGenerator_span :
    Submodule.span ℤ ({1, conductorGenerator O} : Set O) = ⊤ := by
  sorry

include hIQ in
/-- Cox, Lemma 7.2, p. 133, linear independence of the integral order basis. -/
theorem conductorGenerator_linearIndependent :
    LinearIndependent ℤ ![1, conductorGenerator O] := by
  sorry

include hIQ in
/-- Cox, Exercise 11.20, p. 248, the primitive second basis element. -/
theorem conductorGenerator_isPrimitive : IsPrimitiveElement O (conductorGenerator O) := by
  sorry

include hIQ in
/-- Cox, Exercise 11.20, p. 248, the norm computation for `f w_K`. -/
theorem elementNorm_conductorGenerator :
    (elementNorm O (conductorGenerator O) : ℚ) =
      (conductor O : ℚ) ^ 2 * NumberField.discr K * (NumberField.discr K - 1) / 4 := by
  sorry

omit hNF hO in
/-- Cox, Exercise 11.20, p. 248, the consecutive-square obstruction over the rationals. -/
theorem not_isSquare_rat_mul_succ (t : ℕ) (ht : 0 < t) :
    ¬ IsSquare ((t : ℚ) * (t + 1)) := by
  sorry

include hIQ in
/-- Cox, Exercise 11.20, p. 248, positivity of the chosen norm. -/
theorem elementNorm_conductorGenerator_pos : 0 < elementNorm O (conductorGenerator O) := by
  sorry

include hIQ in
/-- Cox, Exercise 11.20, p. 248, the nonsquare norm of the chosen element. -/
theorem elementNorm_conductorGenerator_not_isSquare :
    ¬ IsSquare (elementNorm O (conductorGenerator O)) := by
  sorry

include hIQ in
/-- Cox, Theorem 11.1, p. 237, the diagonal modular-polynomial root from a principal sublattice. -/
theorem exists_nonsquare_diagonal_root (I : (FractionalIdeal O⁰ K)ˣ) :
    ∃ m : ℕ+, ¬ IsSquare (m : ℕ) ∧
      (modularPolynomialDiagonal m).eval₂ (Int.castRingHom ℂ) (idealJ O I) = 0 := by
  sorry

/-- Extension of an order ideal to the maximal order; Cox, Proposition 7.20, pp. 144–145. -/
def extendIdeal (a : Ideal O) : Ideal (𝓞 K) := a.map (toRingOfIntegers O)

/-- Contraction from the maximal order; Cox, Proposition 7.20, pp. 144–145. -/
def contractIdeal (a : Ideal (𝓞 K)) : Ideal O := a.comap (toRingOfIntegers O)

/-- Coprimality with the conductor in the norm formulation; Cox, Lemma 7.18, p. 143. -/
def IsPrimeToConductor (a : Ideal O) : Prop := (idealNorm O a).Coprime (conductor O)

/-- Cox, Lemma 7.18, p. 143: norm coprimality is equivalent to the ideal-sum condition. -/
theorem isPrimeToConductor_iff_sup (a : Ideal O) (ha : a ≠ ⊥) :
    IsPrimeToConductor O a ↔ a ⊔ Ideal.span {(conductor O : O)} = ⊤ := by
  haveI : Finite (O ⧸ a) := Nat.finite_of_card_ne_zero (idealNorm_pos O a ha).ne'
  rw [OrderCoprimality.sup_span_natCast_eq_top_iff_coprime_card]
  rfl

omit hNF in
/-- Cox, Proposition 7.20(i), p. 144, preservation of norm under contraction. -/
theorem idealNorm_contract (a : Ideal (𝓞 K))
    (ha : (Nat.card ((𝓞 K) ⧸ a)).Coprime (conductor O)) :
    idealNorm O (contractIdeal O a) = Nat.card ((𝓞 K) ⧸ a) := by
  let φ := Ideal.quotientMap a (toRingOfIntegers O) (le_refl (contractIdeal O a))
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨s, hs⟩ : ∃ s : 𝓞 K, Ideal.Quotient.mk a ((conductor O : 𝓞 K) * s) =
        Ideal.Quotient.mk a z := by
      rcases Nat.eq_zero_or_pos (Nat.card ((𝓞 K) ⧸ a)) with h0 | hpos
      · rw [h0, Nat.coprime_zero_left] at ha
        exact ⟨z, by rw [ha, Nat.cast_one, one_mul]⟩
      · haveI : Finite ((𝓞 K) ⧸ a) := Nat.finite_of_card_ne_zero hpos.ne'
        obtain ⟨t, ht⟩ := ((OrderCoprimality.bijective_nsmul_iff_coprime_card _).mpr ha).2
          (Ideal.Quotient.mk a z)
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
        dsimp only at ht
        refine ⟨s, ?_⟩
        rw [← ht, map_mul, map_natCast, nsmul_eq_mul]
    refine ⟨Ideal.Quotient.mk _ ⟨(conductor O : K) * (s : K), conductor_mul_mem O s⟩, ?_⟩
    exact (Ideal.quotientMap_mk (I := a) (f := toRingOfIntegers O)
      (H := le_refl (contractIdeal O a))).trans hs
  exact Nat.card_congr (Equiv.ofBijective φ ⟨Ideal.quotientMap_injective, hsurj⟩)

omit hNF in
/-- Cox, Proposition 7.20(i), p. 144, preservation of conductor coprimality. -/
theorem isPrimeToConductor_contract (a : Ideal (𝓞 K))
    (ha : (Nat.card ((𝓞 K) ⧸ a)).Coprime (conductor O)) :
    IsPrimeToConductor O (contractIdeal O a) := by
  rw [IsPrimeToConductor, idealNorm_contract O a ha]
  exact ha

/-- Cox, equation (7.21), pp. 144–145, extension followed by contraction. -/
theorem contract_extend (a : Ideal O) (ha : IsPrimeToConductor O a) :
    contractIdeal O (extendIdeal O a) = a := by
  rcases eq_or_ne a ⊥ with rfl | hne
  · rw [extendIdeal, Ideal.map_bot, contractIdeal, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (toRingOfIntegers_injective O)]
  refine le_antisymm ?_ Ideal.le_comap_map
  intro x hx
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp
    (((isPrimeToConductor_iff_sup O a hne).mp ha).symm ▸ Submodule.mem_top : (1 : O) ∈ _)
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hw
  have hkey : ∀ z ∈ Submodule.span (𝓞 K) ((toRingOfIntegers O) '' a), ∀ r : 𝓞 K,
      ∃ y ∈ a, toRingOfIntegers O y = (conductor O : 𝓞 K) * r * z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      intro r
      refine ⟨⟨(conductor O : K) * r, conductor_mul_mem O r⟩ * y, a.mul_mem_left _ hy, ?_⟩
      rw [map_mul]
      rfl
    | zero => exact fun r => ⟨0, a.zero_mem, by simp⟩
    | add z₁ z₂ _ _ h₁ h₂ =>
      intro r
      obtain ⟨y₁, hy₁, e₁⟩ := h₁ r
      obtain ⟨y₂, hy₂, e₂⟩ := h₂ r
      exact ⟨y₁ + y₂, a.add_mem hy₁ hy₂, by rw [map_add, e₁, e₂]; ring⟩
    | smul s z _ h =>
      intro r
      obtain ⟨y, hy, e⟩ := h (r * s)
      exact ⟨y, hy, by rw [e, smul_eq_mul]; ring⟩
  obtain ⟨y, hy, hyx⟩ := hkey _ hx 1
  have hyx' : y = (conductor O : O) * x :=
    toRingOfIntegers_injective O (by rw [hyx, map_mul, map_natCast, mul_one])
  have hx_eq : x = x * u + v * y := by
    rw [hyx']
    linear_combination (-x) * huw
  rw [hx_eq]
  exact a.add_mem (a.mul_mem_left x hu) (a.mul_mem_left v hy)

/-- Cox, equation (7.21), pp. 144–145, contraction followed by extension. -/
theorem extend_contract (a : Ideal (𝓞 K))
    (ha : (Nat.card ((𝓞 K) ⧸ a)).Coprime (conductor O)) :
    extendIdeal O (contractIdeal O a) = a := by
  have hfK : (conductor O : K) ≠ 0 := Nat.cast_ne_zero.mpr (conductor_pos O).ne'
  refine le_antisymm Ideal.map_comap_le fun y hy => ?_
  let fy : O := ⟨(conductor O : K) * y, conductor_mul_mem O y⟩
  have hfy : toRingOfIntegers O fy = (conductor O : 𝓞 K) * y := by
    apply NumberField.RingOfIntegers.ext
    rw [toRingOfIntegers_coe]
    change (conductor O : K) * (y : K) =
      (algebraMap (𝓞 K) K) ((conductor O : 𝓞 K) * y)
    simp only [map_mul, map_natCast]
  have hfy_mem : fy ∈ contractIdeal O a := by
    change toRingOfIntegers O fy ∈ a
    rw [hfy]
    exact a.mul_mem_left _ hy
  rcases eq_or_ne (contractIdeal O a) ⊥ with h0 | hne
  · rw [h0, Ideal.mem_bot] at hfy_mem
    have h1 : (conductor O : K) * (y : K) = 0 := congrArg Subtype.val hfy_mem
    have hy0 : y = 0 := NumberField.RingOfIntegers.ext (by
      simpa using (mul_eq_zero.mp h1).resolve_left hfK)
    rw [hy0]
    exact zero_mem _
  · obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp
      (((isPrimeToConductor_iff_sup O _ hne).mp (isPrimeToConductor_contract O a ha)).symm ▸
        Submodule.mem_top : (1 : O) ∈ _)
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    have h1 := congrArg (toRingOfIntegers O) huw
    rw [map_add, map_mul, map_natCast, map_one] at h1
    have hy_eq : y = y * toRingOfIntegers O u + toRingOfIntegers O v * toRingOfIntegers O fy := by
      rw [hfy]
      linear_combination (-y) * h1
    rw [hy_eq]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ y (Ideal.mem_map_of_mem _ hu))
      (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hfy_mem))

/-- Cox, Proposition 7.20(ii), pp. 144–145, preservation of norm under extension. -/
theorem idealNorm_extend (a : Ideal O) (ha : IsPrimeToConductor O a) :
    Nat.card ((𝓞 K) ⧸ extendIdeal O a) = idealNorm O a := by
  rcases eq_or_ne a ⊥ with rfl | hne
  · haveI : Infinite O := Infinite.of_injective (fun n : ℕ => (n : O)) fun m n h => by
      have h' := congrArg (fun y : O => (y : K)) h
      simpa using h'
    haveI : Infinite (𝓞 K) := Infinite.of_injective (fun n : ℕ => (n : 𝓞 K)) fun m n h => by
      have h' := congrArg (fun y : 𝓞 K => (y : K)) h
      simpa using h'
    rw [extendIdeal, Ideal.map_bot, idealNorm,
      Nat.card_congr (RingEquiv.quotientBot (𝓞 K)).toEquiv,
      Nat.card_congr (RingEquiv.quotientBot O).toEquiv, Nat.card_eq_zero_of_infinite,
      Nat.card_eq_zero_of_infinite]
  have hsup' : extendIdeal O a ⊔ Ideal.span {((conductor O : ℕ) : 𝓞 K)} = ⊤ := by
    have h := congrArg (Ideal.map (toRingOfIntegers O)) ((isPrimeToConductor_iff_sup O a hne).mp ha)
    rwa [Ideal.map_sup, Ideal.map_top, Ideal.map_span, Set.image_singleton, map_natCast] at h
  have hext : extendIdeal O a ≠ ⊥ := by
    rw [extendIdeal, Ne, Ideal.map_eq_bot_iff_of_injective (toRingOfIntegers_injective O)]
    exact hne
  haveI : Finite ((𝓞 K) ⧸ extendIdeal O a) := Ideal.finiteQuotientOfFreeOfNeBot _ hext
  have hcop := (OrderCoprimality.sup_span_natCast_eq_top_iff_coprime_card _ _).mp hsup'
  rw [← idealNorm_contract O _ hcop, contract_extend O a ha]

include hIQ in
/-- Cox, Lemma 7.18, p. 143: ideals prime to the conductor are proper. -/
theorem isUnit_of_isPrimeToConductor (a : Ideal O) (ha : IsPrimeToConductor O a)
    (hne : a ≠ ⊥) : IsUnit (a : FractionalIdeal O⁰ K) := by
  apply isUnit_of_isProper O
  refine ⟨FractionalIdeal.coeIdeal_ne_zero.mpr hne, fun x => ⟨fun hx => ?_, fun hx y hy => ?_⟩⟩
  · let N : Submodule ℤ K := ((a : FractionalIdeal O⁰ K) : Submodule O K).restrictScalars ℤ
    have hNfg : N.FG := Module.Finite.iff_fg.mp (fractionalIdeal_moduleFinite O _)
    have hN0 : N ≠ ⊥ := by
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      refine (Submodule.ne_bot_iff N).mpr ⟨(u : K), ?_, fun h => hu0 (Subtype.ext h)⟩
      exact (FractionalIdeal.mem_coeIdeal O⁰).mpr ⟨u, hu, rfl⟩
    have hint : IsIntegral ℤ x :=
      isIntegral_of_smul_mem_submodule (A := K) (M := K) N hN0 hNfg x fun n hn => hx n hn
    have hfx : (conductor O : K) * x ∈ O := conductor_mul_mem O ⟨x, hint⟩
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp
      (((isPrimeToConductor_iff_sup O a hne).mp ha).symm ▸ Submodule.mem_top : (1 : O) ∈ _)
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    have hxu : x * (u : K) ∈ O :=
      mem_of_mem_coeIdeal O a (hx _ ((FractionalIdeal.mem_coeIdeal O⁰).mpr ⟨u, hu, rfl⟩))
    have h1 : (u : K) + (v : K) * (conductor O : K) = 1 := by
      have := congrArg (fun z : O => (z : K)) huw
      simpa using this
    have hx_eq : x = x * (u : K) + (conductor O : K) * x * (v : K) := by
      linear_combination (-x) * h1
    rw [hx_eq]
    exact O.add_mem hxu (O.mul_mem hfx v.2)
  · simpa [Algebra.smul_def, Subalgebra.algebraMap_eq] using
      Submodule.smul_mem ((a : FractionalIdeal O⁰ K) : Submodule O K) (⟨x, hx⟩ : O) hy

end RemainingOrderContext

end Order

end Cox
