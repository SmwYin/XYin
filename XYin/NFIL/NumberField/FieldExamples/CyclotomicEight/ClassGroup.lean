/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.CyclotomicEight.PrimeSplitting

/-!
# `ℚ(ζ₈)` ClassGroup

Fractional ideals, ideal representatives, class number, PID/UFD consequences, and class group
structure.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Fractional Ideals
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

namespace NumberField.CyclotomicEight

abbrev zetaFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton (𝓞 K)⁰ ζ

abbrev ramifiedPrimeFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  (Ideal.span {1 - zetaInt} : FractionalIdeal (𝓞 K)⁰ K)

theorem zeta_mem_fractionalIdeal :
    ζ ∈ zetaFractionalIdeal := by
  exact FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ ζ

theorem zetaFractionalIdeal_absNorm :
    FractionalIdeal.absNorm zetaFractionalIdeal = |Algebra.norm ℚ ζ| := by
  rw [zetaFractionalIdeal, FractionalIdeal.absNorm_span_singleton]

theorem ramifiedPrimeFractionalIdeal_ne_zero :
    ramifiedPrimeFractionalIdeal ≠ 0 := by
  exact FractionalIdeal.coeIdeal_ne_zero.mpr (by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    intro h
    have hK : (1 : K) - ζ = 0 := by
      have hmap := congrArg (algebraMap (𝓞 K) K) h
      simpa [zetaInt] using hmap
    have hζ : ζ = 1 := by linear_combination -hK
    have horder : orderOf ζ = 1 := by simp [hζ]
    have horder8 : orderOf ζ = 8 := zeta_isPrimitiveRoot.eq_orderOf.symm
    omega)

end NumberField.CyclotomicEight


/-!
## Class Group
-/

noncomputable section

open Module
open scoped NumberField nonZeroDivisors

namespace NumberField.CyclotomicEight

private theorem gen_eq_zetaInt : zeta_isPrimitiveRoot.integralPowerBasis.gen = zetaInt := by
  rw [zeta_isPrimitiveRoot.integralPowerBasis_gen]
  rfl

private theorem minpoly_gen_eq :
    minpoly ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen = Polynomial.X ^ 4 + 1 := by
  have hint : IsIntegral ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen :=
    zeta_isPrimitiveRoot.integralPowerBasis.isIntegral_gen
  have hdvd : minpoly ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen ∣ Polynomial.X ^ 4 + 1 :=
    minpoly.isIntegrallyClosed_dvd hint (by rw [gen_eq_zetaInt]; simp [zetaInt_pow_four])
  have hmonic := minpoly.monic hint
  have hdeg : (minpoly ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen).natDegree = 4 := by
    rw [zeta_isPrimitiveRoot.integralPowerBasis.natDegree_minpoly,
      zeta_isPrimitiveRoot.integralPowerBasis_dim]
    rfl
  have hXmonic : (Polynomial.X ^ 4 + 1 : Polynomial ℤ).Monic := by
    rw [show (1 : Polynomial ℤ) = Polynomial.C 1 from Polynomial.C_1.symm]
    exact Polynomial.monic_X_pow_add_C 1 (by norm_num)
  obtain ⟨c, hc⟩ := hdvd
  have hcmonic : c.Monic := hmonic.of_mul_monic_left (hc ▸ hXmonic)
  have hdegc : c.natDegree = 0 := by
    have h4 : (Polynomial.X ^ 4 + 1 : Polynomial ℤ).natDegree = 4 := by
      rw [show (1 : Polynomial ℤ) = Polynomial.C 1 from Polynomial.C_1.symm]
      exact Polynomial.natDegree_X_pow_add_C
    have hcong := congrArg Polynomial.natDegree hc
    rw [h4, Polynomial.natDegree_mul (minpoly.ne_zero hint) hcmonic.ne_zero, hdeg] at hcong
    omega
  rw [hc, Polynomial.eq_one_of_monic_natDegree_zero hcmonic hdegc, mul_one]

private noncomputable def residueHom (p : ℕ) (r : ℤ) (hr : ((r : ZMod p)) ^ 4 = -1) :
    𝓞 K →ₐ[ℤ] ZMod p :=
  zeta_isPrimitiveRoot.integralPowerBasis.lift ((r : ℤ) : ZMod p)
    (by rw [minpoly_gen_eq]; simp [hr])

private theorem residueHom_zetaInt (p : ℕ) (r : ℤ) (hr : ((r : ZMod p)) ^ 4 = -1) :
    residueHom p r hr zetaInt = (r : ZMod p) := by
  rw [← gen_eq_zetaInt]
  exact zeta_isPrimitiveRoot.integralPowerBasis.lift_gen ((r : ℤ) : ZMod p)
    (by rw [minpoly_gen_eq]; simp [hr])

private theorem ker_residueHom (p : ℕ) (r : ℤ) (hr : ((r : ZMod p)) ^ 4 = -1) :
    RingHom.ker (residueHom p r hr).toRingHom =
      Ideal.span {(p : 𝓞 K), zetaInt - (r : 𝓞 K)} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [RingHom.mem_ker] at hx
    obtain ⟨q, -, hq⟩ := zeta_isPrimitiveRoot.integralPowerBasis.exists_eq_aeval x
    rw [gen_eq_zetaInt] at hq
    have key : x - ((q.eval r : ℤ) : 𝓞 K) ∈ Ideal.span {zetaInt - (r : 𝓞 K)} := by
      rw [Ideal.mem_span_singleton, hq]
      have hdvd := Polynomial.sub_dvd_eval_sub zetaInt ((r : ℤ) : 𝓞 K)
        (q.map (algebraMap ℤ (𝓞 K)))
      have e1 : (q.map (algebraMap ℤ (𝓞 K))).eval zetaInt = Polynomial.aeval zetaInt q := by
        rw [Polynomial.eval_map, ← Polynomial.aeval_def]
      have e2 : (q.map (algebraMap ℤ (𝓞 K))).eval ((r : ℤ) : 𝓞 K) = ((q.eval r : ℤ) : 𝓞 K) := by
        have hcast : ((r : ℤ) : 𝓞 K) = algebraMap ℤ (𝓞 K) r := by
          simp [algebraMap_int_eq]
        rw [Polynomial.eval_map, hcast, Polynomial.eval₂_at_apply]
        simp [algebraMap_int_eq]
      rw [e1, e2] at hdvd
      exact hdvd
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp key
    have hphi : ((q.eval r : ℤ) : ZMod p) = 0 := by
      have h1 : residueHom p r hr (x - ((q.eval r : ℤ) : 𝓞 K)) = 0 := by
        rw [hd, map_mul, map_sub, residueHom_zetaInt, map_intCast, sub_self, zero_mul]
      rw [map_sub, map_intCast, show residueHom p r hr x = 0 from hx, zero_sub,
        neg_eq_zero] at h1
      exact h1
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hphi
    have hx_eq : x = (zetaInt - (r : 𝓞 K)) * d + (p : 𝓞 K) * ((m : ℤ) : 𝓞 K) := by
      have h2 : x = (zetaInt - (r : 𝓞 K)) * d + ((q.eval r : ℤ) : 𝓞 K) := by
        rw [← hd]
        ring
      rw [h2, hm]
      push_cast
      ring
    rw [hx_eq]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
    · simp
    · simp
  · rw [Ideal.span_le]
    rintro y (rfl | rfl)
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      simp
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      have h0 : (residueHom p r hr) (zetaInt - (r : 𝓞 K)) = 0 := by
        rw [map_sub, residueHom_zetaInt, map_intCast, sub_self]
      exact h0

private theorem residueHom_surjective (p : ℕ) (r : ℤ) (hr : ((r : ZMod p)) ^ 4 = -1) :
    Function.Surjective (residueHom p r hr) := by
  intro z
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective z
  exact ⟨((m : ℤ) : 𝓞 K), by rw [map_intCast]; exact hm⟩

private theorem isMaximal_span_pair (p : ℕ) [Fact p.Prime] (r : ℤ)
    (hr : ((r : ZMod p)) ^ 4 = -1) :
    (Ideal.span {(p : 𝓞 K), zetaInt - (r : 𝓞 K)}).IsMaximal := by
  rw [← ker_residueHom p r hr]
  exact RingHom.ker_isMaximal_of_surjective _ (residueHom_surjective p r hr)

private theorem span_one_sub_zetaInt_eq_pair :
    Ideal.span {1 - zetaInt} = Ideal.span {((2 : ℕ) : 𝓞 K), zetaInt - ((1 : ℤ) : 𝓞 K)} := by
  refine le_antisymm ((Ideal.span_singleton_le_iff_mem _).mpr ?_) (Ideal.span_le.mpr ?_)
  · refine Ideal.mem_span_pair.mpr ⟨0, -1, ?_⟩
    push_cast
    ring
  · rintro y (rfl | rfl)
    · have h2 : ((2 : ℕ) : 𝓞 K) ∈ Ideal.span {(2 : 𝓞 K)} := by
        rw [Ideal.mem_span_singleton]
        exact ⟨1, by push_cast; ring⟩
      rw [span_two_eq] at h2
      exact Ideal.pow_le_self (by norm_num) h2
    · rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      exact ⟨-1, by push_cast; ring⟩

/-- The class number of `ℚ(ζ₈)` is `1` (the Minkowski bound is `(4/π)² · 4!/4⁴ · √256 ≈ 2.4`,
and the only prime below it, `2`, is principal: `(2) = (1 - ζ)⁴` with `(1 - ζ)` principal). -/
private theorem eq_span_one_sub_of_two_mem (P : Ideal (𝓞 K)) (hP : P.IsPrime)
    (h2 : (2 : 𝓞 K) ∈ P) : P = Ideal.span {1 - zetaInt} := by
  have hle : Ideal.span {(2 : 𝓞 K)} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr h2
  have h4 : (1 - zetaInt) ^ 4 ∈ P := by
    apply hle
    rw [span_two_eq, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have h1 : 1 - zetaInt ∈ P := hP.mem_of_pow_mem 4 h4
  have hmax : (Ideal.span {1 - zetaInt}).IsMaximal := by
    rw [span_one_sub_zetaInt_eq_pair]
    exact isMaximal_span_pair 2 1 (by decide)
  exact (hmax.eq_of_le hP.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr h1)).symm

theorem classNumber_eq_one : NumberField.classNumber K = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hp hprime P hPmem _
  have hPprime : P.IsPrime := hPmem.1
  have hpmem : ((p : ℕ) : 𝓞 K) ∈ P := by
    have hover := hPmem.2.over
    have hmem : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
      rw [← hover]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.under, Ideal.mem_comap] at hmem
    simpa [algebraMap_int_eq] using hmem
  have hple : p ≤ 2 := by
    have h2 := (Finset.mem_Icc.mp hp).2
    have h5 : ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        (((Module.finrank ℚ K).factorial : ℝ) /
          ((Module.finrank ℚ K : ℝ)) ^ (Module.finrank ℚ K) *
            Real.sqrt (|NumberField.discr K| : ℝ))⌋₊ < 3 := by
      rw [Nat.floor_lt (by positivity)]
      rw [nrComplexPlaces_eq_two, degree_eq_four, numberField_discr_eq]
      have h16 : Real.sqrt |((256 : ℤ) : ℝ)| = 16 := by
        rw [show |((256 : ℤ) : ℝ)| = (16 : ℝ) ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [h16]
      have hx : (4 / Real.pi) ^ 2 * (((Nat.factorial 4 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) ^ (4 : ℕ) * 16) =
          24 / Real.pi ^ 2 := by
        norm_num [Nat.factorial]
        ring
      rw [hx, div_lt_iff₀ (by positivity)]
      have hπ : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
      push_cast
      nlinarith [sq_nonneg (Real.pi - 3.14)]
    omega
  have hpge := (Finset.mem_Icc.mp hp).1
  interval_cases p
  · exact absurd hprime (by norm_num)
  · rw [eq_span_one_sub_of_two_mem P hPprime (by exact_mod_cast hpmem)]
    exact ⟨⟨1 - zetaInt, rfl⟩⟩

/-- The ring of integers `ℤ[ζ₈]` is a principal ideal domain. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 K) := by
  rw [← NumberField.classNumber_eq_one_iff]
  exact classNumber_eq_one

/-- The ring of integers `ℤ[ζ₈]` is a unique factorization monoid. -/
theorem uniqueFactorizationMonoid : UniqueFactorizationMonoid (𝓞 K) := by
  haveI : IsPrincipalIdealRing (𝓞 K) := isPrincipalIdealRing
  infer_instance

/-- The class group of `𝓞 K` is trivial. -/
theorem classGroupStructure : Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1)) := by
  have h1 : Nat.card (ClassGroup (𝓞 K)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 K)) := (Nat.card_eq_one_iff_unique.mp h1).1
  haveI : Unique (ClassGroup (𝓞 K)) := uniqueOfSubsingleton 1
  exact ⟨MulEquiv.ofUnique⟩

/-- The unit ideal as the concrete representative of the unique ideal class. -/
abbrev unitIdealRepresentative : (Ideal (𝓞 K))⁰ := ⟨(⊤ : Ideal (𝓞 K)), by simp⟩

/-- Every ideal class is represented by the unit ideal. -/
theorem classGroupRepresentative (C : ClassGroup (𝓞 K)) :
    C = ClassGroup.mk0 unitIdealRepresentative := by
  have h1 : Nat.card (ClassGroup (𝓞 K)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 K)) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim _ _


end NumberField.CyclotomicEight
