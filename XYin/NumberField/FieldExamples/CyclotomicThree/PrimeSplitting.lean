/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NumberField.FieldExamples.CyclotomicThree.Discriminant
import XYin.NumberField.FieldExamples.Common

/-!
# `ℚ(ζ₃)` PrimeSplitting

Prime splitting, Kummer-Dedekind computations, ramification, and different-related statements.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Prime Splitting
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial
open NumberField.FieldExamples

namespace NumberField.CyclotomicThree

section PrivateMachinery

private theorem gen_eq_zetaInt : zeta_isPrimitiveRoot.integralPowerBasis.gen = zetaInt := by
  rw [zeta_isPrimitiveRoot.integralPowerBasis_gen]
  rfl

private theorem zetaInt_pow_three : zetaInt ^ 3 = 1 := by
  simpa [zetaInt] using zeta_isPrimitiveRoot.toInteger_cube_eq_one

private theorem zetaInt_relation : zetaInt ^ 2 + zetaInt + 1 = 0 := by
  ext
  simpa [zetaInt] using zeta_isPrimitiveRoot.isRoot_cyclotomic (by decide)

private noncomputable def sig2 : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 2 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private theorem sig2_zeta : sig2 ζ = ζ ^ 2 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 2 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private theorem autEq' (σ : K ≃ₐ[ℚ] K) : σ = 1 ∨ σ = sig2 := by
  have hval : ∀ t : (ZMod 3)ˣ, (t : ZMod 3).val = 1 ∨ (t : ZMod 3).val = 2 := by decide
  have hspec := IsPrimitiveRoot.autToPow_spec ℚ zeta_isPrimitiveRoot σ
  have hext : ∀ τ : K ≃ₐ[ℚ] K, σ ζ = τ ζ → σ = τ := by
    intro τ h
    have hgen := (zeta_isPrimitiveRoot.powerBasis ℚ).algHom_ext
      (f := (σ : K →ₐ[ℚ] K)) (g := (τ : K →ₐ[ℚ] K))
      (by rwa [IsPrimitiveRoot.powerBasis_gen])
    exact AlgEquiv.ext fun x => AlgHom.congr_fun hgen x
  rcases hval (IsPrimitiveRoot.autToPow ℚ zeta_isPrimitiveRoot σ) with h | h <;>
    rw [h] at hspec
  · exact Or.inl (hext 1 (by rw [← hspec, pow_one]; rfl))
  · exact Or.inr (hext sig2 (by rw [← hspec, sig2_zeta]))

private theorem prod_aut_apply (x : K) :
    ∏ σ : K ≃ₐ[ℚ] K, σ x = x * sig2 x := by
  classical
  have hne : (1 : K ≃ₐ[ℚ] K) ≠ sig2 := by
    have hid : (1 : K ≃ₐ[ℚ] K) ζ = ζ ^ 1 := by rw [pow_one]; rfl
    intro h
    exact (by norm_num : (1 : ℕ) ≠ 2)
      (zeta_isPrimitiveRoot.pow_inj (by norm_num) (by norm_num) (by rw [← hid, h, sig2_zeta]))
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, sig2} := by
    refine (Finset.eq_univ_iff_forall.mpr fun σ => ?_).symm
    rcases autEq' σ with h | h <;> simp [h]
  rw [huniv, Finset.prod_pair hne]
  rfl

private theorem minpoly_gen_eq :
    minpoly ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen =
      Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 1 := by
  set q : Polynomial ℤ := Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 1 with hq
  have hint : IsIntegral ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen :=
    zeta_isPrimitiveRoot.integralPowerBasis.isIntegral_gen
  have hdvd : minpoly ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen ∣ q := by
    refine minpoly.isIntegrallyClosed_dvd hint ?_
    rw [gen_eq_zetaInt, hq]
    simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
    exact zetaInt_relation
  have hmonic := minpoly.monic hint
  have hdeg : (minpoly ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen).natDegree = 2 := by
    rw [zeta_isPrimitiveRoot.integralPowerBasis.natDegree_minpoly,
      zeta_isPrimitiveRoot.integralPowerBasis_dim]
    rfl
  have hqmonic : q.Monic := by
    rw [hq]
    monicity!
  obtain ⟨c, hc⟩ := hdvd
  have hcmonic : c.Monic := hmonic.of_mul_monic_left (hc ▸ hqmonic)
  have hdegc : c.natDegree = 0 := by
    have h2 : q.natDegree = 2 := by
      rw [hq]
      compute_degree!
    have hcong := congrArg Polynomial.natDegree hc
    rw [h2, Polynomial.natDegree_mul (minpoly.ne_zero hint) hcmonic.ne_zero, hdeg] at hcong
    omega
  rw [hc, Polynomial.eq_one_of_monic_natDegree_zero hcmonic hdegc, mul_one]

private theorem isMaximal_span_pair (p : ℕ) [Fact p.Prime] (r : ℤ)
    (hr : ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    (Ideal.span {(p : 𝓞 K), zetaInt - (r : 𝓞 K)}).IsMaximal := by
  rw [← gen_eq_zetaInt]
  exact NumberField.FieldExamples.isMaximal_span_gen_sub
    zeta_isPrimitiveRoot.integralPowerBasis p r
    (by rw [minpoly_gen_eq]; simp only [map_add, map_pow, Polynomial.aeval_X, map_one]; exact hr)

private theorem absNorm_span_pair (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K), zetaInt - (r : 𝓞 K)}) = p := by
  rw [← gen_eq_zetaInt]
  exact NumberField.FieldExamples.absNorm_span_gen_sub
    zeta_isPrimitiveRoot.integralPowerBasis p r
    (by rw [minpoly_gen_eq]; simp only [map_add, map_pow, Polynomial.aeval_X, map_one]; exact hr)
end PrivateMachinery

/-- The norm form of `ℚ(ζ₃)` in the basis `1, ζ`: the field norm of `x + yζ` is the binary
quadratic form `x² - xy + y²`, the principal form of discriminant `-3`. -/
theorem norm_eq_normForm (x y : ℚ) :
    Algebra.norm ℚ (x • (1 : K) + y • ζ) = x ^ 2 - x * y + y ^ 2 := by
  haveI := IsCyclotomicExtension.isGalois {3} ℚ K
  apply (algebraMap ℚ K).injective
  rw [Algebra.norm_eq_prod_automorphisms, prod_aut_apply]
  simp [Algebra.smul_def, sig2_zeta]
  have hζ : ζ ^ 2 + ζ + 1 = 0 := by
    simpa using zeta_isPrimitiveRoot.isRoot_cyclotomic (by decide)
  linear_combination (x * y) * hζ + y ^ 2 * zeta_pow_three

/-- The integral norm form: on `𝓞 K = ℤ[ζ]` the norm of `x + yζ` (with `x, y ∈ ℤ`) is
`x² - xy + y²`. -/
theorem intNorm_eq_normForm (x y : ℤ) :
    Algebra.norm ℤ (x • (1 : 𝓞 K) + y • zetaInt) = x ^ 2 - x * y + y ^ 2 := by
  have h1 : ((Algebra.norm ℤ (x • (1 : 𝓞 K) + y • zetaInt) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap (𝓞 K) K (x • (1 : 𝓞 K) + y • zetaInt)) :=
    Algebra.coe_norm_int _
  have h2 : algebraMap (𝓞 K) K (x • (1 : 𝓞 K) + y • zetaInt) =
      (x : ℚ) • (1 : K) + (y : ℚ) • ζ := by
    rw [map_add, map_zsmul, map_zsmul, map_one]
    simp [zetaInt, Algebra.smul_def]
  rw [h2, norm_eq_normForm] at h1
  exact_mod_cast h1

/-- The unit equation of `ℚ(ζ₃)`: `x + yζ` is a unit of `ℤ[ζ]` iff `x² - xy + y² = 1`.
The six integer solutions correspond to the six roots of unity `±1, ±ζ, ±ζ²`. -/
theorem isUnit_iff_normForm (x y : ℤ) :
    IsUnit (x • (1 : 𝓞 K) + y • zetaInt) ↔ x ^ 2 - x * y + y ^ 2 = 1 := by
  rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm, ← Algebra.coe_norm_int,
    intNorm_eq_normForm, abs_eq (by norm_num : (0 : ℚ) ≤ 1)]
  constructor
  · rintro (h | h)
    · exact_mod_cast h
    · have hq : x ^ 2 - x * y + y ^ 2 = (-1 : ℤ) := by exact_mod_cast h
      have hnonneg : (0 : ℤ) ≤ x ^ 2 - x * y + y ^ 2 := by
        nlinarith [sq_nonneg (2 * x - y), sq_nonneg y]
      omega
  · intro h
    left
    exact_mod_cast h

/-- The norm of `1 - ζ` is `3`, the rational prime ramified in `ℚ(ζ₃)`. -/
theorem norm_one_sub_zeta : Algebra.norm ℚ (1 - ζ) = 3 := by
  have h := norm_eq_normForm (1 : ℚ) (-1 : ℚ)
  norm_num at h
  simpa [sub_eq_add_neg] using h

/-- The norm of `1 + ζ` is `1`, so `1 + ζ` is another cyclotomic unit. -/
theorem norm_one_add_zeta : Algebra.norm ℚ (1 + ζ) = 1 := by
  have h := norm_eq_normForm (1 : ℚ) (1 : ℚ)
  norm_num at h
  simpa using h
/-- The element `ζ - 1` is a prime element of the ring of integers. -/
theorem zetaInt_sub_one_prime : Prime (zetaInt - 1 : 𝓞 K) := by
  rw [zetaInt]
  exact zeta_isPrimitiveRoot.zeta_sub_one_prime'

/-- In this field, `ζ - 1` lies above `3`: it divides `3` in `𝓞 K`. -/
theorem zetaInt_sub_one_dvd_three : (zetaInt - 1 : 𝓞 K) ∣ (3 : 𝓞 K) := by
  rw [zetaInt]
  exact zeta_isPrimitiveRoot.toInteger_sub_one_dvd_prime'

/-- `3` is (totally) ramified: `(3) = (ζ - 1)²` as ideals of `𝓞 K`. It is the unique
ramified prime, matching the discriminant `-3`. -/
theorem span_three_eq :
    Ideal.span {(3 : 𝓞 K)} = Ideal.span {zetaInt - 1} ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
  refine ⟨⟨-zetaInt, -zetaInt ^ 2, ?_, ?_⟩, ?_⟩
  · linear_combination zetaInt_pow_three
  · linear_combination zetaInt_pow_three
  · change (3 : 𝓞 K) * (-zetaInt) = (zetaInt - 1) ^ 2
    linear_combination -zetaInt_relation

private theorem span_zetaInt_sub_one_eq_pair :
    Ideal.span {zetaInt - 1} = Ideal.span {((3 : ℕ) : 𝓞 K), zetaInt - ((1 : ℤ) : 𝓞 K)} := by
  refine le_antisymm ((Ideal.span_singleton_le_iff_mem _).mpr ?_) (Ideal.span_le.mpr ?_)
  · exact Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩
  · rintro y (rfl | rfl)
    · have h3 : ((3 : ℕ) : 𝓞 K) ∈ Ideal.span {(3 : 𝓞 K)} := by
        rw [Ideal.mem_span_singleton]
        exact ⟨1, by push_cast; ring⟩
      rw [span_three_eq] at h3
      exact Ideal.pow_le_self (by norm_num) h3
    · exact Ideal.mem_span_singleton_self _

/-- The prime `(ζ - 1)` above `3` has norm `3` (residue degree `f = 1`). -/
theorem absNorm_span_zetaInt_sub_one :
    Ideal.absNorm (Ideal.span {zetaInt - 1}) = 3 := by
  have hr : ((1 : ℤ) : ZMod 3) ^ 2 + ((1 : ℤ) : ZMod 3) + 1 = 0 := by decide
  rw [span_zetaInt_sub_one_eq_pair]
  exact absNorm_span_pair 3 1 hr

/-- `(ζ - 1)` is a prime ideal — the unique prime of `𝓞 K` above `3`. -/
theorem isPrime_span_zetaInt_sub_one : (Ideal.span {zetaInt - 1}).IsPrime := by
  have hr : ((1 : ℤ) : ZMod 3) ^ 2 + ((1 : ℤ) : ZMod 3) + 1 = 0 := by decide
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [span_zetaInt_sub_one_eq_pair]
  exact (isMaximal_span_pair 3 1 hr).isPrime

/-- The ramified prime `(ζ - 1)` lies over `(3)`. -/
theorem liesOver_span_zetaInt_sub_one :
    (Ideal.span {zetaInt - 1}).LiesOver (Ideal.span {(3 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_zetaInt_sub_one.ne_top
    (show Prime (3 : ℤ) by norm_num)]
  change (3 : 𝓞 K) ∈ Ideal.span {zetaInt - 1}
  have hmem : (3 : 𝓞 K) ∈ Ideal.span {(3 : 𝓞 K)} := Ideal.mem_span_singleton_self _
  rw [span_three_eq] at hmem
  exact Ideal.pow_le_self (by norm_num) hmem

/-- The ramified prime `(ζ - 1)` has inertia degree `1` over `3`. -/
theorem inertiaDeg_span_zetaInt_sub_one :
    (Ideal.span {(3 : ℤ)}).inertiaDeg (Ideal.span {zetaInt - 1}) = 1 := by
  haveI : (Ideal.span {zetaInt - 1}).LiesOver (Ideal.span {(3 : ℤ)}) :=
    liesOver_span_zetaInt_sub_one
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {zetaInt - 1})
    (p := 3) Nat.prime_three
  rw [absNorm_span_zetaInt_sub_one] at h
  exact ((Nat.Prime.pow_eq_iff Nat.prime_three).mp h.symm).2

/-- The ramified prime `(ζ - 1)` has ramification index `2` over `3`. -/
theorem ramificationIdx_span_zetaInt_sub_one :
    (Ideal.span {(3 : ℤ)}).ramificationIdx (Ideal.span {zetaInt - 1}) = 2 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(3 : 𝓞 K)} ≤ Ideal.span {zetaInt - 1} ^ 2
    rw [span_three_eq]
  · intro hle3
    have hdvd : Ideal.absNorm (Ideal.span {zetaInt - 1} ^ 3) ∣
        Ideal.absNorm (Ideal.span {((3 : ℤ) : 𝓞 K)}) := by
      simpa [Ideal.map_span, Set.image_singleton] using Ideal.absNorm_dvd_absNorm_of_le hle3
    have hnorm3 : Ideal.absNorm (Ideal.span {((3 : ℤ) : 𝓞 K)}) = 9 := by
      change Ideal.absNorm (Ideal.span {(3 : 𝓞 K)}) = 9
      have hfin : Module.finrank ℤ (𝓞 K) = 2 := by
        rw [Module.finrank_eq_card_basis zetaExplicitIntegralBasis, Fintype.card_fin]
      rw [Ideal.absNorm_span_singleton,
        show (3 : 𝓞 K) = algebraMap ℤ (𝓞 K) 3 from (map_ofNat _ 3).symm,
        Algebra.norm_algebraMap, hfin]
      rfl
    have hnormP3 : Ideal.absNorm (Ideal.span {zetaInt - 1} ^ 3) = 27 := by
      rw [map_pow, absNorm_span_zetaInt_sub_one]
      norm_num
    rw [hnormP3, hnorm3] at hdvd
    norm_num at hdvd

/-- The inert prime `(2)` has norm `4` (residue degree `f = 2`). -/
theorem absNorm_span_two : Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 4 := by
  have hfin : Module.finrank ℤ (𝓞 K) = 2 := by
    rw [Module.finrank_eq_card_basis zetaExplicitIntegralBasis, Fintype.card_fin]
  rw [Ideal.absNorm_span_singleton,
    show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 from (map_ofNat _ 2).symm,
    Algebra.norm_algebraMap, hfin]
  rfl

private theorem quotient_zeta_ne_one_of_two_mem {M : Ideal (𝓞 K)} [M.IsMaximal]
    (h2mem : (2 : 𝓞 K) ∈ M) : Ideal.Quotient.mk M zetaInt ≠ 1 := by
  letI : Field ((𝓞 K) ⧸ M) := Ideal.Quotient.field M
  intro h1
  have hs := congrArg (Ideal.Quotient.mk M) zetaInt_relation
  rw [map_add, map_add, map_one, map_pow, map_zero,
    show Ideal.Quotient.mk M zetaInt = (1 : (𝓞 K) ⧸ M) from h1] at hs
  have h2q : (2 : (𝓞 K) ⧸ M) = 0 := by
    rw [show (2 : (𝓞 K) ⧸ M) = Ideal.Quotient.mk M 2 from (map_ofNat _ 2).symm,
      Ideal.Quotient.eq_zero_iff_mem]
    exact h2mem
  have h1q : (1 : (𝓞 K) ⧸ M) = 0 := by linear_combination hs - h2q
  exact one_ne_zero h1q

private theorem absNorm_maximal_over_span_two_eq_four {M : Ideal (𝓞 K)} (hMmax : M.IsMaximal)
    (hMle : Ideal.span {(2 : 𝓞 K)} ≤ M) : Ideal.absNorm M = 4 := by
  haveI := hMmax
  letI : Field ((𝓞 K) ⧸ M) := Ideal.Quotient.field M
  have hdvd : Ideal.absNorm M ∣ 4 :=
    absNorm_span_two ▸ Ideal.absNorm_dvd_absNorm_of_le hMle
  have h2mem : (2 : 𝓞 K) ∈ M := hMle (Ideal.mem_span_singleton_self _)
  set ω : (𝓞 K) ⧸ M := Ideal.Quotient.mk M zetaInt with hω
  have hω3 : ω ^ 3 = 1 := by
    rw [hω, ← map_pow, zetaInt_pow_three, map_one]
  have hω1 : ω ≠ 1 := by
    simpa [hω] using quotient_zeta_ne_one_of_two_mem (M := M) h2mem
  classical
  have habs : Ideal.absNorm M = Nat.card ((𝓞 K) ⧸ M) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite ((𝓞 K) ⧸ M) := by
    refine Nat.finite_of_card_ne_zero fun h0 => ?_
    rw [habs, h0] at hdvd
    norm_num at hdvd
  haveI : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _
  have hM1 : Ideal.absNorm M ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hMmax.ne_top
  obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Ideal.absNorm M ∣ 2 ^ 2 from hdvd)
  have hcard_eq : Fintype.card ((𝓞 K) ⧸ M) = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card, ← habs, hkeq]
  have hpc := FiniteField.pow_card ω
  rw [hcard_eq] at hpc
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω3
    simp at hω3
  have hpow1 : ω ^ (2 ^ k - 1) = 1 := by
    refine mul_right_cancel₀ hω0 ?_
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
    exact hpc
  have h3dvd : (3 : ℕ) ∣ 2 ^ k - 1 := by
    have horderω : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
    exact horderω ▸ orderOf_dvd_of_pow_eq_one hpow1
  rw [hkeq]
  interval_cases k
  · rw [hkeq] at hM1
    norm_num at hM1
  · norm_num at h3dvd
  · norm_num

/-- `2` is inert in `ℚ(ζ₃)`: `2 ≡ 2 (mod 3)`, equivalently `X² + X + 1` is irreducible
mod `2`, so `(2)` is itself prime. -/
theorem isPrime_span_two : (Ideal.span {(2 : 𝓞 K)}).IsPrime := by
  have htop : Ideal.span {(2 : 𝓞 K)} ≠ ⊤ := by
    intro h
    have h4 := absNorm_span_two
    rw [h, Ideal.absNorm_top] at h4
    norm_num at h4
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ htop
  have hM4 : Ideal.absNorm M = 4 := absNorm_maximal_over_span_two_eq_four hMmax hMle
  have heq := eq_of_le_of_absNorm_eq hMle absNorm_span_two hM4 (by norm_num)
  rw [heq]
  exact hMmax.isPrime

/-- The inert prime `(2)` lies over `(2)`. -/
theorem liesOver_span_two : (Ideal.span {(2 : 𝓞 K)}).LiesOver (Ideal.span {(2 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_two.ne_top
    (show Prime (2 : ℤ) by norm_num)]
  change (2 : 𝓞 K) ∈ Ideal.span {(2 : 𝓞 K)}
  exact Ideal.mem_span_singleton_self _

/-- The inert prime `(2)` has inertia degree `2`. -/
theorem inertiaDeg_span_two :
    (Ideal.span {(2 : ℤ)}).inertiaDeg (Ideal.span {(2 : 𝓞 K)}) = 2 := by
  haveI : (Ideal.span {(2 : 𝓞 K)}).LiesOver (Ideal.span {(2 : ℤ)}) := liesOver_span_two
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {(2 : 𝓞 K)})
    (p := 2) Nat.prime_two
  rw [absNorm_span_two] at h
  change 2 ^ 2 = 2 ^ (Ideal.span {(2 : ℤ)}).inertiaDeg (Ideal.span {(2 : 𝓞 K)}) at h
  exact Nat.pow_right_injective Nat.prime_two.one_lt h.symm

private theorem seven_eq_mul : (7 : 𝓞 K) = (3 + zetaInt) * (3 + zetaInt ^ 2) := by
  linear_combination -zetaInt_pow_three - 3 * zetaInt_relation

/-- `7 ≡ 1 (mod 3)` splits completely: `7 = (3 + ζ)(3 + ζ²)` and
`(7) = (3 + ζ) · (3 + ζ²)` is a product of two distinct primes of norm `7`. -/
theorem span_seven_eq :
    Ideal.span {(7 : 𝓞 K)} = Ideal.span {3 + zetaInt} * Ideal.span {3 + zetaInt ^ 2} := by
  rw [Ideal.span_singleton_mul_span_singleton, ← seven_eq_mul]

/-- The prime `(3 + ζ)` above `7` has norm `7` (residue degree `f = 1`). -/
theorem absNorm_span_seven_factor : Ideal.absNorm (Ideal.span {3 + zetaInt}) = 7 := by
  have hn : Algebra.norm ℤ (3 + zetaInt) = 7 := by
    simpa [Algebra.smul_def] using intNorm_eq_normForm 3 1
  rw [Ideal.absNorm_span_singleton, hn]
  rfl

/-- `(3 + ζ)` is a prime ideal — one of the two primes of `𝓞 K` above `7`. -/
theorem isPrime_span_seven_factor : (Ideal.span {3 + zetaInt}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_span_seven_factor]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- The prime `(3 + ζ)` lies over `(7)`. -/
theorem liesOver_span_seven_factor :
    (Ideal.span {3 + zetaInt}).LiesOver (Ideal.span {(7 : ℤ)}) := by
  rw [Ideal.liesOver_span_iff isPrime_span_seven_factor.ne_top
    (show Prime (7 : ℤ) by norm_num)]
  change (7 : 𝓞 K) ∈ Ideal.span {3 + zetaInt}
  rw [seven_eq_mul]
  exact Ideal.mul_mem_right (3 + zetaInt ^ 2) (Ideal.span {3 + zetaInt})
    (Ideal.mem_span_singleton_self (3 + zetaInt))

/-- The split prime `(3 + ζ)` has inertia degree `1` over `7`. -/
theorem inertiaDeg_span_seven_factor :
    (Ideal.span {(7 : ℤ)}).inertiaDeg (Ideal.span {3 + zetaInt}) = 1 := by
  haveI : (Ideal.span {3 + zetaInt}).LiesOver (Ideal.span {(7 : ℤ)}) :=
    liesOver_span_seven_factor
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (P := Ideal.span {3 + zetaInt})
    (p := 7) (by norm_num : Nat.Prime 7)
  rw [absNorm_span_seven_factor] at h
  exact ((Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h.symm).2

/-- The splitting law at ramified primes: a rational prime `p` ramifies in `ℚ(ζ₃)` iff
`p = 3`, i.e. iff `p` divides the discriminant `-3`. -/
theorem ramified_iff_eq_three (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 3 := by
  constructor
  · rintro ⟨P, hP, hle2⟩
    haveI : P.IsPrime := hP
    have hple : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ P :=
      hle2.trans (Ideal.pow_le_self (by norm_num))
    have hpmemP : ((p : ℕ) : 𝓞 K) ∈ P := hple (Ideal.mem_span_singleton_self _)
    have hpne : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hPbot : P ≠ ⊥ := by
      intro h
      rw [h] at hpmemP
      exact hpne (Ideal.mem_bot.mp hpmemP)
    have hfin : Module.finrank ℤ (𝓞 K) = 2 := by
      rw [Module.finrank_eq_card_basis zetaExplicitIntegralBasis, Fintype.card_fin]
    have habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 := by
      rw [Ideal.absNorm_span_singleton]
      have hcast : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ((p : ℕ) : ℤ) := by
        push_cast
        rfl
      rw [hcast, Algebra.norm_algebraMap, hfin, Int.natAbs_pow, Int.natAbs_natCast]
    have habsPp2 : Ideal.absNorm P ∣ p ^ 2 :=
      habsp ▸ Ideal.absNorm_dvd_absNorm_of_le hple
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow hp).mp habsPp2
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hkeq
      exact hP.ne_top (Ideal.absNorm_eq_one_iff.mp hkeq)
    have hle2' : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 2 := by
      simpa [Ideal.map_span, Set.image_singleton] using hle2
    have hno3 : ¬ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 3 :=
      not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow hp habsp hkeq hk0
    have hunram : ¬ Algebra.IsUnramifiedAt ℤ P :=
      not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ hp hpmemP hPbot hle2'
        hno3
    have hPdiff : P ∣ differentIdeal ℤ (𝓞 K) := dvd_differentIdeal_iff.mpr hunram
    have habsP3 : Ideal.absNorm P ∣ 3 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq] at h
      simpa using h
    have hpdvd : p ∣ 3 := (hkeq ▸ dvd_pow_self p hk0).trans habsP3
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpdvd
  · rintro rfl
    refine ⟨Ideal.span {zetaInt - 1}, isPrime_span_zetaInt_sub_one, ?_⟩
    have hcast : ((3 : ℕ) : 𝓞 K) = (3 : 𝓞 K) := by norm_num
    rw [hcast, span_three_eq]

/-- The inert prime `(2)` is unramified. -/
theorem ramificationIdx_span_two :
    (Ideal.span {(2 : ℤ)}).ramificationIdx (Ideal.span {(2 : 𝓞 K)}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    simp
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(2 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {(2 : 𝓞 K)}, isPrime_span_two, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h := (ramified_iff_eq_three 2 Nat.prime_two).mp hram
    norm_num at h

/-- The split prime `(3 + ζ)` over `7` is unramified. -/
theorem ramificationIdx_span_seven_factor :
    (Ideal.span {(7 : ℤ)}).ramificationIdx (Ideal.span {3 + zetaInt}) = 1 := by
  refine Ideal.ramificationIdx_spec ?hle ?hgt
  · rw [Ideal.map_span, Set.image_singleton, pow_one]
    change Ideal.span {(7 : 𝓞 K)} ≤ Ideal.span {3 + zetaInt}
    rw [span_seven_eq]
    exact Ideal.mul_le_right
  · intro hle2
    have hram : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(7 : 𝓞 K)} ≤ P ^ 2 := by
      refine ⟨Ideal.span {3 + zetaInt}, isPrime_span_seven_factor, ?_⟩
      rw [Ideal.map_span, Set.image_singleton] at hle2
      exact hle2
    have h := (ramified_iff_eq_three 7 (by norm_num)).mp hram
    norm_num at h

private theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 := by
  rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, degree_eq_two]

private theorem one_mod_three_of_prime_norm (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧ Ideal.absNorm P = p) →
      p % 3 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨P, hPprime, hle, habs⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at habs
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [habs]; exact hp.ne_zero)
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 K) ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact habs
  let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) hp hcard'
  obtain ⟨s, hs⟩ := e.surjective (Ideal.Quotient.mk P zetaInt)
  have hs3 : s ^ 3 = (1 : ZMod p) := by
    apply e.injective
    rw [map_pow, hs, ← map_pow (Ideal.Quotient.mk P), zetaInt_pow_three, map_one, map_one]
  have hssum : s ^ 2 + s + 1 = (0 : ZMod p) := by
    apply e.injective
    rw [map_add, map_add, map_one, map_pow, hs, map_zero]
    have hmk := congrArg (Ideal.Quotient.mk P) zetaInt_relation
    rw [map_add, map_add, map_one, map_pow, map_zero] at hmk
    exact hmk
  have hs1 : s ≠ 1 := by
    intro h1
    rw [h1] at hssum
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination hssum
    have hdvd := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp hdvd)
  set u : (ZMod p)ˣ := Units.mkOfMulEqOne s (s ^ 2)
    (by rw [← pow_succ']; exact hs3) with hudef
  have hu : (u : ZMod p) = s := rfl
  have horder : orderOf u = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · ext
      rw [Units.val_pow_eq_pow_val, hu]
      exact hs3
    · intro h1
      apply hs1
      rw [← hu, h1, Units.val_one]
  have hdvd_card : (3 : ℕ) ∣ p - 1 := by
    have h := orderOf_dvd_natCard u
    rw [horder, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp] at h
    exact h
  have h2le := hp.two_le
  obtain ⟨m, hm⟩ := hdvd_card
  omega

private theorem exists_prime_norm_of_one_mod_three (p : ℕ) (hp : p.Prime) :
    p % 3 = 1 →
      ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧ Ideal.absNorm P = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hmod
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have h2le := hp.two_le
  obtain ⟨m, hm⟩ : (3 : ℕ) ∣ p - 1 := ⟨(p - 1) / 3, by omega⟩
  have hm0 : m ≠ 0 := by omega
  have hou : orderOf (g ^ m) = 3 := by
    rw [orderOf_pow, hog, hm]
    have hgcd : Nat.gcd (3 * m) m = m := Nat.gcd_eq_right ⟨3, by ring⟩
    rw [hgcd, Nat.mul_div_assoc 3 (dvd_refl m), Nat.div_self (show 0 < m by omega),
      mul_one]
  have hu3 : ((g ^ m : (ZMod p)ˣ) : ZMod p) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (g ^ m)
    rw [hou] at h
    have hc := congrArg Units.val h
    simpa using hc
  have hu1 : ((g ^ m : (ZMod p)ˣ) : ZMod p) ≠ 1 := by
    intro h1
    have : (g ^ m) = 1 := Units.ext (by simpa using h1)
    rw [this, orderOf_one] at hou
    norm_num at hou
  have hr : (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) ^ 2 +
      (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) + 1 = 0 := by
    have hcast : (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) =
        ((g ^ m : (ZMod p)ˣ) : ZMod p) := by
      push_cast
      exact ZMod.natCast_rightInverse _
    rw [hcast]
    set v : ZMod p := ((g ^ m : (ZMod p)ˣ) : ZMod p)
    have hfactor : (v - 1) * (v ^ 2 + v + 1) = 0 := by
      linear_combination hu3
    rcases mul_eq_zero.mp hfactor with h | h
    · exact absurd (by linear_combination h) hu1
    · linear_combination h
  refine ⟨Ideal.span {((p : ℕ) : 𝓞 K),
    zetaInt - ((((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : 𝓞 K))},
    (isMaximal_span_pair p _ hr).isPrime, ?_, absNorm_span_pair p _ hr⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact Ideal.subset_span (by simp)

private theorem exists_prime_norm_iff_one_mod_three (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧ Ideal.absNorm P = p) ↔
      p % 3 = 1 := by
  constructor
  · exact one_mod_three_of_prime_norm p hp hp3
  · exact exists_prime_norm_of_one_mod_three p hp

private theorem one_mod_three_of_splits (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) → p % 3 = 1 := by
  rintro ⟨P, Q, hPprime, hQprime, hPQ, hspan⟩
  have hPle : Ideal.span {(p : 𝓞 K)} ≤ P := by
    rw [hspan]
    exact (Ideal.mul_le_right (I := P) (J := Q))
  have hmul := _root_.map_mul Ideal.absNorm P Q
  have hspan' : Ideal.span {((p : ℕ) : 𝓞 K)} = P * Q := by
    simpa using hspan
  rw [← hspan', absNorm_span_natCast] at hmul
  have hPnorm_ne_one : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hPprime.ne_top
  have hQnorm_ne_one : Ideal.absNorm Q ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hQprime.ne_top
  have hPnorm_eq : Ideal.absNorm P = p :=
    left_eq_prime_of_mul_eq_prime_sq_of_ne_one hp hmul.symm hPnorm_ne_one hQnorm_ne_one
  exact (exists_prime_norm_iff_one_mod_three p hp hp3).mp
    ⟨P, hPprime, hPle, hPnorm_eq⟩

private theorem splits_of_one_mod_three (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    p % 3 = 1 →
      ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
        Ideal.span {(p : 𝓞 K)} = P * Q := by
  intro hmod
  obtain ⟨P, hPprime, hPle, hPnorm⟩ :=
    (exists_prime_norm_iff_one_mod_three p hp hp3).mpr hmod
  obtain ⟨Q, hspan⟩ := Ideal.dvd_iff_le.mpr hPle
  have hQnorm : Ideal.absNorm Q = p := by
    have hmul := _root_.map_mul Ideal.absNorm P Q
    have hspan' : Ideal.span {((p : ℕ) : 𝓞 K)} = P * Q := by
      simpa using hspan
    rw [← hspan', absNorm_span_natCast, hPnorm] at hmul
    rw [pow_two] at hmul
    exact Nat.eq_of_mul_eq_mul_left hp.pos hmul.symm
  have hQprime : Q.IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [hQnorm]
    exact (Nat.irreducible_iff_nat_prime _).mpr hp
  have hPQ : P ≠ Q := by
    intro h
    have hram : ∃ R : Ideal (𝓞 K), R.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ R ^ 2 := by
      refine ⟨P, hPprime, ?_⟩
      rw [hspan, h, sq]
    exact hp3 ((ramified_iff_eq_three p hp).mp hram)
  exact ⟨P, Q, hPprime, hQprime, hPQ, by simpa using hspan⟩

/-- The quadratic (cyclotomic) splitting law for `ℚ(ζ₃)`: an unramified rational prime `p`
splits into two distinct primes iff `p ≡ 1 (mod 3)`, and is inert otherwise. This is the
simplest instance of splitting governed by congruence conditions (class field theory). -/
theorem splits_iff_one_mod_three (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) ↔ p % 3 = 1 := by
  constructor
  · exact one_mod_three_of_splits p hp hp3
  · exact splits_of_one_mod_three p hp hp3

end NumberField.CyclotomicThree

/-!
## Different
-/

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open IsDedekindDomain

namespace NumberField.CyclotomicThree

private theorem span_zetaInt_sub_one_dvd_differentIdeal :
    Ideal.span {zetaInt - 1} ∣ differentIdeal ℤ (𝓞 K) := by
  have hP : (Ideal.span {zetaInt - 1} : Ideal (𝓞 K)).IsPrime :=
    isPrime_span_zetaInt_sub_one
  haveI : (Ideal.span {zetaInt - 1} : Ideal (𝓞 K)).IsPrime := hP
  rw [dvd_differentIdeal_iff]
  have hpmemP : ((3 : ℕ) : 𝓞 K) ∈ Ideal.span {zetaInt - 1} := by
    have hmem : (3 : 𝓞 K) ∈ Ideal.span {(3 : 𝓞 K)} := Ideal.mem_span_singleton_self _
    rw [span_three_eq] at hmem
    exact Ideal.pow_le_self (by norm_num) hmem
  have hPbot : (Ideal.span {zetaInt - 1} : Ideal (𝓞 K)) ≠ ⊥ := by
    intro hbot
    exact zetaInt_sub_one_prime.ne_zero (Ideal.span_singleton_eq_bot.mp hbot)
  have hle2 : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((3 : ℕ) : ℤ)}) ≤
      (Ideal.span {zetaInt - 1} : Ideal (𝓞 K)) ^ 2 := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(3 : 𝓞 K)} ≤ Ideal.span {zetaInt - 1} ^ 2
    rw [span_three_eq]
  have habsp : Ideal.absNorm (Ideal.span {((3 : ℕ) : 𝓞 K)}) = 3 ^ 2 := by
    change Ideal.absNorm (Ideal.span {(3 : 𝓞 K)}) = 3 ^ 2
    have hfin : Module.finrank ℤ (𝓞 K) = 2 := by
      rw [Module.finrank_eq_card_basis zetaExplicitIntegralBasis, Fintype.card_fin]
    rw [Ideal.absNorm_span_singleton,
      show (3 : 𝓞 K) = algebraMap ℤ (𝓞 K) 3 from (map_ofNat _ 3).symm,
      Algebra.norm_algebraMap, hfin]
    rfl
  have hkeq : Ideal.absNorm (Ideal.span {zetaInt - 1} : Ideal (𝓞 K)) = 3 ^ 1 := by
    rw [absNorm_span_zetaInt_sub_one]
    rfl
  have hnle : ¬ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((3 : ℕ) : ℤ)}) ≤
      (Ideal.span {zetaInt - 1} : Ideal (𝓞 K)) ^ (1 + 2) :=
    NumberField.FieldExamples.not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow
      Nat.prime_three habsp hkeq (by norm_num : 1 ≠ 0)
  exact
    NumberField.FieldExamples.not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ
      Nat.prime_three hpmemP hPbot hle2 hnle

theorem absNorm_differentIdeal_eq_three :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = 3 := by
  rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq]
  norm_num

theorem prime_dvd_differentIdeal_iff_eq_span_zeta_sub_one
    (P : Ideal (𝓞 K)) (_hP : P.IsPrime) (_hP0 : P ≠ ⊥) :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ P = Ideal.span {zetaInt - 1} := by
  constructor
  · intro hdiv
    haveI : P.IsPrime := _hP
    have hnormdvd : Ideal.absNorm P ∣ 3 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdiv)
      rw [absNorm_differentIdeal_eq_three] at h
      exact h
    have hnorm_eq : Ideal.absNorm P = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hnormdvd with h1 | h3
      · exfalso
        exact _hP.ne_top (Ideal.absNorm_eq_one_iff.mp h1)
      · exact h3
    have hthree_mem : (3 : 𝓞 K) ∈ P := by
      simpa [hnorm_eq] using P.absNorm_mem
    haveI : P.LiesOver (Ideal.span {(3 : ℤ)}) := by
      rw [Ideal.liesOver_span_iff _hP.ne_top (show Prime (3 : ℤ) by norm_num)]
      change (3 : 𝓞 K) ∈ P
      exact hthree_mem
    have huniq := IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'
      (p := 3) (K := K) zeta_isPrimitiveRoot P
    simpa [zetaInt] using huniq
  · intro h
    rw [h]
    exact span_zetaInt_sub_one_dvd_differentIdeal

end NumberField.CyclotomicThree
