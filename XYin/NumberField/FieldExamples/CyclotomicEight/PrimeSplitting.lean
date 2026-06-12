import XYin.NumberField.FieldExamples.CyclotomicEight.Subfields

noncomputable section

open Module
open scoped NumberField nonZeroDivisors

namespace XYin.NumberField.New.CyclotomicEight

/-! ## 5. Splitting of primes -/

private theorem coe_zetaInt : algebraMap (𝓞 K) K zetaInt = ζ := rfl

private theorem gen_eq_zetaInt : zeta_isPrimitiveRoot.integralPowerBasis.gen = zetaInt := by
  rw [zeta_isPrimitiveRoot.integralPowerBasis_gen]; rfl

/-- Private forward copy of `sigmaThree` (the public definition appears in section 8). -/
private noncomputable def sig3 : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 3 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private noncomputable def sig5 : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 5 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private noncomputable def sig7 : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 7 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private theorem sig3_zeta : sig3 ζ = ζ ^ 3 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 3 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private theorem sig5_zeta : sig5 ζ = ζ ^ 5 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 5 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private theorem sig7_zeta : sig7 ζ = ζ ^ 7 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 7 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private theorem autEq' (σ : K ≃ₐ[ℚ] K) : σ = 1 ∨ σ = sig3 ∨ σ = sig5 ∨ σ = sig7 := by
  have hval : ∀ t : (ZMod 8)ˣ, (t : ZMod 8).val = 1 ∨ (t : ZMod 8).val = 3 ∨
      (t : ZMod 8).val = 5 ∨ (t : ZMod 8).val = 7 := by decide
  have hspec := IsPrimitiveRoot.autToPow_spec ℚ zeta_isPrimitiveRoot σ
  have hext : ∀ τ : K ≃ₐ[ℚ] K, σ ζ = τ ζ → σ = τ := by
    intro τ h
    have hgen := (zeta_isPrimitiveRoot.powerBasis ℚ).algHom_ext
      (f := (σ : K →ₐ[ℚ] K)) (g := (τ : K →ₐ[ℚ] K))
      (by rwa [IsPrimitiveRoot.powerBasis_gen])
    exact AlgEquiv.ext fun x => AlgHom.congr_fun hgen x
  rcases hval (IsPrimitiveRoot.autToPow ℚ zeta_isPrimitiveRoot σ) with h | h | h | h <;>
    rw [h] at hspec
  · exact Or.inl (hext 1 (by rw [← hspec, pow_one]; rfl))
  · exact Or.inr (Or.inl (hext sig3 (by rw [← hspec, sig3_zeta])))
  · exact Or.inr (Or.inr (Or.inl (hext sig5 (by rw [← hspec, sig5_zeta]))))
  · exact Or.inr (Or.inr (Or.inr (hext sig7 (by rw [← hspec, sig7_zeta]))))

/-- The product of the four Galois conjugates computes the field norm. -/
private theorem prod_aut_apply (x : K) :
    ∏ σ : K ≃ₐ[ℚ] K, σ x = x * sig3 x * sig5 x * sig7 x := by
  classical
  have hne : ∀ (i j : ℕ) (σ τ : K ≃ₐ[ℚ] K), i < 8 → j < 8 → i ≠ j →
      σ ζ = ζ ^ i → τ ζ = ζ ^ j → σ ≠ τ := fun i j σ τ hi hj hij hσ hτ hστ =>
    hij (zeta_isPrimitiveRoot.pow_inj hi hj (by rw [← hσ, ← hτ, hστ]))
  have hid : (1 : K ≃ₐ[ℚ] K) ζ = ζ ^ 1 := by rw [pow_one]; rfl
  have h1 : (1 : K ≃ₐ[ℚ] K) ≠ sig3 :=
    hne 1 3 _ _ (by norm_num) (by norm_num) (by norm_num) hid sig3_zeta
  have h2 : (1 : K ≃ₐ[ℚ] K) ≠ sig5 :=
    hne 1 5 _ _ (by norm_num) (by norm_num) (by norm_num) hid sig5_zeta
  have h3 : (1 : K ≃ₐ[ℚ] K) ≠ sig7 :=
    hne 1 7 _ _ (by norm_num) (by norm_num) (by norm_num) hid sig7_zeta
  have h4 : sig3 ≠ sig5 := hne 3 5 _ _ (by norm_num) (by norm_num) (by norm_num)
    sig3_zeta sig5_zeta
  have h5 : sig3 ≠ sig7 := hne 3 7 _ _ (by norm_num) (by norm_num) (by norm_num)
    sig3_zeta sig7_zeta
  have h6 : sig5 ≠ sig7 := hne 5 7 _ _ (by norm_num) (by norm_num) (by norm_num)
    sig5_zeta sig7_zeta
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, sig3, sig5, sig7} := by
    refine (Finset.eq_univ_iff_forall.mpr fun σ => ?_).symm
    rcases autEq' σ with h | h | h | h <;> simp [h]
  rw [huniv, Finset.prod_insert (by simp [h1, h2, h3]), Finset.prod_insert (by simp [h4, h5]),
    Finset.prod_pair h6]
  change x * (sig3 x * (sig5 x * sig7 x)) = _
  ring

/-- Computing integral norms via the four Galois conjugates. -/
private theorem intNorm_eq (x : 𝓞 K) (n : ℤ)
    (h : algebraMap (𝓞 K) K x * sig3 (algebraMap (𝓞 K) K x) *
      sig5 (algebraMap (𝓞 K) K x) * sig7 (algebraMap (𝓞 K) K x) = (n : K)) :
    Algebra.norm ℤ x = n := by
  haveI := IsCyclotomicExtension.isGalois {8} ℚ K
  have h1 : algebraMap ℚ K (Algebra.norm ℚ (algebraMap (𝓞 K) K x)) = ((n : ℚ) : K) := by
    rw [Algebra.norm_eq_prod_automorphisms, prod_aut_apply, h]
    push_cast
    ring
  have h2 : Algebra.norm ℚ (algebraMap (𝓞 K) K x) = (n : ℚ) := by
    apply (algebraMap ℚ K).injective
    rw [h1, eq_ratCast (algebraMap ℚ K) (n : ℚ)]
  have h3 : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (algebraMap (𝓞 K) K x) :=
    Algebra.coe_norm_int x
  rw [h2] at h3
  exact_mod_cast h3

/-! ### Norm form in the power basis -/

/-- The norm form in the basis `1, ζ, ζ², ζ³`. -/
def normForm {R : Type*} [CommRing R] (a b c d : R) : R :=
  (a ^ 2 - c ^ 2 + 2 * b * d) ^ 2 + (2 * a * c - b ^ 2 + d ^ 2) ^ 2

/-- The field norm of `a + bζ + cζ² + dζ³`. -/
theorem norm_eq_normForm (a b c d : ℚ) :
    Algebra.norm ℚ
      (a • (1 : K) + b • ζ + c • ζ ^ 2 + d • ζ ^ 3) = normForm a b c d := by
  sorry

/-- The integral norm form on `𝓞 K = ℤ[ζ]`. -/
theorem intNorm_eq_normForm (a b c d : ℤ) :
    Algebra.norm ℤ
      (a • (1 : 𝓞 K) + b • zetaInt + c • zetaInt ^ 2 + d • zetaInt ^ 3) =
        normForm a b c d := by
  sorry

/-- The unit equation for `ℤ[ζ₈]` in the integral power basis. -/
theorem isUnit_iff_normForm (a b c d : ℤ) :
    IsUnit (a • (1 : 𝓞 K) + b • zetaInt + c • zetaInt ^ 2 + d • zetaInt ^ 3) ↔
      (normForm a b c d).natAbs = 1 := by
  sorry

private theorem cyclotomic_eight_int : Polynomial.cyclotomic 8 ℤ = Polynomial.X ^ 4 + 1 := by
  have h4 : Polynomial.cyclotomic 4 ℤ = Polynomial.X ^ 2 + 1 := by
    have h := Polynomial.cyclotomic_expand_eq_cyclotomic (R := ℤ) Nat.prime_two (dvd_refl 2)
    rw [Polynomial.cyclotomic_two, show (2 * 2 : ℕ) = 4 from rfl] at h
    rw [← h, map_add, map_one, Polynomial.expand_X]
  have h8 := Polynomial.cyclotomic_expand_eq_cyclotomic (R := ℤ) Nat.prime_two
    (by norm_num : (2 : ℕ) ∣ 4)
  rw [h4, show (4 * 2 : ℕ) = 8 from rfl] at h8
  rw [← h8, map_add, map_one, map_pow, Polynomial.expand_X]
  ring

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

/-- Reduction `𝓞 K → 𝔽_p` sending `ζ ↦ r`, for `r` a fourth root of `-1` mod `p`. -/
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
        rw [← hd]; ring
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

private theorem absNorm_span_pair (p : ℕ) (r : ℤ) (hr : ((r : ZMod p)) ^ 4 = -1) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K), zetaInt - (r : 𝓞 K)}) = p := by
  rw [← ker_residueHom p r hr, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (residueHom_surjective p r hr)).toEquiv]
  exact Nat.card_zmod p

/-- `2` is totally ramified: `(2) = (1 - ζ)⁴` as ideals of `𝓞 K` — ramification index
`e = 4` equals the full degree. -/
theorem span_two_eq : Ideal.span {(2 : 𝓞 K)} = Ideal.span {1 - zetaInt} ^ 4 := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
  refine ⟨⟨-2 * zetaInt + 3 * zetaInt ^ 2 - 2 * zetaInt ^ 3,
    -2 * zetaInt - 3 * zetaInt ^ 2 - 2 * zetaInt ^ 3,
    by linear_combination (4 * zetaInt ^ 2 - 1) * zetaInt_pow_four,
    by linear_combination (4 * zetaInt ^ 2 - 1) * zetaInt_pow_four⟩, ?_⟩
  change (2 : 𝓞 K) * (-2 * zetaInt + 3 * zetaInt ^ 2 - 2 * zetaInt ^ 3) = (1 - zetaInt) ^ 4
  linear_combination -zetaInt_pow_four

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

/-- `(1 - ζ)` is a prime ideal — the unique prime of `𝓞 K` above `2`. -/
theorem isPrime_span_one_sub_zeta : (Ideal.span {1 - zetaInt}).IsPrime := by
  rw [span_one_sub_zetaInt_eq_pair]
  exact (isMaximal_span_pair 2 1 (by decide)).isPrime

/-- The prime `(1 - ζ)` above `2` has norm `Φ₈(1) = 2` (residue degree `f = 1`). -/
theorem absNorm_span_one_sub_zeta : Ideal.absNorm (Ideal.span {1 - zetaInt}) = 2 := by
  rw [span_one_sub_zetaInt_eq_pair]
  exact absNorm_span_pair 2 1 (by decide)

private theorem span_pair_three_left :
    Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + zetaInt + 2} =
      Ideal.span {zetaInt ^ 2 + zetaInt - 1} := by
  have h3 : (3 : 𝓞 K) ∈ Ideal.span {zetaInt ^ 2 + zetaInt - 1} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨-(zetaInt ^ 3 + zetaInt ^ 2 + 1), ?_⟩
    linear_combination (zetaInt + 2) * zetaInt_pow_four
  refine le_antisymm (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · rintro y (rfl | rfl)
    · exact h3
    · rw [SetLike.mem_coe, show zetaInt ^ 2 + zetaInt + 2 =
        (zetaInt ^ 2 + zetaInt - 1) + 3 from by ring]
      exact Ideal.add_mem _ (Ideal.mem_span_singleton_self _) h3
  · exact Ideal.mem_span_pair.mpr ⟨-1, 1, by ring⟩

private theorem span_pair_three_right :
    Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + 2 * zetaInt + 2} =
      Ideal.span {zetaInt ^ 2 - zetaInt - 1} := by
  have h3 : (3 : 𝓞 K) ∈ Ideal.span {zetaInt ^ 2 - zetaInt - 1} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨zetaInt ^ 3 - zetaInt ^ 2 - 1, ?_⟩
    linear_combination (2 - zetaInt) * zetaInt_pow_four
  refine le_antisymm (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · rintro y (rfl | rfl)
    · exact h3
    · rw [SetLike.mem_coe, show zetaInt ^ 2 + 2 * zetaInt + 2 =
        (zetaInt ^ 2 - zetaInt - 1) + 3 * (zetaInt + 1) from by ring]
      exact Ideal.add_mem _ (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ h3)
  · exact Ideal.mem_span_pair.mpr ⟨-(zetaInt + 1), 1, by ring⟩

/-- `3` splits into two primes of degree `2`: `3` has order `2` in `(ℤ/8)ˣ`, and
`Φ₈ = X⁴ + 1 ≡ (X² + X + 2)(X² + 2X + 2) (mod 3)`. -/
theorem span_three_eq :
    Ideal.span {(3 : 𝓞 K)} =
      Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + zetaInt + 2} *
        Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + 2 * zetaInt + 2} := by
  rw [span_pair_three_left, span_pair_three_right, Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_span_singleton]
  refine ⟨⟨-zetaInt ^ 2, zetaInt ^ 2, by linear_combination -zetaInt_pow_four,
    by linear_combination -zetaInt_pow_four⟩, ?_⟩
  change (3 : 𝓞 K) * (-zetaInt ^ 2) =
    (zetaInt ^ 2 + zetaInt - 1) * (zetaInt ^ 2 - zetaInt - 1)
  linear_combination -zetaInt_pow_four

/-- There is no prime of `𝓞 K` with residue field `𝔽₃`: `X⁴ + 1` has no root mod `3`. -/
private theorem absNorm_ne_three (P : Ideal (𝓞 K)) : Ideal.absNorm P ≠ 3 := by
  intro hcard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 K) ⧸ P) = 3 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) (by norm_num) hcard'
  obtain ⟨s, hs⟩ := e.surjective (Ideal.Quotient.mk P zetaInt)
  have hs4 : s ^ 4 = (-1 : ZMod 3) := by
    apply e.injective
    rw [map_pow, hs, ← map_pow (Ideal.Quotient.mk P), zetaInt_pow_four, map_neg, map_one,
      map_neg, map_one]
  clear hs
  revert s
  decide

private theorem isPrime_of_absNorm_nine {g : 𝓞 K}
    (h9 : Ideal.absNorm (Ideal.span {g}) = 9) : (Ideal.span {g}).IsPrime := by
  have htop : Ideal.span {g} ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at h9
    norm_num at h9
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ htop
  have hdvd : Ideal.absNorm M ∣ 9 := h9 ▸ Ideal.absNorm_dvd_absNorm_of_le hMle
  have hM1 : Ideal.absNorm M ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hMmax.ne_top
  have hM3 : Ideal.absNorm M ≠ 3 := absNorm_ne_three M
  have hM9 : Ideal.absNorm M = 9 := by
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Ideal.absNorm M ∣ 3 ^ 2 from hdvd)
    interval_cases k <;> simp_all
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hMle
  have hCnorm : Ideal.absNorm C = 1 := by
    have hmul := _root_.map_mul Ideal.absNorm M C
    rw [← hC, h9, hM9] at hmul
    omega
  have hgM : Ideal.span {g} = M := by
    rw [hC, Ideal.absNorm_eq_one_iff.mp hCnorm, Ideal.mul_top]
  rw [hgM]
  exact hMmax.isPrime

private theorem absNorm_span_g1 :
    Ideal.absNorm (Ideal.span {zetaInt ^ 2 + zetaInt - 1}) = 9 := by
  have hn : Algebra.norm ℤ (zetaInt ^ 2 + zetaInt - 1) = 9 := by
    apply intNorm_eq
    have e0 : algebraMap (𝓞 K) K (zetaInt ^ 2 + zetaInt - 1) = ζ ^ 2 + ζ - 1 := by
      simp [map_add, map_sub, map_pow, map_one, coe_zetaInt]
    rw [e0]
    have e3 : sig3 (ζ ^ 2 + ζ - 1) = ζ ^ 3 - ζ ^ 2 - 1 := by
      rw [map_sub, map_add, map_pow, map_one, sig3_zeta]
      linear_combination ζ ^ 2 * zeta_pow_four
    have e5 : sig5 (ζ ^ 2 + ζ - 1) = ζ ^ 2 - ζ - 1 := by
      rw [map_sub, map_add, map_pow, map_one, sig5_zeta]
      linear_combination (ζ ^ 6 - ζ ^ 2 + ζ) * zeta_pow_four
    have e7 : sig7 (ζ ^ 2 + ζ - 1) = -ζ ^ 3 - ζ ^ 2 - 1 := by
      rw [map_sub, map_add, map_pow, map_one, sig7_zeta]
      linear_combination (ζ ^ 10 - ζ ^ 6 + ζ ^ 2 + ζ ^ 3) * zeta_pow_four
    rw [e3, e5, e7]
    push_cast
    linear_combination (-ζ ^ 6 + 4 * ζ ^ 4 - ζ ^ 2 - 8) * zeta_pow_four
  rw [Ideal.absNorm_span_singleton, hn]
  rfl

private theorem absNorm_span_g2 :
    Ideal.absNorm (Ideal.span {zetaInt ^ 2 - zetaInt - 1}) = 9 := by
  have hn : Algebra.norm ℤ (zetaInt ^ 2 - zetaInt - 1) = 9 := by
    apply intNorm_eq
    have e0 : algebraMap (𝓞 K) K (zetaInt ^ 2 - zetaInt - 1) = ζ ^ 2 - ζ - 1 := by
      simp [map_sub, map_pow, map_one, coe_zetaInt]
    rw [e0]
    have e3 : sig3 (ζ ^ 2 - ζ - 1) = -ζ ^ 3 - ζ ^ 2 - 1 := by
      rw [map_sub, map_sub, map_pow, map_one, sig3_zeta]
      linear_combination ζ ^ 2 * zeta_pow_four
    have e5 : sig5 (ζ ^ 2 - ζ - 1) = ζ ^ 2 + ζ - 1 := by
      rw [map_sub, map_sub, map_pow, map_one, sig5_zeta]
      linear_combination (ζ ^ 6 - ζ ^ 2 - ζ) * zeta_pow_four
    have e7 : sig7 (ζ ^ 2 - ζ - 1) = ζ ^ 3 - ζ ^ 2 - 1 := by
      rw [map_sub, map_sub, map_pow, map_one, sig7_zeta]
      linear_combination (ζ ^ 10 - ζ ^ 6 + ζ ^ 2 - ζ ^ 3) * zeta_pow_four
    rw [e3, e5, e7]
    push_cast
    linear_combination (-ζ ^ 6 + 4 * ζ ^ 4 - ζ ^ 2 - 8) * zeta_pow_four
  rw [Ideal.absNorm_span_singleton, hn]
  rfl

/-- Both primes above `3` are prime ideals of norm `3² = 9`. -/
theorem isPrime_primesAboveThree :
    (Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + zetaInt + 2}).IsPrime ∧
      (Ideal.span {(3 : 𝓞 K), zetaInt ^ 2 + 2 * zetaInt + 2}).IsPrime := by
  constructor
  · rw [span_pair_three_left]
    exact isPrime_of_absNorm_nine absNorm_span_g1
  · rw [span_pair_three_right]
    exact isPrime_of_absNorm_nine absNorm_span_g2

private theorem seventeen_mem_span_two :
    (17 : 𝓞 K) ∈ Ideal.span {zetaInt - 2} := by
  rw [Ideal.mem_span_singleton]
  refine ⟨(zetaInt ^ 3 - 2) * ((zetaInt ^ 5 - 2) * (zetaInt ^ 7 - 2)), ?_⟩
  linear_combination (-zetaInt ^ 12 + 2 * zetaInt ^ 11 + 2 * zetaInt ^ 9 - 3 * zetaInt ^ 8 -
    4 * zetaInt ^ 6 - 5 * zetaInt ^ 4 + 8 * zetaInt ^ 3 + 8 * zetaInt + 1) * zetaInt_pow_four

private theorem seventeen_mem_span_eight :
    (17 : 𝓞 K) ∈ Ideal.span {zetaInt ^ 3 - 2} := by
  rw [Ideal.mem_span_singleton]
  refine ⟨(zetaInt - 2) * ((zetaInt ^ 5 - 2) * (zetaInt ^ 7 - 2)), ?_⟩
  linear_combination (-zetaInt ^ 12 + 2 * zetaInt ^ 11 + 2 * zetaInt ^ 9 - 3 * zetaInt ^ 8 -
    4 * zetaInt ^ 6 - 5 * zetaInt ^ 4 + 8 * zetaInt ^ 3 + 8 * zetaInt + 1) * zetaInt_pow_four

private theorem seventeen_mem_span_nine :
    (17 : 𝓞 K) ∈ Ideal.span {zetaInt ^ 7 - 2} := by
  rw [Ideal.mem_span_singleton]
  refine ⟨(zetaInt - 2) * ((zetaInt ^ 3 - 2) * (zetaInt ^ 5 - 2)), ?_⟩
  linear_combination (-zetaInt ^ 12 + 2 * zetaInt ^ 11 + 2 * zetaInt ^ 9 - 3 * zetaInt ^ 8 -
    4 * zetaInt ^ 6 - 5 * zetaInt ^ 4 + 8 * zetaInt ^ 3 + 8 * zetaInt + 1) * zetaInt_pow_four

private theorem seventeen_mem_span_fifteen :
    (17 : 𝓞 K) ∈ Ideal.span {zetaInt ^ 5 - 2} := by
  rw [Ideal.mem_span_singleton]
  refine ⟨(zetaInt - 2) * ((zetaInt ^ 3 - 2) * (zetaInt ^ 7 - 2)), ?_⟩
  linear_combination (-zetaInt ^ 12 + 2 * zetaInt ^ 11 + 2 * zetaInt ^ 9 - 3 * zetaInt ^ 8 -
    4 * zetaInt ^ 6 - 5 * zetaInt ^ 4 + 8 * zetaInt ^ 3 + 8 * zetaInt + 1) * zetaInt_pow_four

private theorem span_pair_seventeen_two :
    Ideal.span {(17 : 𝓞 K), zetaInt - 2} = Ideal.span {zetaInt - 2} := by
  refine le_antisymm (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · rintro y (rfl | rfl)
    · exact seventeen_mem_span_two
    · exact Ideal.mem_span_singleton_self _
  · exact Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩

private theorem span_pair_seventeen_eight :
    Ideal.span {(17 : 𝓞 K), zetaInt - 8} = Ideal.span {zetaInt ^ 3 - 2} := by
  refine le_antisymm (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · rintro y (rfl | rfl)
    · exact seventeen_mem_span_eight
    · rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      refine ⟨zetaInt ^ 6 + 2 * zetaInt ^ 3 + 4, ?_⟩
      linear_combination (zetaInt - zetaInt ^ 5) * zetaInt_pow_four
  · exact Ideal.mem_span_pair.mpr ⟨30, zetaInt ^ 2 + 8 * zetaInt + 64, by ring⟩

private theorem span_pair_seventeen_nine :
    Ideal.span {(17 : 𝓞 K), zetaInt - 9} = Ideal.span {zetaInt ^ 7 - 2} := by
  refine le_antisymm (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · rintro y (rfl | rfl)
    · exact seventeen_mem_span_nine
    · rw [SetLike.mem_coe, show zetaInt - (9 : 𝓞 K) =
        (zetaInt ^ 7 - 2) * (-9 * zetaInt) + 17 * (-zetaInt) from by
          linear_combination (9 * zetaInt ^ 4 - 9) * zetaInt_pow_four]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
        (Ideal.mul_mem_right _ _ seventeen_mem_span_nine)
  · exact Ideal.mem_span_pair.mpr ⟨-43, -(zetaInt ^ 2 + 9 * zetaInt + 81),
      by linear_combination -zetaInt ^ 3 * zetaInt_pow_four⟩

private theorem span_pair_seventeen_fifteen :
    Ideal.span {(17 : 𝓞 K), zetaInt - 15} = Ideal.span {zetaInt ^ 5 - 2} := by
  refine le_antisymm (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · rintro y (rfl | rfl)
    · exact seventeen_mem_span_fifteen
    · rw [SetLike.mem_coe, show zetaInt - (15 : 𝓞 K) =
        (zetaInt ^ 5 - 2) * (-1) + 17 * (-1) from by
          linear_combination zetaInt * zetaInt_pow_four]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
        (Ideal.mul_mem_right _ _ seventeen_mem_span_fifteen)
  · exact Ideal.mem_span_pair.mpr ⟨-1, -1, by linear_combination -zetaInt * zetaInt_pow_four⟩

/-- `17` splits completely: `17 ≡ 1 (mod 8)`, and the roots of `X⁴ + 1` mod `17` are
`2, 8, 9, 15` (the elements of order `8` in `(ℤ/17)ˣ`). -/
theorem span_seventeen_eq :
    Ideal.span {(17 : 𝓞 K)} =
      Ideal.span {(17 : 𝓞 K), zetaInt - 2} * Ideal.span {(17 : 𝓞 K), zetaInt - 8} *
        Ideal.span {(17 : 𝓞 K), zetaInt - 9} * Ideal.span {(17 : 𝓞 K), zetaInt - 15} := by
  rw [span_pair_seventeen_two, span_pair_seventeen_eight, span_pair_seventeen_nine,
    span_pair_seventeen_fifteen, Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton,
    show (zetaInt - 2) * (zetaInt ^ 3 - 2) * (zetaInt ^ 7 - 2) * (zetaInt ^ 5 - 2) =
      (17 : 𝓞 K) from by
        linear_combination (zetaInt ^ 12 - 2 * zetaInt ^ 11 - 2 * zetaInt ^ 9 +
          3 * zetaInt ^ 8 + 4 * zetaInt ^ 6 + 5 * zetaInt ^ 4 - 8 * zetaInt ^ 3 -
          8 * zetaInt - 1) * zetaInt_pow_four]

/-- Each ideal `(17, ζ - r)` for `r ∈ {2, 8, 9, 15}` is a prime of norm `17`. -/
theorem isPrime_primeAboveSeventeen (r : ℤ) (hr : r = 2 ∨ r = 8 ∨ r = 9 ∨ r = 15) :
    (Ideal.span {(17 : 𝓞 K), zetaInt - (r : 𝓞 K)}).IsPrime := by
  have hs : ((r : ZMod 17)) ^ 4 = -1 := by
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have h := (isMaximal_span_pair 17 r hs).isPrime
  rwa [show ((17 : ℕ) : 𝓞 K) = (17 : 𝓞 K) from by norm_cast] at h

/-- **No rational prime is inert in `ℚ(ζ₈)`**: the Galois group `(ℤ/8)ˣ` has exponent `2`,
so every Frobenius has order at most `2` and every residue degree is `≤ 2 < 4`. This is a
hallmark of non-cyclic abelian extensions. -/
theorem no_inert_prime (p : ℕ) (hp : p.Prime) :
    ¬ (Ideal.span {(p : 𝓞 K)}).IsPrime := by
  intro hpr
  by_cases hp2 : p = 2
  · subst hp2
    rw [show ((2 : ℕ) : 𝓞 K) = (2 : 𝓞 K) by norm_num, span_two_eq] at hpr
    have hmem : (1 - zetaInt) ^ 4 ∈ Ideal.span {1 - zetaInt} ^ 4 := by
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    have h1 : 1 - zetaInt ∈ Ideal.span {1 - zetaInt} ^ 4 := hpr.mem_of_pow_mem 4 hmem
    have hle : Ideal.span {1 - zetaInt} ≤ Ideal.span {1 - zetaInt} ^ 4 :=
      (Ideal.span_singleton_le_iff_mem _).mpr h1
    have hd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [map_pow, absNorm_span_one_sub_zeta] at hd
    norm_num at hd
  · classical
    haveI : Fact p.Prime := ⟨hp⟩
    set P : Ideal (𝓞 K) := Ideal.span {((p : ℕ) : 𝓞 K)} with hPdef
    haveI hPp : P.IsPrime := hpr
    have hfin : Module.finrank ℤ (𝓞 K) = 4 := by
      rw [Module.finrank_eq_card_basis concreteIntegralBasis, Fintype.card_fin]
    have habs : Ideal.absNorm P = p ^ 4 := by
      rw [hPdef, Ideal.absNorm_span_singleton]
      have hcast : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ((p : ℕ) : ℤ) := by push_cast; rfl
      rw [hcast, Algebra.norm_algebraMap, hfin, Int.natAbs_pow, Int.natAbs_natCast]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at habs
    haveI : Finite ((𝓞 K) ⧸ P) :=
      Nat.finite_of_card_ne_zero (by rw [habs]; exact pow_ne_zero 4 hp.ne_zero)
    haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
    have hcardF : Fintype.card ((𝓞 K) ⧸ P) = p ^ 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact habs
    have hPbot : P ≠ ⊥ := by
      rw [hPdef, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    haveI hmax : P.IsMaximal := hPp.isMaximal hPbot
    haveI : Field ((𝓞 K) ⧸ P) := Ideal.Quotient.field P
    have hp0 : ((p : ℕ) : (𝓞 K) ⧸ P) = 0 := by
      rw [show ((p : ℕ) : (𝓞 K) ⧸ P) = Ideal.Quotient.mk P ((p : ℕ) : 𝓞 K) from
        (map_natCast (Ideal.Quotient.mk P) p).symm, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    haveI : CharP ((𝓞 K) ⧸ P) p := by
      have hd := (ringChar.spec ((𝓞 K) ⧸ P) p).mp hp0
      rcases (Nat.dvd_prime hp).mp hd with h1 | h1
      · exfalso
        have h10 : ((1 : ℕ) : (𝓞 K) ⧸ P) = 0 :=
          (ringChar.spec ((𝓞 K) ⧸ P) 1).mpr (h1 ▸ dvd_refl _)
        simp at h10
      · rw [← h1]
        exact ringChar.charP _
    have hz8 : (Ideal.Quotient.mk P zetaInt) ^ 8 = 1 := by
      rw [← map_pow, show zetaInt ^ 8 = 1 from by
        linear_combination (zetaInt ^ 4 - 1) * zetaInt_pow_four, map_one]
    have hp81 : p ^ 2 % 8 = 1 := by
      obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
      rcases Nat.even_or_odd t with ⟨u, hu⟩ | ⟨u, hu⟩ <;> subst hu <;> subst ht <;>
        ring_nf <;> omega
    have hzp : (Ideal.Quotient.mk P zetaInt) ^ p ^ 2 = Ideal.Quotient.mk P zetaInt := by
      obtain ⟨k, hk⟩ : ∃ k, p ^ 2 = 8 * k + 1 := ⟨p ^ 2 / 8, by omega⟩
      rw [hk, pow_add, pow_mul, hz8, one_pow, one_mul, pow_one]
    have hψeq : ∀ w : (𝓞 K) ⧸ P,
        (((frobenius ((𝓞 K) ⧸ P) p).comp (frobenius ((𝓞 K) ⧸ P) p)).toIntAlgHom) w =
          w ^ p ^ 2 := by
      intro w
      change frobenius _ p (frobenius _ p w) = w ^ p ^ 2
      rw [frobenius_def, frobenius_def, ← pow_mul, ← pow_two]
    have hfrob : ∀ x : (𝓞 K) ⧸ P, x ^ p ^ 2 = x := by
      intro x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨q, -, hq⟩ := zeta_isPrimitiveRoot.integralPowerBasis.exists_eq_aeval y
      rw [gen_eq_zetaInt] at hq
      rw [hq]
      have hcomm := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ P) zetaInt q
      rw [Ideal.Quotient.mkₐ_eq_mk] at hcomm
      rw [← hcomm, ← hψeq, ← Polynomial.aeval_algHom_apply, hψeq, hzp]
    set g : Polynomial ((𝓞 K) ⧸ P) := Polynomial.X ^ p ^ 2 - Polynomial.X with hgdef
    have hdeg : g.natDegree = p ^ 2 := by
      rw [hgdef]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow _
      · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
        exact Nat.one_lt_pow (by norm_num) hp.one_lt
    have hgne : g ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hdeg
      have := Nat.one_lt_pow (n := 2) (by norm_num : (2 : ℕ) ≠ 0) hp.one_lt
      omega
    have hsub : (Finset.univ : Finset ((𝓞 K) ⧸ P)) ⊆ g.roots.toFinset := by
      intro x _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hgne]
      change g.eval x = 0
      rw [hgdef]
      simp [hfrob x]
    have hcontr : p ^ 4 ≤ p ^ 2 := by
      calc p ^ 4 = Fintype.card ((𝓞 K) ⧸ P) := hcardF.symm
        _ = (Finset.univ : Finset ((𝓞 K) ⧸ P)).card := Finset.card_univ.symm
        _ ≤ g.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ Multiset.card g.roots := g.roots.toFinset_card_le
        _ ≤ g.natDegree := Polynomial.card_roots' g
        _ = p ^ 2 := hdeg
    have hlt : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

/-- The splitting law for `ℚ(ζ₈)`: a prime `p` splits completely iff `p ≡ 1 (mod 8)`. -/
theorem splits_completely_iff (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧ Ideal.absNorm P = p) ↔
      p % 8 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨P, hPprime, hle, habs⟩
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at habs
    haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [habs]; exact hp.ne_zero)
    haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
    have hcard' : Fintype.card ((𝓞 K) ⧸ P) = p := by rw [← Nat.card_eq_fintype_card]; exact habs
    let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) hp hcard'
    obtain ⟨s, hs⟩ := e.surjective (Ideal.Quotient.mk P zetaInt)
    have hs4 : s ^ 4 = (-1 : ZMod p) := by
      apply e.injective
      rw [map_pow, hs, ← map_pow (Ideal.Quotient.mk P), zetaInt_pow_four, map_neg, map_one,
        map_neg, map_one]
    have hne1 : (-1 : ZMod p) ≠ 1 := by
      intro h
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -h
      have hdvd := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0] at hs4
      exact one_ne_zero (by linear_combination hs4)
    have hu8 : (Units.mk0 s hs0) ^ 8 = 1 := by
      ext
      change s ^ 8 = 1
      rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hs4]
      ring
    have hu4 : (Units.mk0 s hs0) ^ 4 ≠ 1 := by
      intro h
      have hval : s ^ 4 = 1 := by
        have hc := congrArg Units.val h
        simpa using hc
      rw [hs4] at hval
      exact hne1 hval
    have horder : orderOf (Units.mk0 s hs0) = 8 := by
      have hdvd : orderOf (Units.mk0 s hs0) ∣ 8 := orderOf_dvd_of_pow_eq_one hu8
      have hnd4 : ¬ orderOf (Units.mk0 s hs0) ∣ 4 := fun h =>
        hu4 (orderOf_dvd_iff_pow_eq_one.mp h)
      obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (show orderOf (Units.mk0 s hs0) ∣ 2 ^ 3 from hdvd)
      have hk3 : k = 3 := by
        by_contra hne
        exact hnd4 (hkeq ▸ (pow_dvd_pow 2 (by omega) : (2 : ℕ) ^ k ∣ 2 ^ 2))
      rw [hkeq, hk3]
      norm_num
    have hdvd_card : (8 : ℕ) ∣ p - 1 := by
      have h := orderOf_dvd_natCard (Units.mk0 s hs0)
      rw [horder, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime hp] at h
      exact h
    have h2le := hp.two_le
    obtain ⟨m, hm⟩ := hdvd_card
    omega
  · intro hmod
    have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hog : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
    have h2le := hp.two_le
    obtain ⟨m, hm⟩ : (8 : ℕ) ∣ p - 1 := ⟨(p - 1) / 8, by omega⟩
    have hm0 : m ≠ 0 := by omega
    have hou : orderOf (g ^ m) = 8 := by
      rw [orderOf_pow, hog, hm]
      have hgcd : Nat.gcd (8 * m) m = m := Nat.gcd_eq_right ⟨8, by ring⟩
      rw [hgcd, Nat.mul_div_assoc 8 (dvd_refl m), Nat.div_self (show 0 < m by omega), mul_one]
    have hu8 : (g ^ m) ^ 8 = 1 := by
      rw [← hou]
      exact pow_orderOf_eq_one _
    have hu4ne : (g ^ m) ^ 4 ≠ 1 := by
      intro h
      have hd := orderOf_dvd_of_pow_eq_one h
      rw [hou] at hd
      norm_num at hd
    have hval4 : ((g ^ m : (ZMod p)ˣ) : ZMod p) ^ 4 = -1 := by
      have hv8 : ((g ^ m : (ZMod p)ˣ) : ZMod p) ^ 8 = 1 := by
        have hc := congrArg Units.val hu8
        simpa using hc
      have hsq : ((g ^ m : (ZMod p)ˣ) : ZMod p) ^ 4 *
          ((g ^ m : (ZMod p)ˣ) : ZMod p) ^ 4 = 1 := by
        rw [← pow_add]
        exact hv8
      rcases mul_self_eq_one_iff.mp hsq with h | h
      · exfalso
        apply hu4ne
        ext
        simpa using h
      · exact h
    set r : ℤ := (((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ) with hr_def
    have hr : ((r : ZMod p)) ^ 4 = -1 := by
      have hcast : ((r : ℤ) : ZMod p) = ((g ^ m : (ZMod p)ˣ) : ZMod p) := by
        rw [hr_def]
        push_cast
        exact ZMod.natCast_rightInverse _
      rw [hcast]
      exact hval4
    refine ⟨Ideal.span {((p : ℕ) : 𝓞 K), zetaInt - (r : 𝓞 K)},
      (isMaximal_span_pair p r hr).isPrime, ?_, absNorm_span_pair p r hr⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span (by simp)

/-- A rational prime `p` ramifies in `ℚ(ζ₈)` iff `p = 2`, i.e. iff `p` divides the
discriminant `256`. -/
theorem ramified_iff_eq_two (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 2 := by
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
    have hfin : Module.finrank ℤ (𝓞 K) = 4 := by
      rw [Module.finrank_eq_card_basis concreteIntegralBasis, Fintype.card_fin]
    have habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 4 := by
      rw [Ideal.absNorm_span_singleton]
      have hcast : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ((p : ℕ) : ℤ) := by push_cast; rfl
      rw [hcast, Algebra.norm_algebraMap, hfin, Int.natAbs_pow, Int.natAbs_natCast]
    have habsPp4 : Ideal.absNorm P ∣ p ^ 4 :=
      habsp ▸ Ideal.absNorm_dvd_absNorm_of_le hple
    obtain ⟨k, hk4, hkeq⟩ := (Nat.dvd_prime_pow hp).mp habsPp4
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hkeq
      exact hP.ne_top (Ideal.absNorm_eq_one_iff.mp hkeq)
    have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) =
        Ideal.span {((p : ℕ) : 𝓞 K)} := by
      rw [Ideal.map_span, Set.image_singleton]
      norm_num
    have hle2' : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 2 := by
      rw [hmap]; exact hle2
    have hno5 : ¬ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 5 := by
      intro h5
      rw [hmap] at h5
      have hd := Ideal.absNorm_dvd_absNorm_of_le h5
      rw [map_pow, habsp, hkeq, ← pow_mul] at hd
      rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
      omega
    have hidx : Ideal.ramificationIdx (Ideal.span {((p : ℕ) : ℤ)}) P ≠ 1 := by
      by_cases h3 : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 3
      · by_cases h4 : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 4
        · rw [Ideal.ramificationIdx_spec h4 hno5]
          norm_num
        · rw [Ideal.ramificationIdx_spec h3 h4]
          norm_num
      · rw [Ideal.ramificationIdx_spec hle2' h3]
        norm_num
    have hund : Ideal.under ℤ P = Ideal.span {((p : ℕ) : ℤ)} := by
      have hmem : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
        rw [Ideal.under, Ideal.mem_comap]
        have hcast2 : algebraMap ℤ (𝓞 K) ((p : ℕ) : ℤ) = ((p : ℕ) : 𝓞 K) := by push_cast; rfl
        rw [hcast2]
        exact hpmemP
      have hle : Ideal.span {((p : ℕ) : ℤ)} ≤ Ideal.under ℤ P := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hmem
      have hprime : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp hp)
      have hbot : Ideal.span {((p : ℕ) : ℤ)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hp.ne_zero
      have hnetop : Ideal.under ℤ P ≠ ⊤ := by
        intro h
        have h1 : (1 : ℤ) ∈ Ideal.under ℤ P := h ▸ Submodule.mem_top
        rw [Ideal.under, Ideal.mem_comap, map_one] at h1
        exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
      exact ((hprime.isMaximal hbot).eq_of_le hnetop hle).symm
    have hunram : ¬ Algebra.IsUnramifiedAt ℤ P := by
      rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot, hund]
      exact hidx
    have hPdiff : P ∣ differentIdeal ℤ (𝓞 K) := dvd_differentIdeal_iff.mpr hunram
    have habsP256 : Ideal.absNorm P ∣ 256 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq] at h
      simpa using h
    have hpdvd : p ∣ 256 := (hkeq ▸ dvd_pow_self p hk0).trans habsP256
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 8 by norm_num; exact hpdvd)
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp2
  · rintro rfl
    refine ⟨Ideal.span {1 - zetaInt}, isPrime_span_one_sub_zeta, ?_⟩
    have hcast : ((2 : ℕ) : 𝓞 K) = (2 : 𝓞 K) := by norm_num
    rw [hcast, span_two_eq]
    exact Ideal.pow_le_pow_right (by norm_num)


end XYin.NumberField.New.CyclotomicEight
