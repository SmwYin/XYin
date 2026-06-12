import XYin.NumberField.FieldExamples.CyclotomicFive.RingOfIntegers

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace XYin.NumberField.New.CyclotomicFive

private theorem zetaInt_sum : 1 + zetaInt + zetaInt ^ 2 + zetaInt ^ 3 + zetaInt ^ 4 = 0 :=
  Subtype.ext (by push_cast [zetaInt]; exact zeta_sum_eq_zero)

/-! ## 3. Discriminant -/

/-- The number-field discriminant of `ℚ(ζ₅)` is `125 = 5³` (for an odd prime `p` the
discriminant of `ℚ(ζ_p)` is `(-1)^((p-1)/2) p^(p-2)`). In particular `5` is the only
ramified prime, cf. `ramified_iff_eq_five`. -/
theorem numberField_discr_eq : NumberField.discr K = (125 : ℤ) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [IsCyclotomicExtension.Rat.discr_prime 5 K]
  norm_num

/-- The discriminant of the explicit integral basis `1, ζ, ζ², ζ³` is `125`. -/
theorem concreteIntegralBasis_discr :
    Algebra.discr ℤ concreteIntegralBasis = (125 : ℤ) := by
  simpa [numberField_discr_eq] using
    (NumberField.discr_eq_discr (K := K) concreteIntegralBasis)

section PrivateMachinery

private theorem coe_zetaInt : algebraMap (𝓞 K) K zetaInt = ζ := rfl

private theorem gen_eq_zetaInt : zeta_isPrimitiveRoot.integralPowerBasis.gen = zetaInt := by
  rw [zeta_isPrimitiveRoot.integralPowerBasis_gen]; rfl

/-- Private forward copy of `sigmaTwo` (the public definition appears in section 9). -/
private noncomputable def sig2 : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 2 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private noncomputable def sig3 : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 3 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private noncomputable def sig4 : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (zeta_isPrimitiveRoot.pow_of_coprime 4 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private theorem sig2_zeta : sig2 ζ = ζ ^ 2 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 2 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private theorem sig3_zeta : sig3 ζ = ζ ^ 3 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 3 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private theorem sig4_zeta : sig4 ζ = ζ ^ 4 :=
  IsCyclotomicExtension.fromZetaAut_spec (zeta_isPrimitiveRoot.pow_of_coprime 4 (by norm_num))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

private theorem autEq' (σ : K ≃ₐ[ℚ] K) : σ = 1 ∨ σ = sig2 ∨ σ = sig3 ∨ σ = sig4 := by
  have hval : ∀ t : (ZMod 5)ˣ, (t : ZMod 5).val = 1 ∨ (t : ZMod 5).val = 2 ∨
      (t : ZMod 5).val = 3 ∨ (t : ZMod 5).val = 4 := by decide
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
  · exact Or.inr (Or.inl (hext sig2 (by rw [← hspec, sig2_zeta])))
  · exact Or.inr (Or.inr (Or.inl (hext sig3 (by rw [← hspec, sig3_zeta]))))
  · exact Or.inr (Or.inr (Or.inr (hext sig4 (by rw [← hspec, sig4_zeta]))))

/-- The product of the four Galois conjugates computes the field norm. -/
private theorem prod_aut_apply (x : K) :
    ∏ σ : K ≃ₐ[ℚ] K, σ x = x * sig2 x * sig3 x * sig4 x := by
  classical
  have hne : ∀ (i j : ℕ) (σ τ : K ≃ₐ[ℚ] K), i < 5 → j < 5 → i ≠ j →
      σ ζ = ζ ^ i → τ ζ = ζ ^ j → σ ≠ τ := fun i j σ τ hi hj hij hσ hτ hστ =>
    hij (zeta_isPrimitiveRoot.pow_inj hi hj (by rw [← hσ, ← hτ, hστ]))
  have hid : (1 : K ≃ₐ[ℚ] K) ζ = ζ ^ 1 := by rw [pow_one]; rfl
  have h1 : (1 : K ≃ₐ[ℚ] K) ≠ sig2 :=
    hne 1 2 _ _ (by norm_num) (by norm_num) (by norm_num) hid sig2_zeta
  have h2 : (1 : K ≃ₐ[ℚ] K) ≠ sig3 :=
    hne 1 3 _ _ (by norm_num) (by norm_num) (by norm_num) hid sig3_zeta
  have h3 : (1 : K ≃ₐ[ℚ] K) ≠ sig4 :=
    hne 1 4 _ _ (by norm_num) (by norm_num) (by norm_num) hid sig4_zeta
  have h4 : sig2 ≠ sig3 := hne 2 3 _ _ (by norm_num) (by norm_num) (by norm_num)
    sig2_zeta sig3_zeta
  have h5 : sig2 ≠ sig4 := hne 2 4 _ _ (by norm_num) (by norm_num) (by norm_num)
    sig2_zeta sig4_zeta
  have h6 : sig3 ≠ sig4 := hne 3 4 _ _ (by norm_num) (by norm_num) (by norm_num)
    sig3_zeta sig4_zeta
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, sig2, sig3, sig4} := by
    refine (Finset.eq_univ_iff_forall.mpr fun σ => ?_).symm
    rcases autEq' σ with h | h | h | h <;> simp [h]
  rw [huniv, Finset.prod_insert (by simp [h1, h2, h3]), Finset.prod_insert (by simp [h4, h5]),
    Finset.prod_pair h6]
  change x * (sig2 x * (sig3 x * sig4 x)) = _
  ring

/-- Computing integral norms via the four Galois conjugates. -/
private theorem intNorm_eq (x : 𝓞 K) (n : ℤ)
    (h : algebraMap (𝓞 K) K x * sig2 (algebraMap (𝓞 K) K x) *
      sig3 (algebraMap (𝓞 K) K x) * sig4 (algebraMap (𝓞 K) K x) = (n : K)) :
    Algebra.norm ℤ x = n := by
  haveI := IsCyclotomicExtension.isGalois {5} ℚ K
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

private theorem minpoly_gen_eq :
    minpoly ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen =
      Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.C 1 := by
  set q : Polynomial ℤ := Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 +
    Polynomial.X + Polynomial.C 1 with hq
  have hint : IsIntegral ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen :=
    zeta_isPrimitiveRoot.integralPowerBasis.isIntegral_gen
  have hdvd : minpoly ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen ∣ q := by
    refine minpoly.isIntegrallyClosed_dvd hint ?_
    rw [gen_eq_zetaInt, hq]
    simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
    linear_combination zetaInt_sum
  have hmonic := minpoly.monic hint
  have hdeg : (minpoly ℤ zeta_isPrimitiveRoot.integralPowerBasis.gen).natDegree = 4 := by
    rw [zeta_isPrimitiveRoot.integralPowerBasis.natDegree_minpoly,
      zeta_isPrimitiveRoot.integralPowerBasis_dim]
    rfl
  have hXmonic : q.Monic := by
    rw [hq]
    monicity!
  obtain ⟨c, hc⟩ := hdvd
  have hcmonic : c.Monic := hmonic.of_mul_monic_left (hc ▸ hXmonic)
  have hdegc : c.natDegree = 0 := by
    have h4 : q.natDegree = 4 := by
      rw [hq]
      compute_degree!
    have hcong := congrArg Polynomial.natDegree hc
    rw [h4, Polynomial.natDegree_mul (minpoly.ne_zero hint) hcmonic.ne_zero, hdeg] at hcong
    omega
  rw [hc, Polynomial.eq_one_of_monic_natDegree_zero hcmonic hdegc, mul_one]

/-- Reduction `𝓞 K → 𝔽_p` sending `ζ ↦ r`, for `r` a root of `Φ₅` mod `p`. -/
private noncomputable def residueHom (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 4 + ((r : ZMod p)) ^ 3 + ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    𝓞 K →ₐ[ℤ] ZMod p :=
  zeta_isPrimitiveRoot.integralPowerBasis.lift ((r : ℤ) : ZMod p)
    (by
      rw [minpoly_gen_eq]
      simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
      linear_combination hr)

private theorem residueHom_zetaInt (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 4 + ((r : ZMod p)) ^ 3 + ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    residueHom p r hr zetaInt = (r : ZMod p) := by
  rw [← gen_eq_zetaInt]
  exact zeta_isPrimitiveRoot.integralPowerBasis.lift_gen ((r : ℤ) : ZMod p) _

private theorem ker_residueHom (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 4 + ((r : ZMod p)) ^ 3 + ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
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

private theorem residueHom_surjective (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 4 + ((r : ZMod p)) ^ 3 + ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    Function.Surjective (residueHom p r hr) := by
  intro z
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective z
  exact ⟨((m : ℤ) : 𝓞 K), by rw [map_intCast]; exact hm⟩

private theorem isMaximal_span_pair (p : ℕ) [Fact p.Prime] (r : ℤ)
    (hr : ((r : ZMod p)) ^ 4 + ((r : ZMod p)) ^ 3 + ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    (Ideal.span {(p : 𝓞 K), zetaInt - (r : 𝓞 K)}).IsMaximal := by
  rw [← ker_residueHom p r hr]
  exact RingHom.ker_isMaximal_of_surjective _ (residueHom_surjective p r hr)

private theorem absNorm_span_pair (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 4 + ((r : ZMod p)) ^ 3 + ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K), zetaInt - (r : 𝓞 K)}) = p := by
  rw [← ker_residueHom p r hr, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (residueHom_surjective p r hr)).toEquiv]
  exact Nat.card_zmod p

/-- Nonzero ideals with equal absolute norms and one inclusion are equal. -/
private theorem eq_of_le_of_absNorm_eq {I J : Ideal (𝓞 K)} (hle : I ≤ J) {n : ℕ}
    (hI : Ideal.absNorm I = n) (hJ : Ideal.absNorm J = n) (hn : n ≠ 0) : I = J := by
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hmul := _root_.map_mul Ideal.absNorm J C
  rw [← hC, hI, hJ] at hmul
  have hC1 : Ideal.absNorm C = 1 :=
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
      (by rw [mul_one]; exact hmul)).symm
  rw [hC, Ideal.absNorm_eq_one_iff.mp hC1, Ideal.mul_top]

end PrivateMachinery

/-! ## 4. Norms of distinguished elements -/

/-- The norm of `1 - ζ` is `Φ₅(1) = 5`: the standard generator of the unique prime above
`5`. -/
theorem norm_one_sub_zeta : Algebra.norm ℚ (1 - ζ) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := zeta_isPrimitiveRoot.sub_one_norm_isPrimePow
    ((by norm_num : Nat.Prime 5).isPrimePow)
    (Polynomial.cyclotomic.irreducible_rat (by norm_num)) (by norm_num)
  have hneg : (1 : K) - ζ = -(ζ - 1) := by ring
  have hnormneg : Algebra.norm ℚ (-(ζ - 1)) = Algebra.norm ℚ (ζ - 1) := by
    rw [show -(ζ - 1) = (-1 : K) * (ζ - 1) by ring, map_mul,
      show (-1 : K) = algebraMap ℚ K (-1) by norm_num, Algebra.norm_algebraMap,
      degree_eq_four]
    norm_num
  rw [hneg, hnormneg, h, show Nat.minFac 5 = 5 by norm_num]
  norm_num

/-- The norm of `1 + ζ` is `Φ₅(-1) = 1`: hence `1 + ζ` is a unit of `ℤ[ζ]` (a *cyclotomic
unit*). -/
theorem norm_one_add_zeta : Algebra.norm ℚ (1 + ζ) = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h2 : IsPrimitiveRoot (ζ ^ 2) 5 := zeta_isPrimitiveRoot.pow_of_coprime 2 (by norm_num)
  have hn2 : Algebra.norm ℚ (1 - ζ ^ 2) = 5 := by
    have h := h2.sub_one_norm_isPrimePow ((by norm_num : Nat.Prime 5).isPrimePow)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num)) (by norm_num)
    have hneg : (1 : K) - ζ ^ 2 = -(ζ ^ 2 - 1) := by ring
    have hnormneg : Algebra.norm ℚ (-(ζ ^ 2 - 1)) = Algebra.norm ℚ (ζ ^ 2 - 1) := by
      rw [show -(ζ ^ 2 - 1) = (-1 : K) * (ζ ^ 2 - 1) by ring, map_mul,
        show (-1 : K) = algebraMap ℚ K (-1) by norm_num, Algebra.norm_algebraMap,
        degree_eq_four]
      norm_num
    rw [hneg, hnormneg, h, show Nat.minFac 5 = 5 by norm_num]
    norm_num
  have hfact : (1 : K) - ζ ^ 2 = (1 - ζ) * (1 + ζ) := by ring
  rw [hfact, map_mul, norm_one_sub_zeta] at hn2
  linarith

/-- The quartic norm form of `ℚ(ζ₅)` in the integral basis `1, ζ, ζ², ζ³`. -/
def normForm {R : Type*} [CommRing R] (a b c d : R) : R :=
  a ^ 4 - a ^ 3 * b - a ^ 3 * c - a ^ 3 * d +
    a ^ 2 * b ^ 2 + 2 * a ^ 2 * b * c + 2 * a ^ 2 * b * d +
    a ^ 2 * c ^ 2 - 3 * a ^ 2 * c * d + a ^ 2 * d ^ 2 -
    a * b ^ 3 - 3 * a * b ^ 2 * c + 2 * a * b ^ 2 * d +
    2 * a * b * c ^ 2 - a * b * c * d - 3 * a * b * d ^ 2 -
    a * c ^ 3 + 2 * a * c ^ 2 * d + 2 * a * c * d ^ 2 - a * d ^ 3 +
    b ^ 4 - b ^ 3 * c - b ^ 3 * d + b ^ 2 * c ^ 2 +
    2 * b ^ 2 * c * d + b ^ 2 * d ^ 2 - b * c ^ 3 -
    3 * b * c ^ 2 * d + 2 * b * c * d ^ 2 - b * d ^ 3 +
    c ^ 4 - c ^ 3 * d + c ^ 2 * d ^ 2 - c * d ^ 3 + d ^ 4

/-- The field norm of `a + bζ + cζ² + dζ³` is the quartic norm form above. -/
theorem norm_eq_normForm (a b c d : ℚ) :
    Algebra.norm ℚ
        (a • (1 : K) + b • ζ + c • ζ ^ 2 + d • ζ ^ 3) =
      normForm a b c d := by
  have hx : a • (1 : K) + b • ζ + c • ζ ^ 2 + d • ζ ^ 3 =
      (a : K) + (b : K) * ζ + (c : K) * ζ ^ 2 + (d : K) * ζ ^ 3 := by
    simp [Algebra.smul_def]
  rw [hx]
  have e2 : sig2 ((a : K) + (b : K) * ζ + (c : K) * ζ ^ 2 + (d : K) * ζ ^ 3) =
      (a : K) - c + (d - c) * ζ + (b - c) * ζ ^ 2 - c * ζ ^ 3 := by
    simp only [map_add, map_mul, map_pow, sig2_zeta]
    rw [show sig2 (a : K) = (a : K) by simp,
      show sig2 (b : K) = (b : K) by simp,
      show sig2 (c : K) = (c : K) by simp,
      show sig2 (d : K) = (d : K) by simp]
    have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
      linear_combination zeta_sum_eq_zero
    have h6 : ζ ^ 6 = ζ := by linear_combination ζ * zeta_pow_five
    rw [show (ζ ^ 2) ^ 2 = ζ ^ 4 by ring,
      show (ζ ^ 2) ^ 3 = ζ ^ 6 by ring, h4, h6]
    ring
  have e3 : sig3 ((a : K) + (b : K) * ζ + (c : K) * ζ ^ 2 + (d : K) * ζ ^ 3) =
      (a : K) - d + (c - d) * ζ - d * ζ ^ 2 + (b - d) * ζ ^ 3 := by
    simp only [map_add, map_mul, map_pow, sig3_zeta]
    rw [show sig3 (a : K) = (a : K) by simp,
      show sig3 (b : K) = (b : K) by simp,
      show sig3 (c : K) = (c : K) by simp,
      show sig3 (d : K) = (d : K) by simp]
    have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
      linear_combination zeta_sum_eq_zero
    have h6 : ζ ^ 6 = ζ := by linear_combination ζ * zeta_pow_five
    have h9 : ζ ^ 9 = ζ ^ 4 := by linear_combination ζ ^ 4 * zeta_pow_five
    rw [show (ζ ^ 3) ^ 2 = ζ ^ 6 by ring,
      show (ζ ^ 3) ^ 3 = ζ ^ 9 by ring, h6, h9, h4]
    ring
  have e4 : sig4 ((a : K) + (b : K) * ζ + (c : K) * ζ ^ 2 + (d : K) * ζ ^ 3) =
      (a : K) - b - b * ζ + (d - b) * ζ ^ 2 + (c - b) * ζ ^ 3 := by
    simp only [map_add, map_mul, map_pow, sig4_zeta]
    rw [show sig4 (a : K) = (a : K) by simp,
      show sig4 (b : K) = (b : K) by simp,
      show sig4 (c : K) = (c : K) by simp,
      show sig4 (d : K) = (d : K) by simp]
    have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
      linear_combination zeta_sum_eq_zero
    have h8 : ζ ^ 8 = ζ ^ 3 := by linear_combination ζ ^ 3 * zeta_pow_five
    have h7 : ζ ^ 7 = ζ ^ 2 := by linear_combination ζ ^ 2 * zeta_pow_five
    have h12 : ζ ^ 12 = ζ ^ 7 := by linear_combination ζ ^ 7 * zeta_pow_five
    rw [show (ζ ^ 4) ^ 2 = ζ ^ 8 by ring,
      show (ζ ^ 4) ^ 3 = ζ ^ 12 by ring, h4, h8, h12, h7]
    ring
  haveI := IsCyclotomicExtension.isGalois {5} ℚ K
  apply (algebraMap ℚ K).injective
  rw [Algebra.norm_eq_prod_automorphisms, prod_aut_apply, e2, e3, e4]
  let A : K := a ^ 2 - a * b + b ^ 2 - b * c + c ^ 2 - c * d + d ^ 2
  let B : K := -c * d + b * d - b * c + a * d + a * c - a * b
  let C : K := a ^ 2 - a * c - a * d + b ^ 2 - b * d + c ^ 2 + d ^ 2
  let T : K := ζ ^ 2 + ζ ^ 3
  have hpair14 : ((a : K) + b * ζ + c * ζ ^ 2 + d * ζ ^ 3) *
      (a - b - b * ζ + (d - b) * ζ ^ 2 + (c - b) * ζ ^ 3) = A + B * T := by
    dsimp [A, B, T]
    have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
      linear_combination zeta_sum_eq_zero
    have h6 : ζ ^ 6 = ζ := by linear_combination ζ * zeta_pow_five
    ring_nf
    rw [zeta_pow_five, h6, h4]
    ring
  have hpair23 : ((a : K) - c + (d - c) * ζ + (b - c) * ζ ^ 2 - c * ζ ^ 3) *
      (a - d + (c - d) * ζ - d * ζ ^ 2 + (b - d) * ζ ^ 3) = C - B * T := by
    dsimp [B, C, T]
    have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
      linear_combination zeta_sum_eq_zero
    have h6 : ζ ^ 6 = ζ := by linear_combination ζ * zeta_pow_five
    ring_nf
    rw [zeta_pow_five, h6, h4]
    ring
  have hT : T ^ 2 = 1 - T := by
    dsimp [T]
    have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
      linear_combination zeta_sum_eq_zero
    have h6 : ζ ^ 6 = ζ := by linear_combination ζ * zeta_pow_five
    ring_nf
    rw [zeta_pow_five, h6, h4]
    ring
  have hlin : C - A + B = 0 := by
    dsimp [A, B, C]
    ring
  have hmain : (A + B * T) * (C - B * T) = A * C - B ^ 2 := by
    calc
      (A + B * T) * (C - B * T) =
          A * C - B ^ 2 + B * T * (C - A + B) - B ^ 2 * (T ^ 2 - (1 - T)) := by
        ring
      _ = A * C - B ^ 2 := by
        rw [hlin, hT]
        ring
  have hACB : A * C - B ^ 2 = algebraMap ℚ K (normForm a b c d) := by
    dsimp [A, B, C, normForm]
    norm_num
    ring
  rw [show ((a : K) + b * ζ + c * ζ ^ 2 + d * ζ ^ 3) *
        ((a - c) + (d - c) * ζ + (b - c) * ζ ^ 2 - c * ζ ^ 3) *
        ((a - d) + (c - d) * ζ - d * ζ ^ 2 + (b - d) * ζ ^ 3) *
        ((a - b) - b * ζ + (d - b) * ζ ^ 2 + (c - b) * ζ ^ 3) =
      (((a : K) + b * ζ + c * ζ ^ 2 + d * ζ ^ 3) *
        ((a - b) - b * ζ + (d - b) * ζ ^ 2 + (c - b) * ζ ^ 3)) *
      (((a - c) + (d - c) * ζ + (b - c) * ζ ^ 2 - c * ζ ^ 3) *
        ((a - d) + (c - d) * ζ - d * ζ ^ 2 + (b - d) * ζ ^ 3)) by ring]
  rw [hpair14, hpair23, hmain, hACB]

/-- The integral norm of `a + bζ + cζ² + dζ³` is the same quartic form over `ℤ`. -/
theorem intNorm_eq_normForm (a b c d : ℤ) :
    Algebra.norm ℤ
        (a • (1 : 𝓞 K) + b • zetaInt + c • zetaInt ^ 2 + d • zetaInt ^ 3) =
      normForm a b c d := by
  let x : 𝓞 K := a • (1 : 𝓞 K) + b • zetaInt + c • zetaInt ^ 2 + d • zetaInt ^ 3
  change Algebra.norm ℤ x = normForm a b c d
  have hx : algebraMap (𝓞 K) K x =
      (a : ℚ) • (1 : K) + (b : ℚ) • ζ + (c : ℚ) • ζ ^ 2 + (d : ℚ) • ζ ^ 3 := by
    simp [x, coe_zetaInt, Algebra.smul_def]
  have hcoe : ((Algebra.norm ℤ x : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap (𝓞 K) K x) :=
    Algebra.coe_norm_int x
  rw [hx, norm_eq_normForm] at hcoe
  norm_num [normForm] at hcoe ⊢
  exact_mod_cast hcoe

/-- The unit equation in `ℤ[ζ₅]`, written in the integral basis `1, ζ, ζ², ζ³`. -/
theorem isUnit_iff_normForm (a b c d : ℤ) :
    IsUnit (a • (1 : 𝓞 K) + b • zetaInt + c • zetaInt ^ 2 + d • zetaInt ^ 3) ↔
      (normForm a b c d).natAbs = 1 := by
  rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm, ← Algebra.coe_norm_int,
    intNorm_eq_normForm]
  constructor
  · intro h
    apply Nat.cast_injective (R := ℚ)
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact h
  · intro h
    have hq : ((normForm a b c d).natAbs : ℚ) = 1 := by exact_mod_cast h
    rwa [Nat.cast_natAbs, Int.cast_abs] at hq

/-! ## 5. Splitting of primes -/

/-- `5` is totally ramified: `(5) = (1 - ζ)⁴` as ideals of `𝓞 K` — ramification index
`e = 4` equals the full degree. -/
theorem span_five_eq : Ideal.span {(5 : 𝓞 K)} = Ideal.span {1 - zetaInt} ^ 4 := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
  refine ⟨⟨-zetaInt ^ 3 + zetaInt ^ 2 - zetaInt, zetaInt ^ 4 + 2 * zetaInt ^ 3 + zetaInt ^ 2,
    by linear_combination (-zetaInt ^ 3) * zetaInt_sum + zetaInt_pow_five,
    by linear_combination (-zetaInt ^ 3) * zetaInt_sum + zetaInt_pow_five⟩, ?_⟩
  change (5 : 𝓞 K) * (-zetaInt ^ 3 + zetaInt ^ 2 - zetaInt) = (1 - zetaInt) ^ 4
  linear_combination -zetaInt_sum

private theorem span_one_sub_zetaInt_eq_pair :
    Ideal.span {1 - zetaInt} = Ideal.span {((5 : ℕ) : 𝓞 K), zetaInt - ((1 : ℤ) : 𝓞 K)} := by
  refine le_antisymm ((Ideal.span_singleton_le_iff_mem _).mpr ?_) (Ideal.span_le.mpr ?_)
  · refine Ideal.mem_span_pair.mpr ⟨0, -1, ?_⟩
    push_cast
    ring
  · rintro y (rfl | rfl)
    · have h5 : ((5 : ℕ) : 𝓞 K) ∈ Ideal.span {(5 : 𝓞 K)} := by
        rw [Ideal.mem_span_singleton]
        exact ⟨1, by push_cast; ring⟩
      rw [span_five_eq] at h5
      exact Ideal.pow_le_self (by norm_num) h5
    · rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      exact ⟨-1, by push_cast; ring⟩

/-- `(1 - ζ)` is a prime ideal — the unique prime of `𝓞 K` above `5`. -/
theorem isPrime_span_one_sub_zeta : (Ideal.span {1 - zetaInt}).IsPrime := by
  have hr : ((1 : ℤ) : ZMod 5) ^ 4 + ((1 : ℤ) : ZMod 5) ^ 3 + ((1 : ℤ) : ZMod 5) ^ 2 +
      ((1 : ℤ) : ZMod 5) + 1 = 0 := by decide
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [span_one_sub_zetaInt_eq_pair]
  exact (isMaximal_span_pair 5 1 hr).isPrime

/-- The prime `(1 - ζ)` above `5` has norm `5` (residue degree `f = 1`). -/
theorem absNorm_span_one_sub_zeta : Ideal.absNorm (Ideal.span {1 - zetaInt}) = 5 := by
  rw [span_one_sub_zetaInt_eq_pair]
  exact absNorm_span_pair 5 1 (by decide)

/-- The inert prime `(2)` has norm `2⁴ = 16` (residue degree `f = 4`). -/
private theorem absNorm_span_two' : Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 16 := by
  have hfin : Module.finrank ℤ (𝓞 K) = 4 := by
    rw [Module.finrank_eq_card_basis concreteIntegralBasis, Fintype.card_fin]
  rw [Ideal.absNorm_span_singleton,
    show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 from (map_ofNat _ 2).symm,
    Algebra.norm_algebraMap, hfin]
  rfl

/-- `2` is inert in `ℚ(ζ₅)`: `2` has order `4` in `(ℤ/5)ˣ`, so `Φ₅` is irreducible mod `2`. -/
theorem isPrime_span_two : (Ideal.span {(2 : 𝓞 K)}).IsPrime := by
  have htop : Ideal.span {(2 : 𝓞 K)} ≠ ⊤ := by
    intro h
    have h16 := absNorm_span_two'
    rw [h, Ideal.absNorm_top] at h16
    norm_num at h16
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ htop
  haveI := hMmax
  letI : Field ((𝓞 K) ⧸ M) := Ideal.Quotient.field M
  have hdvd : Ideal.absNorm M ∣ 16 :=
    absNorm_span_two' ▸ Ideal.absNorm_dvd_absNorm_of_le hMle
  have h2mem : (2 : 𝓞 K) ∈ M := hMle (Ideal.mem_span_singleton_self _)
  set ω : (𝓞 K) ⧸ M := Ideal.Quotient.mk M zetaInt with hω
  have hω5 : ω ^ 5 = 1 := by
    rw [hω, ← map_pow, zetaInt_pow_five, map_one]
  have hω1 : ω ≠ 1 := by
    intro h1
    have hs := congrArg (Ideal.Quotient.mk M) zetaInt_sum
    rw [map_add, map_add, map_add, map_add, map_one, map_pow, map_pow, map_pow, map_zero,
      show Ideal.Quotient.mk M zetaInt = ω from rfl, h1] at hs
    have h2q : (2 : (𝓞 K) ⧸ M) = 0 := by
      rw [show (2 : (𝓞 K) ⧸ M) = Ideal.Quotient.mk M 2 from (map_ofNat _ 2).symm,
        Ideal.Quotient.eq_zero_iff_mem]
      exact h2mem
    have h1q : (1 : (𝓞 K) ⧸ M) = 0 := by linear_combination hs - 2 * h2q
    exact one_ne_zero h1q
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
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
  obtain ⟨k, hk4, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Ideal.absNorm M ∣ 2 ^ 4 from hdvd)
  have hcard_eq : Fintype.card ((𝓞 K) ⧸ M) = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card, ← habs, hkeq]
  have hpc := FiniteField.pow_card ω
  rw [hcard_eq] at hpc
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω5
    simp at hω5
  have hpow1 : ω ^ (2 ^ k - 1) = 1 := by
    refine mul_right_cancel₀ hω0 ?_
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
    exact hpc
  have h5dvd : (5 : ℕ) ∣ 2 ^ k - 1 := by
    have horderω : orderOf ω = 5 := orderOf_eq_prime hω5 hω1
    exact horderω ▸ orderOf_dvd_of_pow_eq_one hpow1
  have hM16 : Ideal.absNorm M = 16 := by
    rw [hkeq]
    interval_cases k
    · rw [hkeq] at hM1
      norm_num at hM1
    · norm_num at h5dvd
    · norm_num at h5dvd
    · norm_num at h5dvd
    · norm_num
  have heq := eq_of_le_of_absNorm_eq hMle absNorm_span_two' hM16 (by norm_num)
  rw [heq]
  exact hMmax.isPrime

theorem absNorm_span_two : Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 16 :=
  absNorm_span_two'

private theorem nineteen_x_eq : (19 : 𝓞 K) = (zetaInt ^ 2 + 5 * zetaInt + 1) *
    (5 * zetaInt ^ 4 + zetaInt ^ 2 + zetaInt) := by
  linear_combination (-(5 * zetaInt + 25)) * zetaInt_pow_five - 6 * zetaInt_sum

private theorem nineteen_y_eq : (19 : 𝓞 K) = (zetaInt ^ 2 - 4 * zetaInt + 1) *
    (-(4 * zetaInt ^ 4) + zetaInt ^ 2 + zetaInt) := by
  linear_combination (4 * zetaInt - 16) * zetaInt_pow_five + 3 * zetaInt_sum

private theorem span_pair_nineteen_left :
    Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 5 * zetaInt + 1} =
      Ideal.span {zetaInt ^ 2 + 5 * zetaInt + 1} := by
  refine le_antisymm (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · rintro w (rfl | rfl)
    · rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      exact ⟨5 * zetaInt ^ 4 + zetaInt ^ 2 + zetaInt, nineteen_x_eq⟩
    · exact Ideal.mem_span_singleton_self _
  · exact Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩

private theorem span_pair_nineteen_right :
    Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 15 * zetaInt + 1} =
      Ideal.span {zetaInt ^ 2 - 4 * zetaInt + 1} := by
  have h19 : (19 : 𝓞 K) ∈ Ideal.span {zetaInt ^ 2 - 4 * zetaInt + 1} := by
    rw [Ideal.mem_span_singleton]
    exact ⟨-(4 * zetaInt ^ 4) + zetaInt ^ 2 + zetaInt, nineteen_y_eq⟩
  refine le_antisymm (Ideal.span_le.mpr ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · rintro w (rfl | rfl)
    · exact h19
    · rw [SetLike.mem_coe, show zetaInt ^ 2 + 15 * zetaInt + 1 =
        (zetaInt ^ 2 - 4 * zetaInt + 1) + 19 * zetaInt from by ring]
      exact Ideal.add_mem _ (Ideal.mem_span_singleton_self _)
        (Ideal.mul_mem_right _ _ h19)
  · exact Ideal.mem_span_pair.mpr ⟨-zetaInt, 1, by ring⟩

private theorem absNorm_span_x :
    Ideal.absNorm (Ideal.span {zetaInt ^ 2 + 5 * zetaInt + 1}) = 361 := by
  have hn : Algebra.norm ℤ (zetaInt ^ 2 + 5 * zetaInt + 1) = 361 := by
    apply intNorm_eq
    have e0 : algebraMap (𝓞 K) K (zetaInt ^ 2 + 5 * zetaInt + 1) = ζ ^ 2 + 5 * ζ + 1 := by
      simp [map_add, map_mul, map_pow, map_one, map_ofNat, coe_zetaInt]
    rw [e0]
    have e2 : sig2 (ζ ^ 2 + 5 * ζ + 1) = ζ ^ 4 + 5 * ζ ^ 2 + 1 := by
      simp only [map_add, map_pow, map_mul, map_one, map_ofNat, sig2_zeta]
      ring
    have e3 : sig3 (ζ ^ 2 + 5 * ζ + 1) = ζ + 5 * ζ ^ 3 + 1 := by
      simp only [map_add, map_pow, map_mul, map_one, map_ofNat, sig3_zeta]
      linear_combination ζ * zeta_pow_five
    have e4 : sig4 (ζ ^ 2 + 5 * ζ + 1) = ζ ^ 3 + 5 * ζ ^ 4 + 1 := by
      simp only [map_add, map_pow, map_mul, map_one, map_ofNat, sig4_zeta]
      linear_combination ζ ^ 3 * zeta_pow_five
    rw [e2, e3, e4]
    push_cast
    have h13 : (ζ ^ 2 + 5 * ζ + 1) * (ζ + 5 * ζ ^ 3 + 1) = 19 * ζ ^ 4 := by
      linear_combination 5 * zeta_pow_five + 6 * zeta_sum_eq_zero
    have h24 : (ζ ^ 4 + 5 * ζ ^ 2 + 1) * (ζ ^ 3 + 5 * ζ ^ 4 + 1) = 19 * ζ := by
      linear_combination (5 * ζ ^ 3 + ζ ^ 2 + 25 * ζ + 5) * zeta_pow_five +
        6 * zeta_sum_eq_zero
    calc (ζ ^ 2 + 5 * ζ + 1) * (ζ ^ 4 + 5 * ζ ^ 2 + 1) * (ζ + 5 * ζ ^ 3 + 1) *
        (ζ ^ 3 + 5 * ζ ^ 4 + 1)
        = ((ζ ^ 2 + 5 * ζ + 1) * (ζ + 5 * ζ ^ 3 + 1)) *
          ((ζ ^ 4 + 5 * ζ ^ 2 + 1) * (ζ ^ 3 + 5 * ζ ^ 4 + 1)) := by ring
      _ = (19 * ζ ^ 4) * (19 * ζ) := by rw [h13, h24]
      _ = 361 := by linear_combination 361 * zeta_pow_five
  rw [Ideal.absNorm_span_singleton, hn]
  rfl

private theorem absNorm_span_y :
    Ideal.absNorm (Ideal.span {zetaInt ^ 2 - 4 * zetaInt + 1}) = 361 := by
  have hn : Algebra.norm ℤ (zetaInt ^ 2 - 4 * zetaInt + 1) = 361 := by
    apply intNorm_eq
    have e0 : algebraMap (𝓞 K) K (zetaInt ^ 2 - 4 * zetaInt + 1) = ζ ^ 2 - 4 * ζ + 1 := by
      simp [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, coe_zetaInt]
    rw [e0]
    have e2 : sig2 (ζ ^ 2 - 4 * ζ + 1) = ζ ^ 4 - 4 * ζ ^ 2 + 1 := by
      simp only [map_add, map_sub, map_pow, map_mul, map_one, map_ofNat, sig2_zeta]
      ring
    have e3 : sig3 (ζ ^ 2 - 4 * ζ + 1) = ζ - 4 * ζ ^ 3 + 1 := by
      simp only [map_add, map_sub, map_pow, map_mul, map_one, map_ofNat, sig3_zeta]
      linear_combination ζ * zeta_pow_five
    have e4 : sig4 (ζ ^ 2 - 4 * ζ + 1) = ζ ^ 3 - 4 * ζ ^ 4 + 1 := by
      simp only [map_add, map_sub, map_pow, map_mul, map_one, map_ofNat, sig4_zeta]
      linear_combination ζ ^ 3 * zeta_pow_five
    rw [e2, e3, e4]
    push_cast
    have h13 : (ζ ^ 2 - 4 * ζ + 1) * (ζ - 4 * ζ ^ 3 + 1) = 19 * ζ ^ 4 := by
      linear_combination (-4) * zeta_pow_five - 3 * zeta_sum_eq_zero
    have h24 : (ζ ^ 4 - 4 * ζ ^ 2 + 1) * (ζ ^ 3 - 4 * ζ ^ 4 + 1) = 19 * ζ := by
      linear_combination (-(4 * ζ ^ 3) + ζ ^ 2 + 16 * ζ - 4) * zeta_pow_five -
        3 * zeta_sum_eq_zero
    calc (ζ ^ 2 - 4 * ζ + 1) * (ζ ^ 4 - 4 * ζ ^ 2 + 1) * (ζ - 4 * ζ ^ 3 + 1) *
        (ζ ^ 3 - 4 * ζ ^ 4 + 1)
        = ((ζ ^ 2 - 4 * ζ + 1) * (ζ - 4 * ζ ^ 3 + 1)) *
          ((ζ ^ 4 - 4 * ζ ^ 2 + 1) * (ζ ^ 3 - 4 * ζ ^ 4 + 1)) := by ring
      _ = (19 * ζ ^ 4) * (19 * ζ) := by rw [h13, h24]
      _ = 361 := by linear_combination 361 * zeta_pow_five
  rw [Ideal.absNorm_span_singleton, hn]
  rfl

/-- There is no prime of `𝓞 K` with residue field `𝔽₁₉`: `Φ₅` has no root mod `19`. -/
private theorem absNorm_ne_nineteen (P : Ideal (𝓞 K)) : Ideal.absNorm P ≠ 19 := by
  intro hcard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hcard' : Fintype.card ((𝓞 K) ⧸ P) = 19 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) (by norm_num) hcard'
  obtain ⟨s, hs⟩ := e.surjective (Ideal.Quotient.mk P zetaInt)
  have hs5 : 1 + s + s ^ 2 + s ^ 3 + s ^ 4 = (0 : ZMod 19) := by
    apply e.injective
    rw [map_add, map_add, map_add, map_add, map_one, map_pow, map_pow, map_pow, hs, map_zero]
    have hmk := congrArg (Ideal.Quotient.mk P) zetaInt_sum
    rw [map_add, map_add, map_add, map_add, map_one, map_pow, map_pow, map_pow,
      map_zero] at hmk
    exact hmk
  clear hs
  revert s
  decide

private theorem isPrime_of_absNorm_361 {g : 𝓞 K}
    (h361 : Ideal.absNorm (Ideal.span {g}) = 361) : (Ideal.span {g}).IsPrime := by
  have htop : Ideal.span {g} ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at h361
    norm_num at h361
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ htop
  have hdvd : Ideal.absNorm M ∣ 361 := h361 ▸ Ideal.absNorm_dvd_absNorm_of_le hMle
  have hM1 : Ideal.absNorm M ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hMmax.ne_top
  have hM19 : Ideal.absNorm M ≠ 19 := absNorm_ne_nineteen M
  have hM361 : Ideal.absNorm M = 361 := by
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 19)).mp
      (show Ideal.absNorm M ∣ 19 ^ 2 from hdvd)
    interval_cases k
    · rw [pow_zero] at hkeq
      exact absurd hkeq hM1
    · rw [pow_one] at hkeq
      exact absurd hkeq hM19
    · rw [hkeq]
      norm_num
  have heq := eq_of_le_of_absNorm_eq hMle h361 hM361 (by norm_num)
  rw [heq]
  exact hMmax.isPrime

/-- `19` splits into two primes of degree `2`: `19 ≡ -1 (mod 5)` has order `2` in `(ℤ/5)ˣ`,
and `Φ₅ ≡ (X² + 5X + 1)(X² + 15X + 1) (mod 19)`. -/
theorem span_nineteen_eq :
    Ideal.span {(19 : 𝓞 K)} =
      Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 5 * zetaInt + 1} *
        Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 15 * zetaInt + 1} := by
  rw [span_pair_nineteen_left, span_pair_nineteen_right,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_span_singleton]
  refine ⟨⟨-zetaInt ^ 2, -zetaInt ^ 3, by linear_combination zetaInt_pow_five,
    by linear_combination zetaInt_pow_five⟩, ?_⟩
  change (19 : 𝓞 K) * (-zetaInt ^ 2) =
    (zetaInt ^ 2 + 5 * zetaInt + 1) * (zetaInt ^ 2 - 4 * zetaInt + 1)
  linear_combination -zetaInt_sum

/-- Both primes above `19` are prime ideals of norm `19² = 361`. -/
theorem isPrime_primesAboveNineteen :
    (Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 5 * zetaInt + 1}).IsPrime ∧
      (Ideal.span {(19 : 𝓞 K), zetaInt ^ 2 + 15 * zetaInt + 1}).IsPrime := by
  constructor
  · rw [span_pair_nineteen_left]
    exact isPrime_of_absNorm_361 absNorm_span_x
  · rw [span_pair_nineteen_right]
    exact isPrime_of_absNorm_361 absNorm_span_y

private theorem elevenA : (ζ ^ 2 + ζ - 1) * (ζ ^ 3 + ζ - 1) = ζ ^ 4 - 2 * ζ + 2 := by
  linear_combination zeta_pow_five

private theorem elevenB : (ζ ^ 4 + ζ ^ 2 - 1) * (ζ ^ 4 + ζ ^ 3 - 1) = -(2 * ζ ^ 4) + ζ + 2 := by
  linear_combination (ζ ^ 3 + ζ ^ 2 + ζ + 1) * zeta_pow_five

private theorem elevenC : (ζ ^ 4 - 2 * ζ + 2) * (-(2 * ζ ^ 4) + ζ + 2) = 11 := by
  linear_combination (-(2 * ζ ^ 3) + 5) * zeta_pow_five - 2 * zeta_sum_eq_zero

/-- Norm computation shared by the four primes above `11`: the Galois orbit of `ζ² + ζ - 1`
is `{ζ² + ζ - 1, ζ⁴ + ζ² - 1, ζ³ + ζ - 1, ζ⁴ + ζ³ - 1}` with product `11`. -/
private theorem norm_eleven_orbit {w : 𝓞 K}
    (hw : algebraMap (𝓞 K) K w * sig2 (algebraMap (𝓞 K) K w) *
      sig3 (algebraMap (𝓞 K) K w) * sig4 (algebraMap (𝓞 K) K w) =
        (ζ ^ 2 + ζ - 1) * (ζ ^ 3 + ζ - 1) * ((ζ ^ 4 + ζ ^ 2 - 1) * (ζ ^ 4 + ζ ^ 3 - 1))) :
    Ideal.absNorm (Ideal.span {w}) = 11 := by
  have hn : Algebra.norm ℤ w = 11 := by
    apply intNorm_eq
    rw [hw, elevenA, elevenB]
    push_cast
    linear_combination elevenC
  rw [Ideal.absNorm_span_singleton, hn]
  rfl

private theorem absNorm_span_u3 :
    Ideal.absNorm (Ideal.span {zetaInt ^ 2 + zetaInt - 1}) = 11 := by
  refine norm_eleven_orbit ?_
  have e0 : algebraMap (𝓞 K) K (zetaInt ^ 2 + zetaInt - 1) = ζ ^ 2 + ζ - 1 := by
    simp [map_add, map_sub, map_pow, map_one, coe_zetaInt]
  rw [e0]
  have e2 : sig2 (ζ ^ 2 + ζ - 1) = ζ ^ 4 + ζ ^ 2 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig2_zeta]
    ring
  have e3 : sig3 (ζ ^ 2 + ζ - 1) = ζ ^ 3 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig3_zeta]
    linear_combination ζ * zeta_pow_five
  have e4 : sig4 (ζ ^ 2 + ζ - 1) = ζ ^ 4 + ζ ^ 3 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig4_zeta]
    linear_combination ζ ^ 3 * zeta_pow_five
  rw [e2, e3, e4]
  ring

private theorem absNorm_span_u4 :
    Ideal.absNorm (Ideal.span {zetaInt ^ 4 + zetaInt ^ 3 - 1}) = 11 := by
  refine norm_eleven_orbit ?_
  have e0 : algebraMap (𝓞 K) K (zetaInt ^ 4 + zetaInt ^ 3 - 1) = ζ ^ 4 + ζ ^ 3 - 1 := by
    simp [map_add, map_sub, map_pow, map_one, coe_zetaInt]
  rw [e0]
  have e2 : sig2 (ζ ^ 4 + ζ ^ 3 - 1) = ζ ^ 3 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig2_zeta]
    linear_combination (ζ ^ 3 + ζ) * zeta_pow_five
  have e3 : sig3 (ζ ^ 4 + ζ ^ 3 - 1) = ζ ^ 4 + ζ ^ 2 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig3_zeta]
    linear_combination (ζ ^ 7 + ζ ^ 2 + ζ ^ 4) * zeta_pow_five
  have e4 : sig4 (ζ ^ 4 + ζ ^ 3 - 1) = ζ ^ 2 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig4_zeta]
    linear_combination (ζ ^ 11 + ζ ^ 6 + ζ + ζ ^ 7 + ζ ^ 2) * zeta_pow_five
  rw [e2, e3, e4]
  ring

private theorem absNorm_span_u5 :
    Ideal.absNorm (Ideal.span {zetaInt ^ 4 + zetaInt ^ 2 - 1}) = 11 := by
  refine norm_eleven_orbit ?_
  have e0 : algebraMap (𝓞 K) K (zetaInt ^ 4 + zetaInt ^ 2 - 1) = ζ ^ 4 + ζ ^ 2 - 1 := by
    simp [map_add, map_sub, map_pow, map_one, coe_zetaInt]
  rw [e0]
  have e2 : sig2 (ζ ^ 4 + ζ ^ 2 - 1) = ζ ^ 4 + ζ ^ 3 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig2_zeta]
    linear_combination ζ ^ 3 * zeta_pow_five
  have e3 : sig3 (ζ ^ 4 + ζ ^ 2 - 1) = ζ ^ 2 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig3_zeta]
    linear_combination (ζ ^ 7 + ζ ^ 2 + ζ) * zeta_pow_five
  have e4 : sig4 (ζ ^ 4 + ζ ^ 2 - 1) = ζ ^ 3 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig4_zeta]
    linear_combination (ζ ^ 11 + ζ ^ 6 + ζ + ζ ^ 3) * zeta_pow_five
  rw [e2, e3, e4]
  ring

private theorem absNorm_span_u9 :
    Ideal.absNorm (Ideal.span {zetaInt ^ 3 + zetaInt - 1}) = 11 := by
  refine norm_eleven_orbit ?_
  have e0 : algebraMap (𝓞 K) K (zetaInt ^ 3 + zetaInt - 1) = ζ ^ 3 + ζ - 1 := by
    simp [map_add, map_sub, map_pow, map_one, coe_zetaInt]
  rw [e0]
  have e2 : sig2 (ζ ^ 3 + ζ - 1) = ζ ^ 2 + ζ - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig2_zeta]
    linear_combination ζ * zeta_pow_five
  have e3 : sig3 (ζ ^ 3 + ζ - 1) = ζ ^ 4 + ζ ^ 3 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig3_zeta]
    linear_combination ζ ^ 4 * zeta_pow_five
  have e4 : sig4 (ζ ^ 3 + ζ - 1) = ζ ^ 4 + ζ ^ 2 - 1 := by
    simp only [map_add, map_sub, map_pow, map_one, sig4_zeta]
    linear_combination (ζ ^ 7 + ζ ^ 2) * zeta_pow_five
  rw [e2, e3, e4]
  ring

private theorem span_pair_eleven_three :
    Ideal.span {(11 : 𝓞 K), zetaInt - 3} = Ideal.span {zetaInt ^ 2 + zetaInt - 1} := by
  have hr : ((3 : ℤ) : ZMod 11) ^ 4 + ((3 : ℤ) : ZMod 11) ^ 3 + ((3 : ℤ) : ZMod 11) ^ 2 +
      ((3 : ℤ) : ZMod 11) + 1 = 0 := by decide
  refine (eq_of_le_of_absNorm_eq ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    absNorm_span_u3 ?_ (by norm_num)).symm
  · exact Ideal.mem_span_pair.mpr ⟨1, zetaInt + 4, by ring⟩
  · have h := absNorm_span_pair 11 3 hr
    rwa [show ((11 : ℕ) : 𝓞 K) = (11 : 𝓞 K) from by norm_cast,
      show ((3 : ℤ) : 𝓞 K) = (3 : 𝓞 K) from by norm_cast] at h

private theorem span_pair_eleven_four :
    Ideal.span {(11 : 𝓞 K), zetaInt - 4} = Ideal.span {zetaInt ^ 4 + zetaInt ^ 3 - 1} := by
  have hr : ((4 : ℤ) : ZMod 11) ^ 4 + ((4 : ℤ) : ZMod 11) ^ 3 + ((4 : ℤ) : ZMod 11) ^ 2 +
      ((4 : ℤ) : ZMod 11) + 1 = 0 := by decide
  refine (eq_of_le_of_absNorm_eq ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    absNorm_span_u4 ?_ (by norm_num)).symm
  · exact Ideal.mem_span_pair.mpr
      ⟨29, zetaInt ^ 3 + 5 * zetaInt ^ 2 + 20 * zetaInt + 80, by ring⟩
  · have h := absNorm_span_pair 11 4 hr
    rwa [show ((11 : ℕ) : 𝓞 K) = (11 : 𝓞 K) from by norm_cast,
      show ((4 : ℤ) : 𝓞 K) = (4 : 𝓞 K) from by norm_cast] at h

private theorem span_pair_eleven_five :
    Ideal.span {(11 : 𝓞 K), zetaInt - 5} = Ideal.span {zetaInt ^ 4 + zetaInt ^ 2 - 1} := by
  have hr : ((5 : ℤ) : ZMod 11) ^ 4 + ((5 : ℤ) : ZMod 11) ^ 3 + ((5 : ℤ) : ZMod 11) ^ 2 +
      ((5 : ℤ) : ZMod 11) + 1 = 0 := by decide
  refine (eq_of_le_of_absNorm_eq ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    absNorm_span_u5 ?_ (by norm_num)).symm
  · exact Ideal.mem_span_pair.mpr
      ⟨59, zetaInt ^ 3 + 5 * zetaInt ^ 2 + 26 * zetaInt + 130, by ring⟩
  · have h := absNorm_span_pair 11 5 hr
    rwa [show ((11 : ℕ) : 𝓞 K) = (11 : 𝓞 K) from by norm_cast,
      show ((5 : ℤ) : 𝓞 K) = (5 : 𝓞 K) from by norm_cast] at h

private theorem span_pair_eleven_nine :
    Ideal.span {(11 : 𝓞 K), zetaInt - 9} = Ideal.span {zetaInt ^ 3 + zetaInt - 1} := by
  have hr : ((9 : ℤ) : ZMod 11) ^ 4 + ((9 : ℤ) : ZMod 11) ^ 3 + ((9 : ℤ) : ZMod 11) ^ 2 +
      ((9 : ℤ) : ZMod 11) + 1 = 0 := by decide
  refine (eq_of_le_of_absNorm_eq ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    absNorm_span_u9 ?_ (by norm_num)).symm
  · exact Ideal.mem_span_pair.mpr ⟨67, zetaInt ^ 2 + 9 * zetaInt + 82, by ring⟩
  · have h := absNorm_span_pair 11 9 hr
    rwa [show ((11 : ℕ) : 𝓞 K) = (11 : 𝓞 K) from by norm_cast,
      show ((9 : ℤ) : 𝓞 K) = (9 : 𝓞 K) from by norm_cast] at h

/-- `11` splits completely: `11 ≡ 1 (mod 5)`, and the roots of `Φ₅` mod `11` are
`3, 4, 5, 9` (the elements of order `5` in `(ℤ/11)ˣ`). -/
theorem span_eleven_eq :
    Ideal.span {(11 : 𝓞 K)} =
      Ideal.span {(11 : 𝓞 K), zetaInt - 3} * Ideal.span {(11 : 𝓞 K), zetaInt - 4} *
        Ideal.span {(11 : 𝓞 K), zetaInt - 5} * Ideal.span {(11 : 𝓞 K), zetaInt - 9} := by
  rw [span_pair_eleven_three, span_pair_eleven_four, span_pair_eleven_five,
    span_pair_eleven_nine, Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
  have hA : (zetaInt ^ 2 + zetaInt - 1) * (zetaInt ^ 3 + zetaInt - 1) =
      zetaInt ^ 4 - 2 * zetaInt + 2 := by
    linear_combination zetaInt_pow_five
  have hB : (zetaInt ^ 4 + zetaInt ^ 2 - 1) * (zetaInt ^ 4 + zetaInt ^ 3 - 1) =
      -(2 * zetaInt ^ 4) + zetaInt + 2 := by
    linear_combination (zetaInt ^ 3 + zetaInt ^ 2 + zetaInt + 1) * zetaInt_pow_five
  have hC : (zetaInt ^ 4 - 2 * zetaInt + 2) * (-(2 * zetaInt ^ 4) + zetaInt + 2) =
      (11 : 𝓞 K) := by
    linear_combination (-(2 * zetaInt ^ 3) + 5) * zetaInt_pow_five - 2 * zetaInt_sum
  rw [show (zetaInt ^ 2 + zetaInt - 1) * (zetaInt ^ 4 + zetaInt ^ 3 - 1) *
      (zetaInt ^ 4 + zetaInt ^ 2 - 1) * (zetaInt ^ 3 + zetaInt - 1) = (11 : 𝓞 K) from by
    linear_combination ((zetaInt ^ 4 + zetaInt ^ 2 - 1) * (zetaInt ^ 4 + zetaInt ^ 3 - 1)) * hA +
      (zetaInt ^ 4 - 2 * zetaInt + 2) * hB + hC]

/-- Each ideal `(11, ζ - r)` for `r ∈ {3, 4, 5, 9}` is a prime of norm `11`. -/
theorem isPrime_primeAboveEleven (r : ℤ) (hr : r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 9) :
    (Ideal.span {(11 : 𝓞 K), zetaInt - (r : 𝓞 K)}).IsPrime := by
  have hr' : ((r : ZMod 11)) ^ 4 + ((r : ZMod 11)) ^ 3 + ((r : ZMod 11)) ^ 2 +
      (r : ZMod 11) + 1 = 0 := by
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h := (isMaximal_span_pair 11 r hr').isPrime
  rwa [show ((11 : ℕ) : 𝓞 K) = (11 : 𝓞 K) from by norm_cast] at h

/-- The splitting law for `ℚ(ζ₅)`: a prime `p` splits completely iff `p ≡ 1 (mod 5)`. -/
theorem splits_completely_iff (p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ∧ Ideal.absNorm P = p) ↔
      p % 5 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  constructor
  · rintro ⟨P, hPprime, hle, habs⟩
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at habs
    haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [habs]; exact hp.ne_zero)
    haveI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
    have hcard' : Fintype.card ((𝓞 K) ⧸ P) = p := by
      rw [← Nat.card_eq_fintype_card]
      exact habs
    let e := ZMod.ringEquivOfPrime ((𝓞 K) ⧸ P) hp hcard'
    obtain ⟨s, hs⟩ := e.surjective (Ideal.Quotient.mk P zetaInt)
    have hs5 : s ^ 5 = (1 : ZMod p) := by
      apply e.injective
      rw [map_pow, hs, ← map_pow (Ideal.Quotient.mk P), zetaInt_pow_five, map_one, map_one]
    have hssum : 1 + s + s ^ 2 + s ^ 3 + s ^ 4 = (0 : ZMod p) := by
      apply e.injective
      rw [map_add, map_add, map_add, map_add, map_one, map_pow, map_pow, map_pow, hs, map_zero]
      have hmk := congrArg (Ideal.Quotient.mk P) zetaInt_sum
      rw [map_add, map_add, map_add, map_add, map_one, map_pow, map_pow, map_pow,
        map_zero] at hmk
      exact hmk
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1] at hssum
      have h5 : ((5 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination hssum
      have hdvd := (CharP.cast_eq_zero_iff (ZMod p) p 5).mp h5
      exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp hdvd)
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0] at hs5
      simp at hs5
    set u : (ZMod p)ˣ := Units.mkOfMulEqOne s (s ^ 4)
      (by rw [← pow_succ']; exact hs5) with hudef
    have hu : (u : ZMod p) = s := rfl
    have horder : orderOf u = 5 := by
      refine orderOf_eq_prime ?_ ?_
      · ext
        rw [Units.val_pow_eq_pow_val, hu]
        exact hs5
      · intro h1
        apply hs1
        rw [← hu, h1, Units.val_one]
    have hdvd_card : (5 : ℕ) ∣ p - 1 := by
      have h := orderOf_dvd_natCard u
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
    obtain ⟨m, hm⟩ : (5 : ℕ) ∣ p - 1 := ⟨(p - 1) / 5, by omega⟩
    have hm0 : m ≠ 0 := by omega
    have hou : orderOf (g ^ m) = 5 := by
      rw [orderOf_pow, hog, hm]
      have hgcd : Nat.gcd (5 * m) m = m := Nat.gcd_eq_right ⟨5, by ring⟩
      rw [hgcd, Nat.mul_div_assoc 5 (dvd_refl m), Nat.div_self (show 0 < m by omega), mul_one]
    have hu5 : ((g ^ m : (ZMod p)ˣ) : ZMod p) ^ 5 = 1 := by
      have h := pow_orderOf_eq_one (g ^ m)
      rw [hou] at h
      have hc := congrArg Units.val h
      simpa using hc
    have hu1 : ((g ^ m : (ZMod p)ˣ) : ZMod p) ≠ 1 := by
      intro h1
      have : (g ^ m) = 1 := Units.ext (by simpa using h1)
      rw [this, orderOf_one] at hou
      norm_num at hou
    have hr : (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) ^ 4 +
        (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) ^ 3 +
        (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) ^ 2 +
        (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) + 1 = 0 := by
      have hcast : (((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : ZMod p) =
          ((g ^ m : (ZMod p)ˣ) : ZMod p) := by
        push_cast
        exact ZMod.natCast_rightInverse _
      rw [hcast]
      set v : ZMod p := ((g ^ m : (ZMod p)ˣ) : ZMod p)
      have hfactor : (v - 1) * (v ^ 4 + v ^ 3 + v ^ 2 + v + 1) = 0 := by
        linear_combination hu5
      rcases mul_eq_zero.mp hfactor with h | h
      · exact absurd (by linear_combination h) hu1
      · linear_combination h
    refine ⟨Ideal.span {((p : ℕ) : 𝓞 K),
      zetaInt - ((((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : 𝓞 K))},
      (isMaximal_span_pair p _ hr).isPrime, ?_, absNorm_span_pair p _ hr⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span (by simp)

/-- A rational prime `p` ramifies in `ℚ(ζ₅)` iff `p = 5`, i.e. iff `p` divides the
discriminant `125`. -/
theorem ramified_iff_eq_five (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 5 := by
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
      rw [hmap]
      exact hle2
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
    have habsP125 : Ideal.absNorm P ∣ 125 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq] at h
      simpa using h
    have hpdvd : p ∣ 125 := (hkeq ▸ dvd_pow_self p hk0).trans habsP125
    have hp5 : p ∣ 5 := hp.dvd_of_dvd_pow (show p ∣ 5 ^ 3 by norm_num; exact hpdvd)
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp5
  · rintro rfl
    refine ⟨Ideal.span {1 - zetaInt}, isPrime_span_one_sub_zeta, ?_⟩
    have hcast : ((5 : ℕ) : 𝓞 K) = (5 : 𝓞 K) := by norm_num
    rw [hcast, span_five_eq]
    exact Ideal.pow_le_pow_right (by norm_num)


end XYin.NumberField.New.CyclotomicFive
