import XYin.NumberField.FieldExamples.CyclotomicThree.RingOfIntegers

noncomputable section

open scoped NumberField nonZeroDivisors Real ENNReal

open Module NumberField Polynomial

namespace XYin.NumberField.CyclotomicThree

/-! ## 3. Discriminant -/

/-- The number-field discriminant of `ℚ(ζ₃) = ℚ(√-3)` is `-3`: the quadratic field of
smallest absolute discriminant. In particular `3` is the only ramified prime, cf.
`ramified_iff_eq_three`. -/
theorem numberField_discr_eq : NumberField.discr K = -3 := by
  rw [IsCyclotomicExtension.Rat.discr_prime 3 K]
  norm_num

theorem zetaExplicitIntegralBasis_discr :
    Algebra.discr ℤ zetaExplicitIntegralBasis = (-3 : ℤ) := by
  calc
    Algebra.discr ℤ zetaExplicitIntegralBasis = NumberField.discr K := by
      simpa using (NumberField.discr_eq_discr (K := K) zetaExplicitIntegralBasis)
    _ = -3 := by
      rw [IsCyclotomicExtension.Rat.discr_prime 3 K]
      norm_num

/--
`NumberField.coe_discr` says `(NumberField.discr K : ℚ) = Algebra.discr ℚ (integralBasis K)`.
This bridges the integer-valued field discriminant to the concrete `Algebra.discr ℚ`
computed from mathlib's canonical `ℚ`-basis of `K`.
-/
example : Algebra.discr ℚ (NumberField.integralBasis K) = (-3 : ℚ) := by
  have h := NumberField.coe_discr K
  rw [show NumberField.discr K = -3 from by
        rw [IsCyclotomicExtension.Rat.discr_prime 3 K]; norm_num] at h
  simpa using h.symm

/--
`Algebra.discr_of_matrix_mulVec`: replacing basis `b` by `Pb` scales the discriminant by `det(P)²`.
This is the key formula behind the fact that all `ℤ`-bases of `𝓞 K` yield the same
`NumberField.discr K`: change-of-basis matrices between them are unimodular (`det = ±1`),
so `det(P)² = 1` and the discriminant is preserved.
-/
theorem discr_matrix_mulVec_K
    (P : Matrix (Free.ChooseBasisIndex ℤ (𝓞 K)) (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ) :
    Algebra.discr ℚ (Matrix.mulVec (P.map (algebraMap ℚ K)) (NumberField.integralBasis K)) =
      P.det ^ 2 * Algebra.discr ℚ (NumberField.integralBasis K) :=
  Algebra.discr_of_matrix_mulVec _ _

/-- Concretely: a unimodular change of basis preserves the discriminant `-3`. -/
example (P : Matrix (Free.ChooseBasisIndex ℤ (𝓞 K)) (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ)
    (hdet : P.det = 1 ∨ P.det = -1) :
    Algebra.discr ℚ (Matrix.mulVec (P.map (algebraMap ℚ K)) (NumberField.integralBasis K)) =
        (-3 : ℚ) := by
  have hdiscr : Algebra.discr ℚ (NumberField.integralBasis K) = -3 := by
    have h := NumberField.coe_discr K
    rw [show NumberField.discr K = -3 from by
          rw [IsCyclotomicExtension.Rat.discr_prime 3 K]; norm_num] at h
    simpa using h.symm
  rw [discr_matrix_mulVec_K, hdiscr]
  rcases hdet with h | h <;> simp [h]

section PrivateMachinery

private theorem zeta_pow_three : ζ ^ 3 = 1 :=
  zeta_isPrimitiveRoot.pow_eq_one

private theorem coe_zetaInt : algebraMap OK K zetaInt = ζ := rfl

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

private theorem intNorm_eq (x : OK) (n : ℤ)
    (h : algebraMap OK K x * sig2 (algebraMap OK K x) = (n : K)) :
    Algebra.norm ℤ x = n := by
  haveI := IsCyclotomicExtension.isGalois {3} ℚ K
  have h1 : algebraMap ℚ K (Algebra.norm ℚ (algebraMap OK K x)) = ((n : ℚ) : K) := by
    rw [Algebra.norm_eq_prod_automorphisms, prod_aut_apply, h]
    push_cast
    ring
  have h2 : Algebra.norm ℚ (algebraMap OK K x) = (n : ℚ) := by
    apply (algebraMap ℚ K).injective
    rw [h1, eq_ratCast (algebraMap ℚ K) (n : ℚ)]
  have h3 : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (algebraMap OK K x) :=
    Algebra.coe_norm_int x
  rw [h2] at h3
  exact_mod_cast h3

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

private noncomputable def residueHom (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    OK →ₐ[ℤ] ZMod p :=
  zeta_isPrimitiveRoot.integralPowerBasis.lift ((r : ℤ) : ZMod p)
    (by
      rw [minpoly_gen_eq]
      simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
      exact hr)

private theorem residueHom_zetaInt (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    residueHom p r hr zetaInt = (r : ZMod p) := by
  rw [← gen_eq_zetaInt]
  exact zeta_isPrimitiveRoot.integralPowerBasis.lift_gen ((r : ℤ) : ZMod p) _

private theorem ker_residueHom (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    RingHom.ker (residueHom p r hr).toRingHom =
      Ideal.span {(p : OK), zetaInt - (r : OK)} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [RingHom.mem_ker] at hx
    obtain ⟨q, -, hq⟩ := zeta_isPrimitiveRoot.integralPowerBasis.exists_eq_aeval x
    rw [gen_eq_zetaInt] at hq
    have key : x - ((q.eval r : ℤ) : OK) ∈ Ideal.span {zetaInt - (r : OK)} := by
      rw [Ideal.mem_span_singleton, hq]
      have hdvd := Polynomial.sub_dvd_eval_sub zetaInt ((r : ℤ) : OK)
        (q.map (algebraMap ℤ OK))
      have e1 : (q.map (algebraMap ℤ OK)).eval zetaInt = Polynomial.aeval zetaInt q := by
        rw [Polynomial.eval_map, ← Polynomial.aeval_def]
      have e2 : (q.map (algebraMap ℤ OK)).eval ((r : ℤ) : OK) = ((q.eval r : ℤ) : OK) := by
        have hcast : ((r : ℤ) : OK) = algebraMap ℤ OK r := by
          simp [algebraMap_int_eq]
        rw [Polynomial.eval_map, hcast, Polynomial.eval₂_at_apply]
        simp [algebraMap_int_eq]
      rw [e1, e2] at hdvd
      exact hdvd
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp key
    have hphi : ((q.eval r : ℤ) : ZMod p) = 0 := by
      have h1 : residueHom p r hr (x - ((q.eval r : ℤ) : OK)) = 0 := by
        rw [hd, map_mul, map_sub, residueHom_zetaInt, map_intCast, sub_self, zero_mul]
      rw [map_sub, map_intCast, show residueHom p r hr x = 0 from hx, zero_sub,
        neg_eq_zero] at h1
      exact h1
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hphi
    have hx_eq : x = (zetaInt - (r : OK)) * d + (p : OK) * ((m : ℤ) : OK) := by
      have h2 : x = (zetaInt - (r : OK)) * d + ((q.eval r : ℤ) : OK) := by
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
      have h0 : (residueHom p r hr) (zetaInt - (r : OK)) = 0 := by
        rw [map_sub, residueHom_zetaInt, map_intCast, sub_self]
      exact h0

private theorem residueHom_surjective (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    Function.Surjective (residueHom p r hr) := by
  intro z
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective z
  exact ⟨((m : ℤ) : OK), by rw [map_intCast]; exact hm⟩

private theorem isMaximal_span_pair (p : ℕ) [Fact p.Prime] (r : ℤ)
    (hr : ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    (Ideal.span {(p : OK), zetaInt - (r : OK)}).IsMaximal := by
  rw [← ker_residueHom p r hr]
  exact RingHom.ker_isMaximal_of_surjective _ (residueHom_surjective p r hr)

private theorem absNorm_span_pair (p : ℕ) (r : ℤ)
    (hr : ((r : ZMod p)) ^ 2 + (r : ZMod p) + 1 = 0) :
    Ideal.absNorm (Ideal.span {(p : OK), zetaInt - (r : OK)}) = p := by
  rw [← ker_residueHom p r hr, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (residueHom_surjective p r hr)).toEquiv]
  exact Nat.card_zmod p

private theorem eq_of_le_of_absNorm_eq {I J : Ideal OK} (hle : I ≤ J) {n : ℕ}
    (hI : Ideal.absNorm I = n) (hJ : Ideal.absNorm J = n) (hn : n ≠ 0) : I = J := by
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hmul := _root_.map_mul Ideal.absNorm J C
  rw [← hC, hI, hJ] at hmul
  have hC1 : Ideal.absNorm C = 1 :=
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
      (by rw [mul_one]; exact hmul)).symm
  rw [hC, Ideal.absNorm_eq_one_iff.mp hC1, Ideal.mul_top]

end PrivateMachinery

/-! ## 4. Norm form -/

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
    Algebra.norm ℤ (x • (1 : OK) + y • zetaInt) = x ^ 2 - x * y + y ^ 2 := by
  have h1 : ((Algebra.norm ℤ (x • (1 : OK) + y • zetaInt) : ℤ) : ℚ) =
      Algebra.norm ℚ (algebraMap OK K (x • (1 : OK) + y • zetaInt)) :=
    Algebra.coe_norm_int _
  have h2 : algebraMap OK K (x • (1 : OK) + y • zetaInt) =
      (x : ℚ) • (1 : K) + (y : ℚ) • ζ := by
    rw [map_add, map_zsmul, map_zsmul, map_one, coe_zetaInt]
    rw [Int.cast_smul_eq_zsmul ℚ x (1 : K), Int.cast_smul_eq_zsmul ℚ y ζ]
  rw [h2, norm_eq_normForm] at h1
  exact_mod_cast h1

/-- The unit equation of `ℚ(ζ₃)`: `x + yζ` is a unit of `ℤ[ζ]` iff `x² - xy + y² = 1`. The
form is positive definite (this is the imaginary quadratic case), so only the value `+1`
occurs, and the six integer solutions correspond to the six roots of unity `±1, ±ζ, ±ζ²`. -/
theorem isUnit_iff_normForm (x y : ℤ) :
    IsUnit (x • (1 : OK) + y • zetaInt) ↔ x ^ 2 - x * y + y ^ 2 = 1 := by
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
  sorry

/-- The norm of `1 + ζ` is `1`, so `1 + ζ` is another cyclotomic unit. -/
theorem norm_one_add_zeta : Algebra.norm ℚ (1 + ζ) = 1 := by
  sorry

/-! ## 5. Splitting of primes -/

/-- The element `ζ - 1` is a prime element of the ring of integers. -/
example : Prime (zeta_isPrimitiveRoot.toInteger - 1 : OK) :=
  zeta_isPrimitiveRoot.zeta_sub_one_prime'

/-- In this field, `ζ - 1` lies above `3`: it divides `3` in `𝓞 K`. -/
example : (zeta_isPrimitiveRoot.toInteger - 1 : OK) ∣ (3 : OK) :=
  zeta_isPrimitiveRoot.toInteger_sub_one_dvd_prime'

/-- `3` is (totally) ramified: `(3) = (ζ - 1)²` as ideals of `𝓞 K`. It is the unique
ramified prime, matching the discriminant `-3`. -/
theorem span_three_eq :
    Ideal.span {(3 : OK)} = Ideal.span {zetaInt - 1} ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
  refine ⟨⟨-zetaInt, -zetaInt ^ 2, ?_, ?_⟩, ?_⟩
  · linear_combination zetaInt_pow_three
  · linear_combination zetaInt_pow_three
  · change (3 : OK) * (-zetaInt) = (zetaInt - 1) ^ 2
    linear_combination -zetaInt_relation

private theorem span_zetaInt_sub_one_eq_pair :
    Ideal.span {zetaInt - 1} = Ideal.span {((3 : ℕ) : OK), zetaInt - ((1 : ℤ) : OK)} := by
  refine le_antisymm ((Ideal.span_singleton_le_iff_mem _).mpr ?_) (Ideal.span_le.mpr ?_)
  · exact Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩
  · rintro y (rfl | rfl)
    · have h3 : ((3 : ℕ) : OK) ∈ Ideal.span {(3 : OK)} := by
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

private theorem absNorm_span_two' : Ideal.absNorm (Ideal.span {(2 : OK)}) = 4 := by
  have hfin : Module.finrank ℤ OK = 2 := by
    rw [Module.finrank_eq_card_basis zetaExplicitIntegralBasis, Fintype.card_fin]
  rw [Ideal.absNorm_span_singleton,
    show (2 : OK) = algebraMap ℤ OK 2 from (map_ofNat _ 2).symm,
    Algebra.norm_algebraMap, hfin]
  rfl

/-- `2` is inert in `ℚ(ζ₃)`: `2 ≡ 2 (mod 3)`, equivalently `X² + X + 1` is irreducible
mod `2`, so `(2)` is itself prime. -/
theorem isPrime_span_two : (Ideal.span {(2 : OK)}).IsPrime := by
  have htop : Ideal.span {(2 : OK)} ≠ ⊤ := by
    intro h
    have h4 := absNorm_span_two'
    rw [h, Ideal.absNorm_top] at h4
    norm_num at h4
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ htop
  haveI := hMmax
  letI : Field (OK ⧸ M) := Ideal.Quotient.field M
  have hdvd : Ideal.absNorm M ∣ 4 :=
    absNorm_span_two' ▸ Ideal.absNorm_dvd_absNorm_of_le hMle
  have h2mem : (2 : OK) ∈ M := hMle (Ideal.mem_span_singleton_self _)
  set ω : OK ⧸ M := Ideal.Quotient.mk M zetaInt with hω
  have hω3 : ω ^ 3 = 1 := by
    rw [hω, ← map_pow, zetaInt_pow_three, map_one]
  have hω1 : ω ≠ 1 := by
    intro h1
    have hs := congrArg (Ideal.Quotient.mk M) zetaInt_relation
    rw [map_add, map_add, map_one, map_pow, map_zero, show Ideal.Quotient.mk M zetaInt = ω from rfl,
      h1] at hs
    have h2q : (2 : OK ⧸ M) = 0 := by
      rw [show (2 : OK ⧸ M) = Ideal.Quotient.mk M 2 from (map_ofNat _ 2).symm,
        Ideal.Quotient.eq_zero_iff_mem]
      exact h2mem
    have h1q : (1 : OK ⧸ M) = 0 := by linear_combination hs - h2q
    exact one_ne_zero h1q
  classical
  have habs : Ideal.absNorm M = Nat.card (OK ⧸ M) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (OK ⧸ M) := by
    refine Nat.finite_of_card_ne_zero fun h0 => ?_
    rw [habs, h0] at hdvd
    norm_num at hdvd
  haveI : Fintype (OK ⧸ M) := Fintype.ofFinite _
  have hM1 : Ideal.absNorm M ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hMmax.ne_top
  obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Ideal.absNorm M ∣ 2 ^ 2 from hdvd)
  have hcard_eq : Fintype.card (OK ⧸ M) = 2 ^ k := by
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
  have hM4 : Ideal.absNorm M = 4 := by
    rw [hkeq]
    interval_cases k
    · rw [hkeq] at hM1
      norm_num at hM1
    · norm_num at h3dvd
    · norm_num
  have heq := eq_of_le_of_absNorm_eq hMle absNorm_span_two' hM4 (by norm_num)
  rw [heq]
  exact hMmax.isPrime

/-- The inert prime `(2)` has norm `4` (residue degree `f = 2`). -/
theorem absNorm_span_two : Ideal.absNorm (Ideal.span {(2 : OK)}) = 4 := by
  exact absNorm_span_two'

private theorem seven_eq_mul : (7 : OK) = (3 + zetaInt) * (3 + zetaInt ^ 2) := by
  linear_combination -zetaInt_pow_three - 3 * zetaInt_relation

/-- `7 ≡ 1 (mod 3)` splits completely: `7 = (3 + ζ)(3 + ζ²)` and
`(7) = (3 + ζ) · (3 + ζ²)` is a product of two distinct primes of norm `7`. -/
theorem span_seven_eq :
    Ideal.span {(7 : OK)} = Ideal.span {3 + zetaInt} * Ideal.span {3 + zetaInt ^ 2} := by
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

/-- The splitting law at ramified primes: a rational prime `p` ramifies in `ℚ(ζ₃)` iff
`p = 3`, i.e. iff `p` divides the discriminant `-3`. -/
theorem ramified_iff_eq_three (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal OK, P.IsPrime ∧ Ideal.span {(p : OK)} ≤ P ^ 2) ↔ p = 3 := by
  constructor
  · rintro ⟨P, hP, hle2⟩
    haveI : P.IsPrime := hP
    have hple : Ideal.span {((p : ℕ) : OK)} ≤ P :=
      hle2.trans (Ideal.pow_le_self (by norm_num))
    have hpmemP : ((p : ℕ) : OK) ∈ P := hple (Ideal.mem_span_singleton_self _)
    have hpne : ((p : ℕ) : OK) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hPbot : P ≠ ⊥ := by
      intro h
      rw [h] at hpmemP
      exact hpne (Ideal.mem_bot.mp hpmemP)
    have hfin : Module.finrank ℤ OK = 2 := by
      rw [Module.finrank_eq_card_basis zetaExplicitIntegralBasis, Fintype.card_fin]
    have habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : OK)}) = p ^ 2 := by
      rw [Ideal.absNorm_span_singleton]
      have hcast : ((p : ℕ) : OK) = algebraMap ℤ OK ((p : ℕ) : ℤ) := by
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
    have hmap : Ideal.map (algebraMap ℤ OK) (Ideal.span {((p : ℕ) : ℤ)}) =
        Ideal.span {((p : ℕ) : OK)} := by
      rw [Ideal.map_span, Set.image_singleton]
      norm_num
    have hle2' : Ideal.map (algebraMap ℤ OK) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 2 := by
      rw [hmap]
      exact hle2
    have hno3 : ¬ Ideal.map (algebraMap ℤ OK) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 3 := by
      intro h3
      rw [hmap] at h3
      have hd := Ideal.absNorm_dvd_absNorm_of_le h3
      rw [map_pow, habsp, hkeq, ← pow_mul] at hd
      rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
      omega
    have hidx : Ideal.ramificationIdx (Ideal.span {((p : ℕ) : ℤ)}) P ≠ 1 := by
      rw [Ideal.ramificationIdx_spec hle2' hno3]
      norm_num
    have hund : Ideal.under ℤ P = Ideal.span {((p : ℕ) : ℤ)} := by
      have hmem : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
        rw [Ideal.under, Ideal.mem_comap]
        have hcast2 : algebraMap ℤ OK ((p : ℕ) : ℤ) = ((p : ℕ) : OK) := by
          push_cast
          rfl
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
    have hPdiff : P ∣ differentIdeal ℤ OK := dvd_differentIdeal_iff.mpr hunram
    have habsP3 : Ideal.absNorm P ∣ 3 := by
      have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPdiff)
      rw [NumberField.absNorm_differentIdeal (K := K), numberField_discr_eq] at h
      simpa using h
    have hpdvd : p ∣ 3 := (hkeq ▸ dvd_pow_self p hk0).trans habsP3
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpdvd
  · rintro rfl
    refine ⟨Ideal.span {zetaInt - 1}, isPrime_span_zetaInt_sub_one, ?_⟩
    have hcast : ((3 : ℕ) : OK) = (3 : OK) := by norm_num
    rw [hcast, span_three_eq]

private theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : OK)}) = p ^ 2 := by
  have hfin : Module.finrank ℤ OK = 2 := by
    rw [Module.finrank_eq_card_basis zetaExplicitIntegralBasis, Fintype.card_fin]
  rw [Ideal.absNorm_span_singleton]
  have hcast : ((p : ℕ) : OK) = algebraMap ℤ OK ((p : ℕ) : ℤ) := by
    push_cast
    rfl
  rw [hcast, Algebra.norm_algebraMap, hfin, Int.natAbs_pow, Int.natAbs_natCast]

private theorem exists_prime_norm_iff_one_mod_three (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (∃ P : Ideal OK, P.IsPrime ∧ Ideal.span {(p : OK)} ≤ P ∧ Ideal.absNorm P = p) ↔
      p % 3 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨P, hPprime, hle, habs⟩
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at habs
    haveI : Finite (OK ⧸ P) := Nat.finite_of_card_ne_zero (by rw [habs]; exact hp.ne_zero)
    haveI : Fintype (OK ⧸ P) := Fintype.ofFinite _
    have hcard' : Fintype.card (OK ⧸ P) = p := by
      rw [← Nat.card_eq_fintype_card]
      exact habs
    let e := ZMod.ringEquivOfPrime (OK ⧸ P) hp hcard'
    obtain ⟨s, hs⟩ := e.surjective (Ideal.Quotient.mk P zetaInt)
    have hs3 : s ^ 3 = (1 : ZMod p) := by
      apply e.injective
      rw [map_pow, hs, ← map_pow (Ideal.Quotient.mk P), zetaInt_pow_three, map_one,
        map_one]
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
    refine ⟨Ideal.span {((p : ℕ) : OK),
      zetaInt - ((((((g ^ m : (ZMod p)ˣ) : ZMod p).val : ℤ)) : OK))},
      (isMaximal_span_pair p _ hr).isPrime, ?_, absNorm_span_pair p _ hr⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span (by simp)

/-- The quadratic (cyclotomic) splitting law for `ℚ(ζ₃)`: an unramified rational prime `p`
splits into two distinct primes iff `p ≡ 1 (mod 3)`, and is inert otherwise. This is the
simplest instance of splitting governed by congruence conditions (class field theory). -/
theorem splits_iff_one_mod_three (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    (∃ P Q : Ideal OK, P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : OK)} = P * Q) ↔ p % 3 = 1 := by
  constructor
  · rintro ⟨P, Q, hPprime, hQprime, hPQ, hspan⟩
    have hPle : Ideal.span {(p : OK)} ≤ P := by
      rw [hspan]
      exact (Ideal.mul_le_right (I := P) (J := Q))
    have hPnorm_dvd : Ideal.absNorm P ∣ p ^ 2 := by
      exact absNorm_span_natCast p ▸ Ideal.absNorm_dvd_absNorm_of_le hPle
    obtain ⟨k, hk2, hPnorm⟩ := (Nat.dvd_prime_pow hp).mp hPnorm_dvd
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hPnorm
      exact hPprime.ne_top (Ideal.absNorm_eq_one_iff.mp hPnorm)
    have hmul := _root_.map_mul Ideal.absNorm P Q
    have hspan' : Ideal.span {((p : ℕ) : OK)} = P * Q := by
      simpa using hspan
    rw [← hspan', absNorm_span_natCast] at hmul
    have hQnorm_ne_one : Ideal.absNorm Q ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact hQprime.ne_top
    have hPnorm_eq : Ideal.absNorm P = p := by
      interval_cases k
      · exact (hk0 rfl).elim
      · simpa using hPnorm
      · exfalso
        rw [hPnorm] at hmul
        have hQone : Ideal.absNorm Q = 1 :=
          (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2)
            (by rw [mul_one]; exact hmul)).symm
        exact hQnorm_ne_one hQone
    exact (exists_prime_norm_iff_one_mod_three p hp hp3).mp
      ⟨P, hPprime, hPle, hPnorm_eq⟩
  · intro hmod
    obtain ⟨P, hPprime, hPle, hPnorm⟩ :=
      (exists_prime_norm_iff_one_mod_three p hp hp3).mpr hmod
    obtain ⟨Q, hspan⟩ := Ideal.dvd_iff_le.mpr hPle
    have hQnorm : Ideal.absNorm Q = p := by
      have hmul := _root_.map_mul Ideal.absNorm P Q
      have hspan' : Ideal.span {((p : ℕ) : OK)} = P * Q := by
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
      have hram : ∃ R : Ideal OK, R.IsPrime ∧ Ideal.span {(p : OK)} ≤ R ^ 2 := by
        refine ⟨P, hPprime, ?_⟩
        rw [hspan, h, sq]
      exact hp3 ((ramified_iff_eq_three p hp).mp hram)
    exact ⟨P, Q, hPprime, hQprime, hPQ, by simpa using hspan⟩


end XYin.NumberField.CyclotomicThree
