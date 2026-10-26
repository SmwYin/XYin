/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevDefs

/-!
# Prime-ideal Euler product prerequisites

Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87` is not an imported dependency.
Contracts are adapted to pinned Lean 4.30.0. Local prerequisites precede their consumers. See the
declaration records for exact source matches and remaining port boundaries.
-/

noncomputable section
open Filter NumberField Topology Set UniqueFactorizationMonoid
open scoped nonZeroDivisors
namespace Cox.Chebotarev
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]
variable {S : Set (Ideal (𝓞 K))} {δ : ℝ}

/-- Planning source: NumberFieldEulerProduct.lean:47; statement placeholder. -/
def idealNormMultiplicity (n : ℕ) : ℕ :=
  Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}

/-- Planning source: NumberFieldEulerProduct.lean:501; statement placeholder. -/
theorem finite_absNormFiber (n : ℕ) :
    Finite {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} :=
  Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal L ↦ I.1)
    ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
    (fun _ _ _ _ ↦ Subtype.ext)

/-- Planning source: NumberFieldEulerProduct.lean:507; statement placeholder. -/
theorem tsum_absNormFiber {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    [IsTopologicalAddGroup M] (n : ℕ) (g : ℕ → M) :
    (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}, g (Ideal.absNorm y.1.1))
      = idealNormMultiplicity L n • g n :=
  (tsum_congr fun y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
    (tsum_const (g n))

/-- Planning source: NumberFieldEulerProduct.lean:246; statement placeholder. -/
theorem sum_idealNormMultiplicity_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity L k : ℝ))
      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
  classical
  have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal L | Ideal.absNorm I.1 = b}.Finite := fun b ↦
    Set.Finite.preimage (f := fun I : NonzeroIdeal L ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) b)
  have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity L k =
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
    have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal L ↦
      Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
    rw [show ((fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
        {I : NonzeroIdeal L | Ideal.absNorm I.1 ≤ n} by
      ext ⟨I, hI⟩
      simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
      exact ⟨fun h ↦ h.2, fun h ↦
        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
    exact key.symm
  have h_card_bridge : ∀ n : ℕ,
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} =
      Nat.card {I : (Ideal (𝓞 L))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
    fun n ↦ Nat.card_congr
      { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
          ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
        invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
          ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ L).comp
      tendsto_natCast_atTop_atTop).congr' ?_)
  filter_upwards with n
  simp only [Function.comp_apply, Real.rpow_one]
  rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
  push_cast
  rfl

/-- Planning source: NumberFieldEulerProduct.lean:50; statement placeholder. -/
theorem idealNormMultiplicity_zero : idealNormMultiplicity L 0 = 0 := by
  unfold idealNormMultiplicity
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩

/-- Planning source: NumberFieldEulerProduct.lean:283; statement placeholder. -/
theorem summable_idealNormMultiplicity_mul_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ ↦ ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ := by
  classical
  have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (f := fun n ↦ (idealNormMultiplicity L n : ℝ))
      (sum_idealNormMultiplicity_isBigO L) (fun _ ↦ Nat.cast_nonneg _) zero_le_one
      (by exact_mod_cast hs)
  have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s =
      fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
    funext n
    simp only [LSeries.term]
    split_ifs with hn
    · subst hn
      simp [idealNormMultiplicity_zero]
    · simp [Complex.cpow_neg, div_eq_mul_inv]
  exact (h_term_eq ▸ h_lss :
    Summable fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)).norm

/-- Planning source: NumberFieldEulerProduct.lean:194; statement placeholder. -/
theorem dedekindZeta_eq_tsum_idealNormMultiplicity {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold NumberField.dedekindZeta LSeries
  refine tsum_congr fun n ↦ ?_
  unfold LSeries.term
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    simp [idealNormMultiplicity_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · simp only [hn.ne', ↓reduceIte]
    rw [Complex.cpow_neg, div_eq_mul_inv]
    congr 1
    unfold idealNormMultiplicity
    have hequiv : {I : Ideal (𝓞 L) // Ideal.absNorm I = n} ≃
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} := by
      refine {
        toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
        invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
      intro h
      rw [h, Ideal.absNorm_bot] at hI
      omega
    exact_mod_cast Nat.card_congr hequiv

/-- Planning source: NumberFieldEulerProduct.lean:515; statement placeholder. -/
theorem hasSum_nonzeroIdeal_absNorm_cpow {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))
      (NumberField.dedekindZeta L s) := by
  classical
  set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1)
  have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
      (Ideal.absNorm (y.1).1 : ℂ) ^ (-s)) = (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) :=
    fun n ↦ by rw [tsum_absNormFiber L n fun k ↦ (k : ℂ) ^ (-s), nsmul_eq_mul]
  have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
      ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-s)‖) = ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ :=
    fun n ↦ by
      rw [tsum_absNormFiber L n fun k ↦ ‖(k : ℂ) ^ (-s)‖, nsmul_eq_mul, norm_mul,
        Complex.norm_natCast]
  have hsummable : Summable fun I : NonzeroIdeal L ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-s)‖ := by
    haveI := fun n : ℕ ↦ finite_absNormFiber L n
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
    exact (summable_idealNormMultiplicity_mul_cpow_neg L hs).congr fun n ↦ (hnorm n).symm
  have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦
      (Ideal.absNorm (e p).1 : ℂ) ^ (-s) :=
    (e.summable_iff (f := fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))).mpr
      hsummable.of_norm
  have hval_sum : (∑' I : NonzeroIdeal L, (Ideal.absNorm I.1 : ℂ) ^ (-s))
      = NumberField.dedekindZeta L s := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs,
      ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s)), hsummable_sigma.tsum_sigma]
    exact tsum_congr hval
  exact hval_sum ▸ hsummable.of_norm.hasSum

/-- Planning source: NumberFieldEulerProduct.lean:555; statement placeholder. -/
theorem factorization_prod_primePow_apply
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (e : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℕ)
    (𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 =
      ∑ 𝔭 ∈ S.attach, factorization (𝔭.1.1 ^ e 𝔭.1) 𝔮.1 := by
  classical
  induction S using Finset.induction with
  | empty => rw [Finset.attach_empty, Finset.prod_empty, Finset.sum_empty, factorization_one,
      Finsupp.coe_zero, Pi.zero_apply]
  | insert a s ha ih =>
    rw [Finset.attach_insert, Finset.prod_insert, Finset.sum_insert,
      factorization_mul (pow_ne_zero _ a.2.2)
        (Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)), Finsupp.add_apply,
      Finset.prod_image (fun x _ y _ h ↦ Subtype.ext (by simpa using h)),
      Finset.sum_image (fun x _ y _ h ↦ Subtype.ext (by simpa using h)), ih] <;>
    · rw [Finset.mem_image]
      rintro ⟨x, -, hx⟩
      exact ha ((Subtype.mk.inj hx) ▸ x.2)

/-- Planning source: NumberFieldEulerProduct.lean:545; statement placeholder. -/
theorem factorization_primePow_apply
    (𝔭 𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (n : ℕ) :
    factorization (𝔭.1 ^ n) 𝔮.1 = if 𝔮 = 𝔭 then n else 0 := by
  rw [factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_eq_count,
    normalizedFactors_irreducible (Ideal.prime_of_isPrime 𝔭.2.2 𝔭.2.1).irreducible,
    normalize_eq, Multiset.count_singleton]
  split_ifs <;> simp_all [Subtype.ext_iff]

/-- Planning source: NumberFieldEulerProduct.lean:577; statement placeholder. -/
theorem factorization_prod_primePow_eq
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (e : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℕ)
    (𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 = if 𝔮 ∈ S then e 𝔮 else 0 := by
  classical
  rw [factorization_prod_primePow_apply L S e 𝔮]
  simp_rw [factorization_primePow_apply L]
  by_cases h𝔮 : 𝔮 ∈ S
  · rw [if_pos h𝔮, Finset.sum_eq_single (⟨𝔮, h𝔮⟩ : {x // x ∈ S})]
    · rw [if_pos rfl]
    · rintro b _ hb
      rw [if_neg (fun h ↦ hb (Subtype.ext h.symm))]
    · exact fun h ↦ absurd (Finset.mem_attach S _) h
  · rw [if_neg h𝔮, Finset.sum_eq_zero]
    rintro ⟨b, hb⟩ -
    rw [if_neg (fun h : 𝔮 = b ↦ h𝔮 (h.symm ▸ hb))]

/-- Planning source: NumberFieldEulerProduct.lean:621; statement placeholder. -/
theorem factorization_idealOfExp_eq
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (f : S →₀ ℕ) (𝔮 : S) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ f 𝔭) 𝔮.1.1 = f 𝔮 := by
  classical
  have hprod : (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (fun q ↦ if h : q ∈ S then f ⟨q, h⟩ else 0) 𝔭.1)
      = ∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ f 𝔭 :=
    Finset.prod_congr rfl fun 𝔭 _ ↦ by simp only [dif_pos 𝔭.2]
  rw [← hprod, factorization_prod_primePow_eq L S
    (fun q ↦ if h : q ∈ S then f ⟨q, h⟩ else 0) 𝔮.1, if_pos 𝔮.2, dif_pos 𝔮.2]

/-- Planning source: NumberFieldEulerProduct.lean:632; statement placeholder. -/
theorem prod_primePow_count_eq (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (𝔞 : NonzeroIdeal L) (hsupp : ∀ p ∈ normalizedFactors 𝔞.1, ∃ 𝔭 ∈ S, 𝔭.1 = p) :
    (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (normalizedFactors 𝔞.1).count 𝔭.1.1) = 𝔞.1 := by
  classical
  rw [show (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (normalizedFactors 𝔞.1).count 𝔭.1.1)
      = ∏ p ∈ S.image (fun 𝔭 ↦ 𝔭.1), p ^ (normalizedFactors 𝔞.1).count p by
    rw [Finset.prod_image (fun x _ y _ h ↦ Subtype.ext h), ← Finset.prod_attach S
      (fun p ↦ p.1 ^ (normalizedFactors 𝔞.1).count p.1)]]
  rw [← Finset.prod_subset (s₁ := (normalizedFactors 𝔞.1).toFinset)
    (s₂ := S.image (fun 𝔭 ↦ 𝔭.1))
    (fun p hp ↦ by
      rw [Multiset.mem_toFinset] at hp
      obtain ⟨𝔭, h𝔭S, rfl⟩ := hsupp p hp
      exact Finset.mem_image.mpr ⟨𝔭, h𝔭S, rfl⟩)
    (fun p _ hp ↦ by
      rw [Multiset.mem_toFinset] at hp
      rw [Multiset.count_eq_zero_of_notMem hp, pow_zero])]
  conv_rhs => rw [← finprod_pow_count_eq_of_subsingleton_units 𝔞.2]
  exact (finprod_eq_finsetProd_of_mulSupport_subset _ (by
    intro p hp
    simp only [Function.mem_mulSupport] at hp
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    by_contra hc
    rw [Multiset.count_eq_zero_of_notMem hc, pow_zero] at hp
    exact hp rfl)).symm

/-- Planning source: NumberFieldEulerProduct.lean:597; statement placeholder. -/
def primeFactorsOf (𝔞 : NonzeroIdeal L) :
    Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
  (normalizedFactors 𝔞.1).toFinset.preimage
    (fun p : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ p.1) Subtype.val_injective.injOn

/-- Planning source: NumberFieldEulerProduct.lean:612; statement placeholder. -/
theorem mem_primeFactorsOf (𝔞 : NonzeroIdeal L) (p : Ideal (𝓞 L))
    (hp : p ∈ normalizedFactors 𝔞.1) :
    ∃ 𝔭 ∈ primeFactorsOf L 𝔞, 𝔭.1 = p := by
  refine ⟨⟨p, ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor p hp),
      (prime_of_normalized_factor p hp).ne_zero⟩⟩, ?_, rfl⟩
  rw [primeFactorsOf, Finset.mem_preimage, Multiset.mem_toFinset]
  exact hp

/-- Planning source: NumberFieldEulerProduct.lean:436; statement placeholder. -/
theorem norm_absNorm_cpow_neg_lt_one {s : ℂ} (hs : 1 < s.re)
    (𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := by
  have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h ↦ 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h ↦ 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h2 : 2 ≤ Ideal.absNorm 𝔭.1 := by omega
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h2.trans_lt' one_lt_two) (by linarith)

/-- Planning source: NumberFieldEulerProduct.lean:326; statement placeholder. -/
def insertPiEquiv {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) : ({i // i ∈ insert a s} → ℕ) ≃ ℕ × ({i // i ∈ s} → ℕ) :=
  ((Finset.subtypeInsertEquivOption ha).arrowCongr (Equiv.refl ℕ)).trans Equiv.piOptionEquivProd

/-- Planning source: NumberFieldEulerProduct.lean:330; statement placeholder. -/
theorem insertPiEquiv_fst {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) :
    (insertPiEquiv a s ha e).1 = e ⟨a, Finset.mem_insert_self a s⟩ := rfl

/-- Planning source: NumberFieldEulerProduct.lean:334; statement placeholder. -/
theorem insertPiEquiv_snd {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) (i : {i // i ∈ s}) :
    (insertPiEquiv a s ha e).2 i = e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ := rfl

/-- Planning source: NumberFieldEulerProduct.lean:340; statement placeholder. -/
theorem prodInsertAttach {ι : Type*} [DecidableEq ι] (g : ι → ℂ) (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) :
    ∏ i ∈ (insert a s).attach, g i.1 ^ e i =
      g a ^ (insertPiEquiv a s ha e).1 *
        ∏ i ∈ s.attach, g i.1 ^ (insertPiEquiv a s ha e).2 i := by
  rw [insertPiEquiv_fst]
  conv_rhs => rw [show (∏ i ∈ s.attach, g i.1 ^ (insertPiEquiv a s ha e).2 i)
    = ∏ i ∈ s.attach, g i.1 ^ e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ from
    Finset.prod_congr rfl fun i _ ↦ by rw [insertPiEquiv_snd]]
  rw [Finset.attach_insert, Finset.prod_insert, Finset.prod_image]
  · exact fun x _ y _ h ↦ Subtype.ext (Subtype.mk.inj h)
  · simpa only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and,
      Subtype.exists, exists_prop, exists_eq_right] using ha

/-- Planning source: NumberFieldEulerProduct.lean:367; statement placeholder.
One induction on the index set carries both conclusions, so they stay bundled in this
private auxiliary. -/
private theorem finsetGeometricProd_summable_and_hasSum {ι : Type*} (g : ι → ℂ)
    (hg : ∀ i, ‖g i‖ < 1) (s : Finset ι) :
    (Summable fun e : {i // i ∈ s} → ℕ ↦ ‖∏ i ∈ s.attach, g i.1 ^ e i‖) ∧
      HasSum (fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i)
        (∏ i ∈ s, (1 - g i)⁻¹) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · have h1 : (fun e : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ ‖∏ i ∈ Finset.attach ∅, g i.1 ^ e i‖)
          = fun _ ↦ (1 : ℝ) := by
        funext e
        simp [Finset.attach_empty]
      rw [h1]
      exact (hasSum_unique (fun _ : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ (1 : ℝ))).summable
    · have h1 : (fun e : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ ∏ i ∈ Finset.attach ∅, g i.1 ^ e i)
          = fun _ ↦ (1 : ℂ) := by
        funext e
        simp [Finset.attach_empty]
      rw [h1]
      exact hasSum_unique (fun _ : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ (1 : ℂ))
  | insert a s ha ih =>
    obtain ⟨ihsum, ihhas⟩ := ih
    rw [Finset.prod_insert ha]
    have hgeo : HasSum (fun n : ℕ ↦ g a ^ n) (1 - g a)⁻¹ :=
      hasSum_geometric_of_norm_lt_one (hg a)
    have hgeosum : Summable (fun n : ℕ ↦ ‖g a ^ n‖) := by
      simp_rw [norm_pow]
      exact summable_geometric_of_lt_one (norm_nonneg _) (hg a)
    have hprodsum : Summable (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) :=
      summable_mul_of_summable_norm (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeosum ihsum
    have hHsum : Summable (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        ‖g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i‖) :=
      Summable.mul_norm (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeosum ihsum
    have hHhas : HasSum (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) ((1 - g a)⁻¹ * ∏ i ∈ s, (1 - g i)⁻¹) :=
      HasSum.mul (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeo ihhas hprodsum
    refine ⟨?_, ?_⟩
    · have heq : (fun e : {i // i ∈ insert a s} → ℕ ↦ ‖∏ i ∈ (insert a s).attach, g i.1 ^ e i‖)
          = (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
              ‖g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i‖) ∘ insertPiEquiv a s ha := by
        funext e
        rw [Function.comp_apply, prodInsertAttach g a s ha e]
      rw [heq]
      exact (insertPiEquiv a s ha).summable_iff.mpr hHsum
    · have heq : (fun e : {i // i ∈ insert a s} → ℕ ↦ ∏ i ∈ (insert a s).attach, g i.1 ^ e i)
          = (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
              g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) ∘ insertPiEquiv a s ha := by
        funext e
        rw [Function.comp_apply, prodInsertAttach g a s ha e]
      rw [heq]
      exact (insertPiEquiv a s ha).hasSum_iff.mpr hHhas

/-- Planning source: NumberFieldEulerProduct.lean:426; statement placeholder. -/
theorem prod_natCast_cpow {ι : Type*} (S : Finset ι) (m : ι → ℕ) (z : ℂ) :
    (∏ i ∈ S, (m i : ℂ) ^ z) = ((∏ i ∈ S, m i : ℕ) : ℂ) ^ z := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]

/-- Planning source: NumberFieldEulerProduct.lean:471; statement placeholder. -/
theorem absNorm_prod_pow_of_primeIdeal
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    Ideal.absNorm (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) =
      ∏ 𝔭 ∈ S.attach, Ideal.absNorm 𝔭.1.1 ^ e 𝔭 := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun 𝔭 _ ↦ map_pow Ideal.absNorm 𝔭.1.1 (e 𝔭)

/-- Planning source: NumberFieldEulerProduct.lean:479; statement placeholder. -/
theorem prod_absNorm_cpow_eq_absNorm_prod_pow_cpow {s : ℂ}
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    (∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s)) =
      (Ideal.absNorm (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) : ℂ) ^ (-s) := by
  have hinner : ∀ 𝔭 ∈ S.attach,
      (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) =
        ((Ideal.absNorm 𝔭.1.1 ^ e 𝔭 : ℕ) : ℂ) ^ (-s) := fun 𝔭 _ ↦ by
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    ring_nf
  rw [Finset.prod_congr rfl hinner, prod_natCast_cpow, absNorm_prod_pow_of_primeIdeal]

omit [NumberField L] in
/-- Planning source: NumberFieldEulerProduct.lean:671; statement placeholder. -/
theorem weight_prod_primePow (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    w (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ S.attach, (w 𝔭.1.1) ^ e 𝔭 := by
  classical
  have wpow : ∀ (𝔭 : Ideal (𝓞 L)) (_ : 𝔭 ≠ ⊥) (k : ℕ), w (𝔭 ^ k) = (w 𝔭) ^ k := by
    intro 𝔭 h𝔭 k
    induction k with
    | zero => simpa using hw_one
    | succ n ih => rw [pow_succ, hw_mul (pow_ne_zero _ h𝔭) h𝔭, ih, pow_succ]
  have key : ∀ T : Finset S, w (∏ 𝔭 ∈ T, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ T, (w 𝔭.1.1) ^ e 𝔭 := by
    intro T
    induction T using Finset.induction with
    | empty => simpa using hw_one
    | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        hw_mul (pow_ne_zero _ a.1.2.2)
          (Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)),
        wpow a.1.1 a.1.2.2, ih]
  exact key S.attach

/-- Planning source: NumberFieldEulerProduct.lean:695; statement placeholder. -/
theorem weighted_prod_eulerFactor_eq_tsum {s : ℂ} (hs : 1 < s.re)
    (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (hw_norm : ∀ 𝔞, ‖w 𝔞‖ ≤ 1)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (idealOfExp : (S →₀ ℕ) → NonzeroIdeal L)
    (hidealOfExp : ∀ e : S →₀ ℕ,
      (idealOfExp e).1 = ∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭)
    (hinj : Function.Injective idealOfExp) :
    (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
      = ∑' 𝔞 : Set.range idealOfExp,
          w 𝔞.1.1 * (Ideal.absNorm 𝔞.1.1 : ℂ) ^ (-s) := by
  classical
  have hg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ‖w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := fun 𝔭 ↦
    ((norm_mul_le_of_le (hw_norm _) le_rfl).trans_eq (one_mul _)).trans_lt
      (norm_absNorm_cpow_neg_lt_one L hs 𝔭)
  have hHS := (finsetGeometricProd_summable_and_hasSum
    (fun 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) hg S).2
  have hsummand : ∀ e : S →₀ ℕ,
      (∏ 𝔭 ∈ S.attach, (w 𝔭.1.1 * (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)
        = w (idealOfExp e).1 * (Ideal.absNorm (idealOfExp e).1 : ℂ) ^ (-s) := fun e ↦ by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib,
      show (∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)
        = ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) from
      Finset.prod_congr rfl fun 𝔭 _ ↦ by
        rw [← Complex.cpow_nat_mul]
        ring_nf,
      prod_absNorm_cpow_eq_absNorm_prod_pow_cpow L S (fun 𝔭 ↦ e 𝔭),
      ← weight_prod_primePow L w hw_one hw_mul S (fun 𝔭 ↦ e 𝔭), hidealOfExp e]
  have hHS' : HasSum
      (fun e : S →₀ ℕ ↦ w (idealOfExp e).1 * (Ideal.absNorm (idealOfExp e).1 : ℂ) ^ (-s))
      (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹) := by
    have hbase := (Finsupp.equivFunOnFinite (α := S) (M := ℕ)).hasSum_iff.mpr hHS
    refine hbase.congr_fun fun e ↦ ?_
    simp only [Function.comp_apply, Finsupp.equivFunOnFinite_apply]
    exact (hsummand e).symm
  rw [← hHS'.tsum_eq]
  exact (tsum_range
    (fun 𝔞 : NonzeroIdeal L ↦ w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) hinj).symm

/-- Planning source: NumberFieldEulerProduct.lean:743; statement placeholder. -/
theorem weighted_eulerProduct_eq_tsum {s : ℂ} (hs : 1 < s.re)
    (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (hw_norm : ∀ 𝔞, ‖w 𝔞‖ ≤ 1) :
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
      = ∑' 𝔞 : NonzeroIdeal L, w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) := by
  classical
  set P := {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}
  set Dw : NonzeroIdeal L → ℂ := fun 𝔞 ↦ w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) with hDw
  set idealOfExp : (S : Finset P) → (S →₀ ℕ) → NonzeroIdeal L :=
    fun S e ↦ ⟨∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭,
      Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)⟩ with hidealOfExp
  have hnormD : Summable fun 𝔞 : NonzeroIdeal L ↦ ‖Dw 𝔞‖ := by
    refine ((hasSum_nonzeroIdeal_absNorm_cpow L hs).summable.norm).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun 𝔞 ↦ ?_)
    rw [hDw]
    exact (norm_mul_le_of_le (hw_norm _) le_rfl).trans_eq (one_mul _)
  have hinj : ∀ S : Finset P, Function.Injective (idealOfExp S) := by
    intro S e e' h
    rw [hidealOfExp, Subtype.mk.injEq] at h
    ext 𝔮
    rw [← factorization_idealOfExp_eq L S e 𝔮, ← factorization_idealOfExp_eq L S e' 𝔮, h]
  have hmem : ∀ (S : Finset P) (𝔞 : NonzeroIdeal L),
      (∀ p ∈ normalizedFactors 𝔞.1, ∃ 𝔭 ∈ S, 𝔭.1 = p) →
      𝔞 ∈ Set.range (idealOfExp S) := by
    intro S 𝔞 hsupp
    refine ⟨Finsupp.onFinset S.attach
      (fun 𝔭 ↦ (normalizedFactors 𝔞.1).count 𝔭.1.1) (by simp), ?_⟩
    rw [hidealOfExp, Subtype.ext_iff]
    simpa only [Finsupp.onFinset_apply] using prod_primePow_count_eq L S 𝔞 hsupp
  have hpartial : ∀ S : Finset P,
      (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
        = ∑' 𝔞 : Set.range (idealOfExp S), Dw 𝔞.1 := by
    intro S
    exact weighted_prod_eulerFactor_eq_tsum L hs w hw_one hw_mul hw_norm S (idealOfExp S)
      (fun e ↦ rfl) (hinj S)
  refine HasProd.tprod_eq ?_
  rw [HasProd, SummationFilter.unconditional, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F, hF⟩ := ((tendsto_tsum_compl_atTop_zero (fun 𝔞 ↦ ‖Dw 𝔞‖)).eventually
    (gt_mem_nhds hε)).exists
  refine ⟨F.biUnion (primeFactorsOf L), fun S hS ↦ ?_⟩
  have hF_sub : ∀ 𝔞 ∈ F, 𝔞 ∈ Set.range (idealOfExp S) := by
    intro 𝔞 h𝔞F
    refine hmem S 𝔞 fun p hp ↦ ?_
    obtain ⟨𝔭, h𝔭, rfl⟩ := mem_primeFactorsOf L 𝔞 p hp
    exact ⟨𝔭, hS (Finset.mem_biUnion.mpr ⟨𝔞, h𝔞F, h𝔭⟩), rfl⟩
  rw [dist_eq_norm, hpartial S]
  have hsplit : ∑' 𝔞 : NonzeroIdeal L, Dw 𝔞 =
      (∑' 𝔞 : Set.range (idealOfExp S), Dw 𝔞.1) +
        ∑' 𝔞 : ↥(Set.range (idealOfExp S))ᶜ, Dw 𝔞.1 :=
    (hnormD.of_norm.tsum_subtype_add_tsum_subtype_compl _).symm
  rw [hsplit, sub_add_cancel_left, norm_neg]
  refine (norm_tsum_le_tsum_norm (hnormD.subtype _)).trans_lt ?_
  refine lt_of_le_of_lt ?_ hF
  refine (hnormD.subtype _).tsum_le_tsum_of_inj
    (fun 𝔞 : ↥(Set.range (idealOfExp S))ᶜ ↦
      (⟨𝔞.1, fun h ↦ 𝔞.2 (hF_sub 𝔞.1 h)⟩ : {x // x ∉ F}))
    (fun x y h ↦ Subtype.ext (congrArg (fun z : {x // x ∉ F} ↦ (z : NonzeroIdeal L)) h))
    (fun _ _ ↦ norm_nonneg _) (fun _ ↦ le_rfl) (hnormD.subtype _)

/-- Planning source: NumberFieldEulerProduct.lean:808; statement placeholder. -/
theorem dedekindZeta_eq_tprod_primeIdeal {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ := by
  have hw := weighted_eulerProduct_eq_tsum L hs (fun _ ↦ 1) (by simp) (by simp) (by simp)
  simp only [one_mul] at hw
  exact (hw.trans (hasSum_nonzeroIdeal_absNorm_cpow L hs).tsum_eq).symm

end Cox.Chebotarev
