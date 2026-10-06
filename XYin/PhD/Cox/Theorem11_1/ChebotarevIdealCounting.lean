/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevIdealFrobenius
import XYin.PhD.Cox.Theorem11_1.ChebotarevCyclotomicFrobenius
import XYin.PhD.Cox.Theorem11_1.ChebotarevDensity
import XYin.PhD.Cox.Theorem11_1.ChebotarevNormResidueCount
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicUnramified
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Cyclotomic ideal counts

Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87`. The norm-residue and
Frobenius-generation prerequisites are explicit source-local contracts.
-/
noncomputable section
open NumberField Filter Topology Set UniqueFactorizationMonoid nonZeroDivisors
namespace Cox.Chebotarev

/-- Planning source: ZetaProduct.lean:615; ideal-count child. -/
theorem unramifiedIn_of_coprime_absNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hcop : (Ideal.absNorm 𝔭).Coprime m) :
    UnramifiedIn K L 𝔭 := by
  classical
  refine ⟨h𝔭, fun 𝔓 h𝔓max h𝔓lo ↦ ?_⟩
  haveI := h𝔓lo
  haveI : 𝔓.IsPrime := h𝔓max.isPrime
  rw [← not_dvd_differentIdeal_iff (A := 𝓞 K) (B := 𝓞 L)]
  intro hdvd
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L
    (Set.mem_singleton m) (NeZero.ne m)
  set ζ𝓞 : 𝓞 L := hζ.toInteger with hζ𝓞
  have hpow : ζ𝓞 ^ m = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hdvd_pol : minpoly (𝓞 K) ζ𝓞 ∣ Polynomial.X ^ m - 1 := by
    refine minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral ζ𝓞) ?_
    simp [hpow]
  obtain ⟨g, hg⟩ := hdvd_pol
  have hkey : (m : 𝓞 L) * ζ𝓞 ^ (m - 1)
      = Polynomial.aeval ζ𝓞 (Polynomial.derivative (minpoly (𝓞 K) ζ𝓞))
        * Polynomial.aeval ζ𝓞 g := by
    have hder := congrArg (Polynomial.aeval ζ𝓞 ∘ Polynomial.derivative) hg
    simp only [Function.comp_apply, Polynomial.derivative_one,
      Polynomial.derivative_X_pow, Polynomial.derivative_mul, map_sub, map_mul, map_add,
      map_pow, Polynomial.aeval_X, minpoly.aeval, zero_mul, add_zero,
      sub_zero, Polynomial.aeval_C] at hder
    simpa using hder
  have hadj : Algebra.adjoin K {algebraMap (𝓞 L) L ζ𝓞} = ⊤ := by
    have : algebraMap (𝓞 L) L ζ𝓞 = ζ := hζ.coe_toInteger
    rw [this]
    exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have hdiff_dvd : differentIdeal (𝓞 K) (𝓞 L)
      ∣ Ideal.span {Polynomial.aeval ζ𝓞 (Polynomial.derivative (minpoly (𝓞 K) ζ𝓞))} :=
    ⟨conductor (𝓞 K) ζ𝓞, by
      rw [← conductor_mul_differentIdeal (𝓞 K) K L ζ𝓞 hadj]; ring⟩
  have hmem : (m : 𝓞 L) * ζ𝓞 ^ (m - 1) ∈ 𝔓 := by
    rw [hkey]
    exact Ideal.mul_mem_right _ _
      ((Ideal.dvd_iff_le.mp (dvd_trans hdvd hdiff_dvd)) (Ideal.mem_span_singleton_self _))
  have hm𝔓 : ((m : ℕ) : 𝓞 L) ∈ 𝔓 := by
    rcases ‹𝔓.IsPrime›.mem_or_mem hmem with h | h
    · exact h
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h
        ((IsUnit.of_pow_eq_one hpow (NeZero.ne m)).pow _)) ‹𝔓.IsPrime›.ne_top
  have hm𝔭 : ((m : ℕ) : 𝓞 K) ∈ 𝔭 := by
    have hmap : algebraMap (𝓞 K) (𝓞 L) ((m : ℕ) : 𝓞 K) ∈ 𝔓 := by
      rwa [map_natCast]
    rw [h𝔓lo.over]
    exact Ideal.mem_comap.mpr hmap
  have hdvd_norm : Ideal.absNorm 𝔭 ∣ m ^ Module.finrank ℤ (𝓞 K) := by
    have hle : Ideal.span {((m : ℕ) : 𝓞 K)} ≤ 𝔭 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hm𝔭
    have hd := Ideal.absNorm_dvd_absNorm_of_le hle
    rwa [Ideal.absNorm_span_singleton, show ((m : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ) by
        push_cast; rfl,
      Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
  exact absurd (Ideal.absNorm_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hcop.pow_right _) dvd_rfl hdvd_norm))
    ‹𝔭.IsPrime›.ne_top

/-- Planning source: ZetaProduct.lean:679; ideal-count child. -/
theorem autToPow_frobeniusIdeal
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ m) (𝔠 : Ideal (𝓞 K)) (h𝔠 : 𝔠 ≠ ⊥)
    (hcop : (Ideal.absNorm 𝔠).Coprime m) :
    hζ.autToPow K (frobeniusIdeal K L 𝔠) = ZMod.unitOfCoprime (Ideal.absNorm 𝔠) hcop := by
  classical
  revert h𝔠 hcop
  induction 𝔠 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h𝔠 _ ↦ absurd rfl h𝔠
  | h₂ u hu =>
      intro _ hcop
      obtain rfl : u = ⊤ := Ideal.isUnit_iff.mp hu
      rw [frobeniusIdeal_one, map_one]
      exact Units.ext (by simp [ZMod.coe_unitOfCoprime])
  | h₃ a p ha hp ih =>
      intro hpa hcop
      have hp' : p ≠ ⊥ := hp.ne_zero
      have ha' : a ≠ ⊥ := ha
      haveI : p.IsPrime := Ideal.isPrime_of_prime hp
      have hsplit : Ideal.absNorm (p * a) = Ideal.absNorm p * Ideal.absNorm a :=
        map_mul Ideal.absNorm p a
      have hcp : (Ideal.absNorm p).Coprime m :=
        Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) (hsplit ▸ hcop)
      have hca : (Ideal.absNorm a).Coprime m :=
        Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) (hsplit ▸ hcop)
      rw [frobeniusIdeal_mul K L hp' ha', map_mul,
        frobeniusIdeal_apply_prime K L p hp',
        autToPow_frobeniusClass_out K L m hζ p
          (unramifiedIn_of_coprime_absNorm K L m p hp' hcp) hcp,
        ih ha' hca]
      exact Units.ext (by push_cast [ZMod.coe_unitOfCoprime, hsplit]; ring)

/-- Planning source: ZetaProduct.lean:719; ideal-count child. -/
theorem card_good_fibre_eq_card_residue
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ m) (h : Gal(L/K)) (X : ℕ) :
    Nat.card {𝔠 : Ideal (𝓞 K) // 𝔠 ≠ ⊥ ∧ Ideal.absNorm 𝔠 ≤ X ∧
        (Ideal.absNorm 𝔠).Coprime m ∧ frobeniusIdeal K L 𝔠 = h}
      = Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ X ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m))
          = ((hζ.autToPow K h : (ZMod m)ˣ) : ZMod m)} := by
  classical
  refine Nat.card_congr
    { toFun := fun 𝔠 ↦ ⟨⟨𝔠.1, mem_nonZeroDivisors_of_ne_zero 𝔠.2.1⟩, 𝔠.2.2.1, by
        obtain ⟨𝔠, h0, hX, hcp, hfr⟩ := 𝔠
        subst hfr
        rw [autToPow_frobeniusIdeal K L m hζ 𝔠 h0 hcp, ZMod.coe_unitOfCoprime]⟩
      invFun := fun I ↦ ⟨(I.1 : Ideal (𝓞 K)), ?_⟩
      left_inv := fun 𝔠 ↦ Subtype.ext rfl
      right_inv := fun I ↦ Subtype.ext (Subtype.ext rfl) }
  have h0 : (I.1 : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa using nonZeroDivisors.coe_ne_zero I.1
  have hcp : (Ideal.absNorm (I.1 : Ideal (𝓞 K))).Coprime m := by
    refine (ZMod.isUnit_iff_coprime _ m).mp ?_
    rw [I.2.2]
    exact (hζ.autToPow K h).isUnit
  have hfr : frobeniusIdeal K L (I.1 : Ideal (𝓞 K)) = h := by
    refine hζ.autToPow_injective (K := K) ?_
    rw [autToPow_frobeniusIdeal K L m hζ _ h0 hcp]
    exact Units.ext (by rw [ZMod.coe_unitOfCoprime, I.2.2])
  exact ⟨h0, I.2.1, hcp, hfr⟩

/-- Planning source: ZetaProduct.lean:753; ideal-count child. -/
def badPart (K : Type*) [Field K] [NumberField K] (m : ℕ)
    (𝔞 : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).filter
    fun 𝔭 ↦ ¬(Ideal.absNorm 𝔭).Coprime m).prod

/-- Planning source: ZetaProduct.lean:759; ideal-count child. -/
def goodPart (K : Type*) [Field K] [NumberField K] (m : ℕ)
    (𝔞 : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).filter
    fun 𝔭 ↦ (Ideal.absNorm 𝔭).Coprime m).prod

/-- Planning source: ZetaProduct.lean:768; ideal-count child. -/
theorem prod_filter_normalizedFactors_ne_bot (K : Type*) [Field K] [NumberField K] (𝔞 : Ideal (𝓞 K))
    (p : Ideal (𝓞 K) → Prop) [DecidablePred p] :
    ((UniqueFactorizationMonoid.normalizedFactors 𝔞).filter p).prod ≠ ⊥ :=
  Multiset.prod_ne_zero fun h0 ↦ (UniqueFactorizationMonoid.prime_of_normalized_factor _
    (Multiset.mem_of_mem_filter h0)).ne_zero rfl

/-- Planning source: ZetaProduct.lean:774; ideal-count child. -/
theorem goodPart_mul_badPart (K : Type*) [Field K] [NumberField K] (m : ℕ) (𝔞 : Ideal (𝓞 K))
    (h𝔞 : 𝔞 ≠ ⊥) :
    goodPart K m 𝔞 * badPart K m 𝔞 = 𝔞 := by
  rw [goodPart, badPart, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self h𝔞

/-- Planning source: ZetaProduct.lean:779; ideal-count child. -/
theorem badPart_ne_bot (K : Type*) [Field K] [NumberField K] (m : ℕ) (𝔞 : Ideal (𝓞 K)) :
    badPart K m 𝔞 ≠ ⊥ :=
  prod_filter_normalizedFactors_ne_bot K 𝔞 _

/-- Planning source: ZetaProduct.lean:782; ideal-count child. -/
theorem goodPart_ne_bot (K : Type*) [Field K] [NumberField K] (m : ℕ) (𝔞 : Ideal (𝓞 K)) :
    goodPart K m 𝔞 ≠ ⊥ :=
  prod_filter_normalizedFactors_ne_bot K 𝔞 _

/-- Planning source: ZetaProduct.lean:785; ideal-count child. -/
theorem absNorm_goodPart_coprime (K : Type*) [Field K] [NumberField K] (m : ℕ) (𝔞 : Ideal (𝓞 K)) :
    (Ideal.absNorm (goodPart K m 𝔞)).Coprime m := by
  rw [goodPart, map_multiset_prod]
  refine Multiset.prod_induction (fun n : ℕ ↦ n.Coprime m) _
    (fun a b ha hb ↦ Nat.Coprime.mul_left ha hb) (Nat.coprime_one_left m) fun n hn ↦ ?_
  obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hn
  exact (Multiset.mem_filter.mp h𝔭).2

/-- Planning source: ZetaProduct.lean:793, first conclusion; ideal-count child. -/
theorem mem_factors_of_mem_factors_badPart (K : Type*) [Field K] [NumberField K] (m : ℕ)
    {𝔞 : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 K)}
    (h𝔭 : 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors (badPart K m 𝔞)) :
    𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞 := by
  classical
  rw [badPart, UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (fun 𝔮 h𝔮 ↦
    UniqueFactorizationMonoid.prime_of_normalized_factor _
      (Multiset.mem_of_mem_filter h𝔮))] at h𝔭
  exact Multiset.mem_of_mem_filter h𝔭

/-- Planning source: ZetaProduct.lean:793, second conclusion; ideal-count child. -/
theorem not_coprime_absNorm_of_mem_factors_badPart (K : Type*) [Field K] [NumberField K]
    (m : ℕ) {𝔞 : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 K)}
    (h𝔭 : 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors (badPart K m 𝔞)) :
    ¬(Ideal.absNorm 𝔭).Coprime m := by
  classical
  rw [badPart, UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (fun 𝔮 h𝔮 ↦
    UniqueFactorizationMonoid.prime_of_normalized_factor _
      (Multiset.mem_of_mem_filter h𝔮))] at h𝔭
  exact (Multiset.mem_filter.mp h𝔭).2

/-- Planning source: ZetaProduct.lean:804; ideal-count child. -/
theorem coprime_absNorm_of_mem_factors_of_coprime (K : Type*) [Field K] [NumberField K] (m : ℕ)
    {𝔠 : Ideal (𝓞 K)}
    (hcop : (Ideal.absNorm 𝔠).Coprime m) {𝔮 : Ideal (𝓞 K)}
    (h𝔮 : 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠) :
    (Ideal.absNorm 𝔮).Coprime m :=
  Nat.Coprime.coprime_dvd_left
    (Ideal.absNorm_dvd_absNorm_of_le
      (Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔮))) hcop

/-- Planning source: ZetaProduct.lean:815; ideal-count child. -/
theorem goodPart_mul_eq (K : Type*) [Field K] [NumberField K] (m : ℕ) {𝔠 𝔟 : Ideal (𝓞 K)}
    (h𝔠 : 𝔠 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥)
    (hc : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠, (Ideal.absNorm 𝔭).Coprime m)
    (hb : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, ¬(Ideal.absNorm 𝔭).Coprime m) :
    goodPart K m (𝔠 * 𝔟) = 𝔠 := by
  classical
  rw [goodPart, UniqueFactorizationMonoid.normalizedFactors_mul h𝔠 h𝔟, Multiset.filter_add,
    Multiset.filter_eq_self.mpr hc, Multiset.filter_eq_nil.mpr hb, add_zero]
  exact Ideal.prod_normalizedFactors_eq_self h𝔠

/-- Planning source: ZetaProduct.lean:825; ideal-count child. -/
theorem badPart_mul_eq (K : Type*) [Field K] [NumberField K] (m : ℕ) {𝔠 𝔟 : Ideal (𝓞 K)}
    (h𝔠 : 𝔠 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥)
    (hc : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠, (Ideal.absNorm 𝔭).Coprime m)
    (hb : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, ¬(Ideal.absNorm 𝔭).Coprime m) :
    badPart K m (𝔠 * 𝔟) = 𝔟 := by
  classical
  rw [badPart, UniqueFactorizationMonoid.normalizedFactors_mul h𝔠 h𝔟, Multiset.filter_add,
    Multiset.filter_eq_nil.mpr (fun 𝔭 h𝔭 ↦ not_not.mpr (hc 𝔭 h𝔭)),
    Multiset.filter_eq_self.mpr hb, zero_add]
  exact Ideal.prod_normalizedFactors_eq_self h𝔟

/-- Planning source: ZetaProduct.lean:850; ideal-count child. -/
theorem card_fibre_eq_card_good_fibre
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (g : Gal(L/K)) (N : ℕ) {𝔟 : Ideal (𝓞 K)} (h𝔟 : 𝔟 ≠ ⊥)
    (hbU : ∀ 𝔭 ∈ normalizedFactors 𝔟, UnramifiedIn K L 𝔭)
    (hbn : ∀ 𝔭 ∈ normalizedFactors 𝔟, ¬(Ideal.absNorm 𝔭).Coprime m) :
    Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
            frobeniusIdeal K L 𝔞 = g ∧ badPart K m 𝔞 = 𝔟}
        = Nat.card {𝔠 : Ideal (𝓞 K) // 𝔠 ≠ ⊥ ∧ Ideal.absNorm 𝔠 ≤ N / Ideal.absNorm 𝔟 ∧
            (Ideal.absNorm 𝔠).Coprime m ∧ frobeniusIdeal K L 𝔠 = g * (frobeniusIdeal K L 𝔟)⁻¹} := by
  classical
  have hNb : 0 < Ideal.absNorm 𝔟 :=
    Nat.pos_of_ne_zero fun h ↦ h𝔟 (Ideal.absNorm_eq_zero_iff.mp h)
  refine Nat.card_congr
    { toFun := fun 𝔞 ↦ ⟨goodPart K m 𝔞.1, goodPart_ne_bot K m 𝔞.1, ?_, ?_, ?_⟩
      invFun := fun 𝔠 ↦ ⟨𝔠.1 * 𝔟, ?_, ?_, ?_, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨𝔞, h0, hN, _, _, hbad⟩ := 𝔞
    have hgood : goodPart K m 𝔞 * 𝔟 = 𝔞 := hbad ▸ goodPart_mul_badPart K m 𝔞 h0
    refine (Nat.le_div_iff_mul_le hNb).mpr ?_
    rw [← map_mul Ideal.absNorm, hgood]
    exact hN
  · exact absNorm_goodPart_coprime K m 𝔞.1
  · obtain ⟨𝔞, h0, _, _, hfr, hbad⟩ := 𝔞
    have hgood : goodPart K m 𝔞 * 𝔟 = 𝔞 := hbad ▸ goodPart_mul_badPart K m 𝔞 h0
    refine eq_mul_inv_of_mul_eq ?_
    rw [← frobeniusIdeal_mul K L (goodPart_ne_bot K m 𝔞) h𝔟, hgood, hfr]
  · exact mul_ne_zero 𝔠.2.1 h𝔟
  · obtain ⟨𝔠, h0, hN, _, _⟩ := 𝔠
    rw [map_mul Ideal.absNorm]
    exact (Nat.le_div_iff_mul_le hNb).mp hN
  · obtain ⟨𝔠, h0, _, hcop, _⟩ := 𝔠
    intro 𝔭 h𝔭
    rw [normalizedFactors_mul h0 h𝔟, Multiset.mem_add] at h𝔭
    rcases h𝔭 with h𝔭 | h𝔭
    · haveI : 𝔭.IsPrime := Ideal.isPrime_of_prime (prime_of_normalized_factor _ h𝔭)
      exact unramifiedIn_of_coprime_absNorm K L m 𝔭
        (prime_of_normalized_factor _ h𝔭).ne_zero
        (coprime_absNorm_of_mem_factors_of_coprime K m hcop h𝔭)
    · exact hbU 𝔭 h𝔭
  · obtain ⟨𝔠, h0, _, _, hfr⟩ := 𝔠
    rw [frobeniusIdeal_mul K L h0 h𝔟, hfr, inv_mul_cancel_right]
  · obtain ⟨𝔠, h0, _, hcop, _⟩ := 𝔠
    exact badPart_mul_eq K m h0 h𝔟
      (fun 𝔭 h𝔭 ↦ coprime_absNorm_of_mem_factors_of_coprime K m hcop h𝔭) hbn
  · rintro ⟨𝔞, h0, _, _, _, hbad⟩
    apply Subtype.ext
    simp only
    rw [← hbad, goodPart_mul_badPart K m 𝔞 h0]
  · rintro ⟨𝔠, h0, _, hcop, _⟩
    apply Subtype.ext
    simp only
    exact goodPart_mul_eq K m h0 h𝔟
      (fun 𝔭 h𝔭 ↦ coprime_absNorm_of_mem_factors_of_coprime K m hcop h𝔭) hbn

/-- Planning source: ZetaProduct.lean:914; ideal-count child. -/
def IsBadPart (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L] [IsGalois K L]
    (m : ℕ) (N : ℕ) (𝔟 : Ideal (𝓞 K)) : Prop :=
  𝔟 ≠ ⊥ ∧ (∀ 𝔭 ∈ normalizedFactors 𝔟, UnramifiedIn K L 𝔭 ∧ ¬(Ideal.absNorm 𝔭).Coprime m) ∧
    Ideal.absNorm 𝔟 ≤ N

/-- Planning source: ZetaProduct.lean:922; ideal-count child. -/
theorem finite_isBadPart (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsGalois K L] (m : ℕ) (N : ℕ) : {𝔟 : Ideal (𝓞 K) | IsBadPart K L m N 𝔟}.Finite :=
  (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).subset fun _ h𝔟 ↦ h𝔟.2.2

/-- Planning source: ZetaProduct.lean:927; ideal-count child. -/
theorem finite_L2 (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsMulCommutative Gal(L/K)] (g : Gal(L/K)) (N : ℕ) :
    Finite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
      (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g} := by
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ N} :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
  exact Finite.of_injective (β := {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ N})
    (fun 𝔞 ↦ ⟨𝔞.1, 𝔞.2.2.1⟩)
    (fun _ _ hab ↦ Subtype.ext (by simpa using hab))

/-- Planning source: ZetaProduct.lean:942; ideal-count child. -/
theorem card_L2_eq_sum_fibres (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsMulCommutative Gal(L/K)] (m : ℕ) (g : Gal(L/K)) (N : ℕ) :
    Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g}
        = ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
              frobeniusIdeal K L 𝔞 = g ∧ badPart K m 𝔞 = 𝔟} := by
  classical
  set L2 := {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
    (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g}
  have hbadmem : ∀ 𝔞 : L2, IsBadPart K L m N (badPart K m 𝔞.1) := by
    rintro ⟨𝔞, h0, hN, hU, _⟩
    refine ⟨badPart_ne_bot K m 𝔞, fun 𝔭 h𝔭 ↦ ?_, ?_⟩
    · exact ⟨hU 𝔭 (mem_factors_of_mem_factors_badPart K m h𝔭),
        not_coprime_absNorm_of_mem_factors_badPart K m h𝔭⟩
    · have hdvd : badPart K m 𝔞 ∣ 𝔞 := by
        rw [badPart]
        conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self h0]
        exact Multiset.prod_dvd_prod_of_le (Multiset.filter_le _ _)
      exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero
        (fun h ↦ h0 (Ideal.absNorm_eq_zero_iff.mp h)))
        (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd))) hN
  haveI := finite_L2 K L g N
  set F : L2 → (finite_isBadPart K L m N).toFinset :=
    fun 𝔞 ↦ ⟨badPart K m 𝔞.1, (finite_isBadPart K L m N).mem_toFinset.mpr (hbadmem 𝔞)⟩
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv F).symm, Nat.card_sigma,
    ← Finset.sum_coe_sort (finite_isBadPart K L m N).toFinset]
  refine Finset.sum_congr rfl fun 𝔟 _ ↦ ?_
  refine Nat.card_congr
    { toFun := fun x ↦ ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1, x.1.2.2.2.2,
        Subtype.ext_iff.mp x.2⟩
      invFun := fun y ↦ ⟨⟨y.1, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2.1⟩,
        Subtype.ext y.2.2.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- Planning source: ZetaProduct.lean:982; ideal-count child. -/
theorem card_L2_eq_sum_residue (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ m) (g : Gal(L/K)) (N : ℕ) :
    Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g}
        = ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          Nat.card {I : (Ideal (𝓞 K))⁰ //
            Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N / Ideal.absNorm 𝔟 ∧
              ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m))
                = ((hζ.autToPow K (g * (frobeniusIdeal K L 𝔟)⁻¹) : (ZMod m)ˣ) : ZMod m)} := by
  rw [card_L2_eq_sum_fibres K L m g N]
  refine Finset.sum_congr rfl fun 𝔟 h𝔟 ↦ ?_
  rw [Set.Finite.mem_toFinset] at h𝔟
  obtain ⟨h0, hbfac, _⟩ := h𝔟
  rw [card_fibre_eq_card_good_fibre K L m g N h0 (fun 𝔭 h ↦ (hbfac 𝔭 h).1)
      (fun 𝔭 h ↦ (hbfac 𝔭 h).2),
    card_good_fibre_eq_card_residue K L m hζ (g * (frobeniusIdeal K L 𝔟)⁻¹) (N / Ideal.absNorm 𝔟)]

/-- Planning source: ZetaProduct.lean:1087; ideal-count child. -/
theorem pow_count_dvd_prod {α : Type*} [CommMonoid α] [DecidableEq α] (a : α)
    (s : Multiset α) : a ^ s.count a ∣ s.prod :=
  (Multiset.prod_replicate (s.count a) a) ▸
    Multiset.prod_dvd_prod_of_le (Multiset.le_count_iff_replicate_le.mp le_rfl)

/-- Planning source: ZetaProduct.lean:1094; ideal-count child. -/
theorem prod_pow_count_normalizedFactors_eq (K : Type*) [Field K] [NumberField K]
    (P : Finset (Ideal (𝓞 K))) {𝔠 : Ideal (𝓞 K)} (h0 : 𝔠 ≠ ⊥)
    (hP : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠, 𝔭 ∈ P) :
    𝔠 = ∏ 𝔭 ∈ P, 𝔭 ^ (UniqueFactorizationMonoid.normalizedFactors 𝔠).count 𝔭 := by
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self h0]
  rw [Finset.prod_multiset_count]
  refine Finset.prod_subset (fun 𝔭 h ↦ hP 𝔭 (Multiset.mem_toFinset.mp h)) ?_
  intro 𝔭 _ hnotin
  rw [Multiset.count_eq_zero.mpr (fun h ↦ hnotin (Multiset.mem_toFinset.mpr h)), pow_zero]

/-- Planning source: ZetaProduct.lean:1106; ideal-count child. -/
theorem count_normalizedFactors_le_log {K : Type*} [Field K] [NumberField K]
    {𝔭 𝔟 : Ideal (𝓞 K)} (h𝔭p : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥) (hb0 : 𝔟 ≠ ⊥) {N : ℕ}
    (hbN : Ideal.absNorm 𝔟 ≤ N) :
    (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 ≤ Nat.log 2 N := by
  have hk : 𝔭 ^ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 ∣ 𝔟 := by
    have hd := pow_count_dvd_prod 𝔭 (UniqueFactorizationMonoid.normalizedFactors 𝔟)
    rwa [Ideal.prod_normalizedFactors_eq_self hb0] at hd
  have hN𝔭2 : 2 ≤ Ideal.absNorm 𝔭 := by
    have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ h𝔭p.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ h𝔭0 (Ideal.absNorm_eq_zero_iff.mp h)
    omega
  have hb0' : Ideal.absNorm 𝔟 ≠ 0 := fun h ↦ hb0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hdvd : Ideal.absNorm 𝔭 ^ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭
      ∣ Ideal.absNorm 𝔟 := by
    have := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hk); rwa [map_pow] at this
  exact Nat.le_log_of_pow_le (by norm_num) (le_trans (Nat.pow_le_pow_left hN𝔭2 _)
    (le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hb0') hdvd) hbN))

/-- Planning source: ZetaProduct.lean:1126; ideal-count child. -/
theorem absNorm_rpow_eq_prod_attach_count (K : Type*) [Field K] [NumberField K]
    (P : Finset (Ideal (𝓞 K))) {𝔟 : Ideal (𝓞 K)} (h0 : 𝔟 ≠ ⊥)
    (hP : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, 𝔭 ∈ P) (e : ℝ) :
    (Ideal.absNorm 𝔟 : ℝ) ^ e = ∏ 𝔭 ∈ P.attach, (((Ideal.absNorm 𝔭.1 : ℝ)) ^ e) ^
      (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭.1 := by
  have hNprod : Ideal.absNorm 𝔟 =
      ∏ 𝔭 ∈ P, (Ideal.absNorm 𝔭) ^ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 := by
    conv_lhs => rw [prod_pow_count_normalizedFactors_eq K P h0 hP, map_prod]
    exact Finset.prod_congr rfl fun 𝔭 _ ↦ by rw [map_pow]
  rw [Finset.prod_attach P
    (fun 𝔭 ↦ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^
      (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭), hNprod]
  push_cast
  rw [← Real.finsetProd_rpow P _ (fun 𝔭 _ ↦ by positivity) e]
  refine Finset.prod_congr rfl fun 𝔭 _ ↦ ?_
  rw [← Real.rpow_natCast ((Ideal.absNorm 𝔭 : ℝ)) _,
    ← Real.rpow_natCast (((Ideal.absNorm 𝔭 : ℝ)) ^ e) _,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_comm]

/-- Planning source: ZetaProduct.lean:1154; ideal-count child. -/
theorem sum_rpow_le_euler_prod (K : Type*) [Field K] [NumberField K]
    (P : Finset (Ideal (𝓞 K))) (hPprime : ∀ 𝔭 ∈ P, 𝔭.IsPrime ∧ 𝔭 ≠ ⊥)
    (N : ℕ) (BF : Finset (Ideal (𝓞 K)))
    (hBF : ∀ 𝔟 ∈ BF, 𝔟 ≠ ⊥ ∧
      (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, 𝔭 ∈ P) ∧ Ideal.absNorm 𝔟 ≤ N)
    (e : ℝ) (hxlt : ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ e < 1) :
    ∑ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e
      ≤ ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)⁻¹ := by
  classical
  set Kn := Nat.log 2 N with hKn
  have hx0 : ∀ 𝔭 ∈ P, (0 : ℝ) ≤ ((Ideal.absNorm 𝔭 : ℝ)) ^ e :=
    fun 𝔭 _ ↦ Real.rpow_nonneg (by positivity) e
  set cnt : Ideal (𝓞 K) → ((𝔭 : Ideal (𝓞 K)) → 𝔭 ∈ P → ℕ) :=
    fun 𝔟 𝔭 _ ↦ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 with hcnt
  set F : ((𝔭 : Ideal (𝓞 K)) → 𝔭 ∈ P → ℕ) → ℝ :=
    fun g ↦ ∏ 𝔭 ∈ P.attach, (((Ideal.absNorm 𝔭.1 : ℝ)) ^ e) ^ (g 𝔭.1 𝔭.2) with hF
  have hterm : ∀ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e = F (cnt 𝔟) := by
    intro 𝔟 h𝔟
    obtain ⟨hb0, hbP, _⟩ := hBF 𝔟 h𝔟
    simpa only [hF, hcnt] using absNorm_rpow_eq_prod_attach_count K P hb0 hbP e
  have hmaps : ∀ 𝔟 ∈ BF, cnt 𝔟 ∈ P.pi (fun _ ↦ Finset.range (Kn + 1)) := by
    intro 𝔟 h𝔟
    obtain ⟨hb0, hbP, hbN⟩ := hBF 𝔟 h𝔟
    rw [Finset.mem_pi]; intro 𝔭 h𝔭
    rw [hcnt]; simp only; rw [Finset.mem_range, Nat.lt_succ_iff]
    obtain ⟨h𝔭p, h𝔭0⟩ := hPprime 𝔭 h𝔭
    exact count_normalizedFactors_le_log h𝔭p h𝔭0 hb0 hbN
  have hinj : Set.InjOn cnt BF := by
    intro 𝔞 ha 𝔟 hb hcnteq
    obtain ⟨ha0, haP, _⟩ := hBF 𝔞 ha
    obtain ⟨hb0, hbP, _⟩ := hBF 𝔟 hb
    have hcc : ∀ 𝔭 ∈ P, (UniqueFactorizationMonoid.normalizedFactors 𝔞).count 𝔭
        = (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 :=
      fun 𝔭 h𝔭 ↦ congrFun (congrFun hcnteq 𝔭) h𝔭
    rw [prod_pow_count_normalizedFactors_eq K P ha0 haP,
      prod_pow_count_normalizedFactors_eq K P hb0 hbP]
    exact Finset.prod_congr rfl fun 𝔭 h𝔭 ↦ by rw [hcc 𝔭 h𝔭]
  calc ∑ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e
      = ∑ 𝔟 ∈ BF, F (cnt 𝔟) := Finset.sum_congr rfl hterm
    _ = ∑ g ∈ BF.image cnt, F g := (Finset.sum_image (fun a ha b hb ↦ hinj ha hb)).symm
    _ ≤ ∑ g ∈ P.pi (fun _ ↦ Finset.range (Kn + 1)), F g := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun g _ _ ↦
          Finset.prod_nonneg fun 𝔭 _ ↦ pow_nonneg (hx0 𝔭.1 𝔭.2) _)
        intro g hg
        rw [Finset.mem_image] at hg
        obtain ⟨𝔟, h𝔟, rfl⟩ := hg
        exact hmaps 𝔟 h𝔟
    _ = ∏ 𝔭 ∈ P, ∑ k ∈ Finset.range (Kn + 1), (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k := by
        rw [Finset.prod_sum P (fun _ ↦ Finset.range (Kn + 1))
          (fun 𝔭 k ↦ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k)]
    _ ≤ ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)⁻¹ := by
        refine Finset.prod_le_prod
          (fun 𝔭 h𝔭 ↦ Finset.sum_nonneg fun k _ ↦ pow_nonneg (hx0 𝔭 h𝔭) k) (fun 𝔭 h𝔭 ↦ ?_)
        have h1x : 0 < 1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e := by have := hxlt 𝔭 h𝔭; linarith
        have hkey := geom_sum_mul (((Ideal.absNorm 𝔭 : ℝ)) ^ e) (Kn + 1)
        have hxK : (0 : ℝ) ≤ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ (Kn + 1) := pow_nonneg (hx0 𝔭 h𝔭) _
        have hmul : (∑ k ∈ Finset.range (Kn + 1), (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k)
            * (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)
            = 1 - (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ (Kn + 1) := by nlinarith [hkey]
        have hle : (∑ k ∈ Finset.range (Kn + 1), (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k)
            * (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e) ≤ 1 := by rw [hmul]; linarith
        rw [← le_div_iff₀ h1x] at hle; rwa [one_div] at hle

/-- Planning source: ZetaProduct.lean:1225; ideal-count child. -/
theorem badFinset_subset_of_le (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsGalois K L] (m : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    (finite_isBadPart K L m N).toFinset ⊆ (finite_isBadPart K L m M).toFinset := by
  intro 𝔟 h
  rw [Set.Finite.mem_toFinset] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.trans hNM⟩

/-- Planning source: ZetaProduct.lean:1237; ideal-count child. -/
theorem sum_rpow_badFinset_le (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsGalois K L] (m : ℕ) [NeZero m] (N : ℕ) (e : ℝ)
    (hxlt : ∀ 𝔭 ∈ (finite_badPrimes K m).toFinset, ((Ideal.absNorm 𝔭 : ℝ)) ^ e < 1) :
    ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ)) ^ e
      ≤ ∏ 𝔭 ∈ (finite_badPrimes K m).toFinset, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)⁻¹ := by
  refine sum_rpow_le_euler_prod K (finite_badPrimes K m).toFinset (fun 𝔭 h𝔭 ↦ ?_) N _
    (fun 𝔟 h𝔟 ↦ ?_) e hxlt
  · rw [Set.Finite.mem_toFinset] at h𝔭; exact ⟨h𝔭.1, h𝔭.2.1⟩
  · rw [Set.Finite.mem_toFinset] at h𝔟
    refine ⟨h𝔟.1, fun 𝔭 h𝔭 ↦ ?_, h𝔟.2.2⟩
    have hprime := prime_of_normalized_factor 𝔭 h𝔭
    rw [Set.Finite.mem_toFinset]
    exact ⟨Ideal.isPrime_of_prime hprime, hprime.ne_zero, (h𝔟.2.1 𝔭 h𝔭).2⟩

/-- Planning source: ZetaProduct.lean:1020–1078; realized residues. -/
def IsRealizedNormResidue (K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m]
    (a : (ZMod m)ˣ) : Prop :=
  ∃ b : (Ideal (𝓞 K))⁰, ((Ideal.absNorm (b : Ideal (𝓞 K)) : ZMod m)) = (a : ZMod m)

/-- Planning source: ZetaProduct.lean:1020–1078; realized residues. -/
theorem isRealizedNormResidue_one (K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m] :
    IsRealizedNormResidue K m 1 := by
  exact ⟨1, by
    rw [Submonoid.coe_one, Ideal.one_eq_top, Ideal.absNorm_top, Nat.cast_one, Units.val_one]⟩

/-- Planning source: ZetaProduct.lean:1020–1078; realized residues. -/
theorem isRealizedNormResidue_mul (K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m]
    {a b : (ZMod m)ˣ}
    (ha : IsRealizedNormResidue K m a) (hb : IsRealizedNormResidue K m b) :
    IsRealizedNormResidue K m (a * b) := by
  obtain ⟨𝔟₁, h₁⟩ := ha
  obtain ⟨𝔟₂, h₂⟩ := hb
  exact ⟨𝔟₁ * 𝔟₂, by rw [Submonoid.coe_mul, map_mul, Nat.cast_mul, h₁, h₂, Units.val_mul]⟩

/-- Planning source: ZetaProduct.lean:1020–1078; realized residues. -/
theorem isRealizedNormResidue_inv (K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m]
    {a : (ZMod m)ˣ}
    (ha : IsRealizedNormResidue K m a) : IsRealizedNormResidue K m a⁻¹ := by
  obtain ⟨𝔟, h⟩ := ha
  refine ⟨𝔟 ^ (orderOf a - 1), ?_⟩
  have hpow : ((𝔟 ^ (orderOf a - 1) : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      = (𝔟 : Ideal (𝓞 K)) ^ (orderOf a - 1) := by push_cast; ring
  have hinv : a⁻¹ = a ^ (orderOf a - 1) := inv_eq_of_mul_eq_one_right
    (by rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one])
  rw [hpow, map_pow, Nat.cast_pow, h, hinv, Units.val_pow_eq_pow_val]

/-- Planning source: ZetaProduct.lean:1020–1078; realized residues. -/
def realizedResidues (K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m] :
    Subgroup (ZMod m)ˣ where
  carrier := {a | IsRealizedNormResidue K m a}
  one_mem' := isRealizedNormResidue_one K m
  mul_mem' := isRealizedNormResidue_mul K m
  inv_mem' := isRealizedNormResidue_inv K m

/-- Planning source: ZetaProduct.lean:1020–1078; realized residues. -/
theorem autToPow_range_le_realizedResidues
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) :
    (hζ.autToPow K).range ≤ realizedResidues K m := by
  set R := realizedResidues K m with hR
  set H := Subgroup.comap (hζ.autToPow K) R with hH
  have hHtop : H = ⊤ := by
    refine subgroup_eq_top_of_forall_frobenius_mem_of_coprime K L m H
      (fun 𝔭 h𝔭p h𝔭ne h𝔭unr h𝔭cop ↦ ?_)
    haveI := h𝔭p
    rw [hH, Subgroup.mem_comap, autToPow_frobeniusClass_out K L m hζ 𝔭 h𝔭unr h𝔭cop]
    exact ⟨⟨𝔭, mem_nonZeroDivisors_of_ne_zero h𝔭ne⟩, by rw [ZMod.coe_unitOfCoprime]⟩
  intro a ha
  obtain ⟨g, rfl⟩ := ha
  have : g ∈ H := hHtop ▸ Subgroup.mem_top g
  rwa [hH, Subgroup.mem_comap] at this

/-- Planning source: ZetaProduct.lean:1020–1078; realized residues. -/
theorem realizes_autToPow_range
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) :
    ∀ a ∈ (hζ.autToPow K).range, ∃ 𝔟 : (Ideal (𝓞 K))⁰,
      ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod m)) = (a : ZMod m) :=
  fun _ ha ↦ autToPow_range_le_realizedResidues K L m hζ ha

/-- Planning source: ZetaProduct.lean:1259; ideal-count child. -/
theorem exists_kappa_uniform (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ)
    [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) :
    ∃ κ₀ C₀ : ℝ, ∀ a ∈ (hζ.autToPow K).range, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m)) = (a : ZMod m)} : ℝ)
          - κ₀ * N|
        ≤ C₀ * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) :=
  exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform K m (hζ.autToPow K).range
    (fun χ hχ ↦ tendsto_sum_char_mul_cardNormLeResidue_div_of_realized K m (hζ.autToPow K).range
      (realizes_autToPow_range K L m hζ) χ hχ)

/-- Planning source: ZetaProduct.lean:1275; ideal-count child. -/
theorem abs_sub_kappa_mul_div_le {N Nb : ℕ} {RCb κ₀ C₀ α e₂ : ℝ} (hNb : 0 < Nb)
    (hαnn : 0 ≤ α) (hαe₂ : α = -e₂) (hC₀nn : 0 ≤ C₀)
    (heff : |RCb - κ₀ * ((N / Nb : ℕ) : ℝ)| ≤ C₀ * ((N / Nb : ℕ) : ℝ) ^ α) :
    |RCb - κ₀ * ((N : ℝ) / (Nb : ℝ))| ≤ C₀ * (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ + |κ₀| := by
  have hbposR : (0 : ℝ) < (Nb : ℝ) := by exact_mod_cast hNb
  have hWle : ((N / Nb : ℕ) : ℝ) ≤ (N : ℝ) / (Nb : ℝ) := by
    rw [le_div_iff₀ hbposR]; exact_mod_cast Nat.div_mul_le_self N Nb
  have hWslack : (N : ℝ) / (Nb : ℝ) - ((N / Nb : ℕ) : ℝ) ≤ 1 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hbposR]
    have hlt : N < (N / Nb + 1) * Nb := by
      have hm := Nat.mod_lt N hNb; have hdm := Nat.div_add_mod N Nb
      rw [add_mul, one_mul, mul_comm]; omega
    have : (N : ℝ) < ((N / Nb : ℕ) + 1) * (Nb : ℝ) := by exact_mod_cast hlt
    nlinarith [this]
  have hpow_le : ((N / Nb : ℕ) : ℝ) ^ α ≤ (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ := by
    have heq : (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ = ((N : ℝ) / (Nb : ℝ)) ^ α := by
      rw [Real.div_rpow (Nat.cast_nonneg N) hbposR.le, div_eq_mul_inv]
      congr 1
      rw [hαe₂, Real.rpow_neg hbposR.le, inv_inv]
    rw [heq]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hWle hαnn
  calc |RCb - κ₀ * ((N : ℝ) / (Nb : ℝ))|
      ≤ |RCb - κ₀ * ((N / Nb : ℕ) : ℝ)|
        + |κ₀ * ((N / Nb : ℕ) : ℝ) - κ₀ * ((N : ℝ) / (Nb : ℝ))| := by
        simpa using abs_add_le (RCb - κ₀ * ((N / Nb : ℕ) : ℝ))
          (κ₀ * ((N / Nb : ℕ) : ℝ) - κ₀ * ((N : ℝ) / (Nb : ℝ)))
    _ ≤ C₀ * ((N / Nb : ℕ) : ℝ) ^ α + |κ₀| * 1 := by
        gcongr
        rw [← mul_sub, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_le]
        constructor <;> [linarith [hWle]; linarith [hWslack]]
    _ ≤ C₀ * ((N : ℝ) ^ α * (Nb : ℝ) ^ e₂) + |κ₀| := by rw [mul_one]; gcongr
    _ = C₀ * (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ + |κ₀| := by ring

/-- Planning source: ZetaProduct.lean:1315; ideal-count child. -/
theorem ciSup_sum_inv_absNorm_sub_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] {d : ℕ} {e₂ E₂ : ℝ} (he₂ : e₂ = (d : ℝ)⁻¹ - 1)
    (hE₂nn : 0 ≤ E₂)
    (hEuler : ∀ M : ℕ, ∑ 𝔟 ∈ (finite_isBadPart K L m M).toFinset,
        ((Ideal.absNorm 𝔟 : ℝ)) ^ e₂ ≤ E₂)
    (N : ℕ) (hN1 : 1 ≤ N) :
    (⨆ M : ℕ, ∑ 𝔟 ∈ (finite_isBadPart K L m M).toFinset, ((Ideal.absNorm 𝔟 : ℝ))⁻¹)
        - ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ))⁻¹
      ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) * E₂ := by
  set Tfun : ℕ → ℝ :=
    fun N ↦ ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ))⁻¹ with hTfun
  have hTmono : Monotone Tfun := fun N M hNM ↦
    Finset.sum_le_sum_of_subset_of_nonneg (badFinset_subset_of_le K L m hNM)
      (fun 𝔟 _ _ ↦ by positivity)
  have hNrpow_nn : (0 : ℝ) ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [sub_le_iff_le_add]
  refine ciSup_le fun M ↦ ?_
  rcases le_or_gt N M with hNM | hMN
  · have hsub : (finite_isBadPart K L m N).toFinset ⊆ (finite_isBadPart K L m M).toFinset :=
      badFinset_subset_of_le K L m hNM
    have hdiff : Tfun M - Tfun N
        = ∑ 𝔟 ∈ (finite_isBadPart K L m M).toFinset \ (finite_isBadPart K L m N).toFinset,
            ((Ideal.absNorm 𝔟 : ℝ))⁻¹ := by
      simp only [hTfun]
      rw [sub_eq_iff_eq_add', ← Finset.sum_sdiff hsub, add_comm]
    have hperb : ∑ 𝔟 ∈ (finite_isBadPart K L m M).toFinset \ (finite_isBadPart K L m N).toFinset,
          ((Ideal.absNorm 𝔟 : ℝ))⁻¹
        ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) *
          ∑ 𝔟 ∈ (finite_isBadPart K L m M).toFinset, ((Ideal.absNorm 𝔟 : ℝ)) ^ e₂ := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum (fun 𝔟 h𝔟 ↦ ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun 𝔟 _ _ ↦ mul_nonneg hNrpow_nn (Real.rpow_nonneg (by positivity) _)))
      rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at h𝔟
      obtain ⟨hin, hnotin⟩ := h𝔟
      have hb0 : Ideal.absNorm 𝔟 ≠ 0 := fun h ↦ hin.1 (Ideal.absNorm_eq_zero_iff.mp h)
      have hNb : N < Ideal.absNorm 𝔟 := by
        by_contra h; push Not at h; exact hnotin ⟨hin.1, hin.2.1, h⟩
      have hbposR : (0 : ℝ) < (Ideal.absNorm 𝔟 : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hb0
      have hNbR : (N : ℝ) ≤ (Ideal.absNorm 𝔟 : ℝ) := by exact_mod_cast hNb.le
      have hsplit : (Ideal.absNorm 𝔟 : ℝ)⁻¹
          = (Ideal.absNorm 𝔟 : ℝ) ^ e₂ * (Ideal.absNorm 𝔟 : ℝ) ^ (-(d : ℝ)⁻¹) := by
        rw [← Real.rpow_add hbposR, he₂,
          (by ring : ((d : ℝ)⁻¹ - 1) + (-(d : ℝ)⁻¹) = -1), Real.rpow_neg_one]
      rw [hsplit, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hN1) hNbR (neg_nonpos.mpr (by positivity)))
        (le_of_lt (Real.rpow_pos_of_pos hbposR _))
    have : Tfun M - Tfun N ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) * E₂ :=
      hdiff ▸ le_trans hperb (mul_le_mul_of_nonneg_left (hEuler M) hNrpow_nn)
    linarith
  · have : Tfun M ≤ Tfun N := hTmono hMN.le
    nlinarith [mul_nonneg hNrpow_nn hE₂nn]

/-- Planning source: ZetaProduct.lean:1375; ideal-count child. -/
theorem card_finite_isBadPart_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] {α e₂ E₂ : ℝ} (hαnn : 0 ≤ α) (hαe₂ : α = -e₂)
    (N : ℕ) (hNα_nn : 0 ≤ (N : ℝ) ^ α)
    (hsumE₂ : ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ)) ^ e₂ ≤ E₂) :
    (((finite_isBadPart K L m N).toFinset.card : ℕ) : ℝ) ≤ (N : ℝ) ^ α * E₂ := by
  calc (((finite_isBadPart K L m N).toFinset.card : ℕ) : ℝ)
      = ∑ _𝔟 ∈ (finite_isBadPart K L m N).toFinset, (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, (N : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ := by
        refine Finset.sum_le_sum fun 𝔟 h𝔟 ↦ ?_
        rw [Set.Finite.mem_toFinset] at h𝔟
        have hbpos : 0 < Ideal.absNorm 𝔟 :=
          Nat.pos_of_ne_zero fun h ↦ h𝔟.1 (Ideal.absNorm_eq_zero_iff.mp h)
        have hbposR : (0 : ℝ) < (Ideal.absNorm 𝔟 : ℝ) := by exact_mod_cast hbpos
        have hbNR : (Ideal.absNorm 𝔟 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h𝔟.2.2
        have h1eq : (1 : ℝ) = (Ideal.absNorm 𝔟 : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ := by
          rw [← Real.rpow_add hbposR, hαe₂, neg_add_cancel, Real.rpow_zero]
        rw [h1eq]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hbposR.le hbNR hαnn)
          (Real.rpow_pos_of_pos hbposR _).le
    _ = (N : ℝ) ^ α * ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          (Ideal.absNorm 𝔟 : ℝ) ^ e₂ := by rw [Finset.mul_sum]
    _ ≤ (N : ℝ) ^ α * E₂ := mul_le_mul_of_nonneg_left hsumE₂ hNα_nn

/-- Planning source: ZetaProduct.lean:1417; ideal-count child. -/
theorem card_fibre_bound_two_le (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ m)
    (hd : 2 ≤ Module.finrank ℚ K) :
    ∃ κ C' : ℝ, ∀ g : Gal(L/K), ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g} : ℝ)
          - κ * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  set d : ℕ := Module.finrank ℚ K
  set α : ℝ := 1 - (d : ℝ)⁻¹ with hα
  set e₂ : ℝ := (d : ℝ)⁻¹ - 1 with he₂
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have he₂neg : e₂ < 0 := by
    have hle : (d : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by gcongr
    rw [he₂]; linarith [hle, (by norm_num : (2 : ℝ)⁻¹ < 1)]
  have hαnn : 0 ≤ α := by rw [hα]; linarith [he₂neg, he₂]
  have hαe₂ : α = -e₂ := by rw [hα, he₂]; ring
  set P : Finset (Ideal (𝓞 K)) := (finite_badPrimes K m).toFinset with hP
  have hN𝔭2 : ∀ 𝔭 ∈ P, (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) := by
    intro 𝔭 h𝔭
    rw [hP, Set.Finite.mem_toFinset] at h𝔭
    have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ h𝔭.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ h𝔭.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast (show 2 ≤ Ideal.absNorm 𝔭 by omega)
  have hxlt : ∀ e : ℝ, e < 0 → ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ e < 1 := by
    intro e he 𝔭 h𝔭
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith [hN𝔭2 𝔭 h𝔭]) he
  have hxlt1 : ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ (-1 : ℝ) < 1 := hxlt _ (by norm_num)
  have hxlt2 : ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ e₂ < 1 := hxlt _ he₂neg
  set E₁ : ℝ := ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ (-1 : ℝ))⁻¹
  set E₂ : ℝ := ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e₂)⁻¹ with hE₂
  obtain ⟨κ₀, C₀, hunif⟩ := exists_kappa_uniform K L m hζ
  set Tfun : ℕ → ℝ :=
    fun N ↦ ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ))⁻¹ with hTfun
  have hTfun_eq : ∀ N, Tfun N
      = ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ)) ^ (-1 : ℝ) := by
    intro N
    rw [hTfun]; refine Finset.sum_congr rfl fun 𝔟 _ ↦ ?_
    rw [Real.rpow_neg_one]
  have hTbdd : ∀ N, Tfun N ≤ E₁ := fun N ↦ by
    rw [hTfun_eq N]; exact sum_rpow_badFinset_le K L m N (-1) hxlt1
  have hTmono : Monotone Tfun := by
    intro N M hNM
    exact Finset.sum_le_sum_of_subset_of_nonneg (badFinset_subset_of_le K L m hNM)
      (fun 𝔟 _ _ ↦ by positivity)
  set T : ℝ := ⨆ N, Tfun N
  have hTbddAbove : BddAbove (Set.range Tfun) := ⟨E₁, fun y ⟨N, hN⟩ ↦ hN ▸ hTbdd N⟩
  have hTfun_le_T : ∀ N, Tfun N ≤ T := fun N ↦ le_ciSup hTbddAbove N
  have hE₂nn : 0 ≤ E₂ := by
    rw [hE₂]; refine Finset.prod_nonneg fun 𝔭 h𝔭 ↦ ?_
    have := hxlt2 𝔭 h𝔭; positivity
  have htail : ∀ N : ℕ, 1 ≤ N → T - Tfun N ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) * E₂ := fun N hN1 ↦
    ciSup_sum_inv_absNorm_sub_le K L m he₂ hE₂nn
      (fun M ↦ sum_rpow_badFinset_le K L m M e₂ hxlt2) N hN1
  refine ⟨κ₀ * T, (C₀ + 2 * |κ₀|) * E₂, fun g N hN1 ↦ ?_⟩
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNα_nn : (0 : ℝ) ≤ (N : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [card_L2_eq_sum_residue K L m hζ g N, Nat.cast_sum]
  set a : Ideal (𝓞 K) → (ZMod m)ˣ :=
    fun 𝔟 ↦ hζ.autToPow K (g * (frobeniusIdeal K L 𝔟)⁻¹)
  set RC : Ideal (𝓞 K) → ℝ := fun 𝔟 ↦
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N / Ideal.absNorm 𝔟 ∧
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m)) = ((a 𝔟 : (ZMod m)ˣ) : ZMod m)} : ℝ)
  change |(∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, RC 𝔟) - κ₀ * T * (N : ℝ)| ≤ _
  have hamem : ∀ 𝔟, a 𝔟 ∈ (hζ.autToPow K).range := fun 𝔟 ↦ ⟨_, rfl⟩
  have hC₀nn : 0 ≤ C₀ := by
    have h := hunif 1 (one_mem _) 1 (le_refl 1)
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hbadmem : ∀ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
      𝔟 ≠ ⊥ ∧ Ideal.absNorm 𝔟 ≤ N := fun 𝔟 h𝔟 ↦ by
    rw [Set.Finite.mem_toFinset] at h𝔟; exact ⟨h𝔟.1, h𝔟.2.2⟩
  have hperbad : ∀ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
      |RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ))|
        ≤ C₀ * (N : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ + |κ₀| := by
    intro 𝔟 h𝔟
    obtain ⟨hb0, hbN⟩ := hbadmem 𝔟 h𝔟
    have hbpos : 0 < Ideal.absNorm 𝔟 :=
      Nat.pos_of_ne_zero fun h ↦ hb0 (Ideal.absNorm_eq_zero_iff.mp h)
    exact abs_sub_kappa_mul_div_le hbpos hαnn hαe₂ hC₀nn
      (hunif (a 𝔟) (hamem 𝔟) _ ((Nat.one_le_div_iff hbpos).mpr hbN))
  have hsum_div : ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, (N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)
      = (N : ℝ) * Tfun N := by
    rw [hTfun, Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝔟 _ ↦ ?_
    rw [div_eq_mul_inv]
  have hsumE₂ : ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, ((Ideal.absNorm 𝔟 : ℝ)) ^ e₂ ≤ E₂ :=
    sum_rpow_badFinset_le K L m N e₂ hxlt2
  have hcard_le : (((finite_isBadPart K L m N).toFinset.card : ℕ) : ℝ) ≤ (N : ℝ) ^ α * E₂ :=
    card_finite_isBadPart_le K L m hαnn hαe₂ N hNα_nn hsumE₂
  have hA : |∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
        (RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)))|
      ≤ (C₀ + |κ₀|) * ((N : ℝ) ^ α * E₂) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          |RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ))|
        ≤ ∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
            (C₀ * (N : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ + |κ₀|) :=
          Finset.sum_le_sum hperbad
      _ = C₀ * (N : ℝ) ^ α * (∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
            (Ideal.absNorm 𝔟 : ℝ) ^ e₂)
          + |κ₀| * (((finite_isBadPart K L m N).toFinset.card : ℕ) : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ C₀ * (N : ℝ) ^ α * E₂ + |κ₀| * ((N : ℝ) ^ α * E₂) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hsumE₂ (mul_nonneg hC₀nn hNα_nn))
            (mul_le_mul_of_nonneg_left hcard_le (abs_nonneg _))
      _ = (C₀ + |κ₀|) * ((N : ℝ) ^ α * E₂) := by ring
  have hB : |κ₀ * ((∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
        (N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)) - T * (N : ℝ))|
      ≤ |κ₀| * ((N : ℝ) ^ α * E₂) := by
    rw [hsum_div, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hTrw : (N : ℝ) * Tfun N - T * (N : ℝ) = -((N : ℝ) * (T - Tfun N)) := by ring
    rw [hTrw, abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N)
      (sub_nonneg.mpr (hTfun_le_T N)))]
    refine le_trans (mul_le_mul_of_nonneg_left (htail N hN1) (Nat.cast_nonneg N)) ?_
    rw [← mul_assoc, hα]
    have hNmul : (N : ℝ) * (N : ℝ) ^ (-(d : ℝ)⁻¹) = (N : ℝ) ^ (1 - (d : ℝ)⁻¹) := by
      nth_rewrite 1 [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hNposR, sub_eq_add_neg]
    rw [hNmul]
  have hdecomp : (∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset, RC 𝔟) - κ₀ * T * (N : ℝ)
      = (∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          (RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ))))
        + κ₀ * ((∑ 𝔟 ∈ (finite_isBadPart K L m N).toFinset,
          (N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)) - T * (N : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
  rw [hdecomp]
  refine le_trans (abs_add_le _ _) ?_
  have hgoal : (C₀ + 2 * |κ₀|) * E₂ * (N : ℝ) ^ α
      = (C₀ + |κ₀|) * ((N : ℝ) ^ α * E₂) + |κ₀| * ((N : ℝ) ^ α * E₂) := by ring
  rw [hgoal]
  exact add_le_add hA hB

open Polynomial in
/-- Planning source: ZetaProduct.lean:1568; ideal-count child. -/
theorem associated_natCast_sub_one_pow {A : Type*} [CommRing A] [IsDomain A] {p k : ℕ}
    [hp : Fact p.Prime] {ζ' : A} (hζ' : IsPrimitiveRoot ζ' (p ^ (k + 1))) :
    Associated (p : A) ((ζ' - 1) ^ (p ^ k * (p - 1))) := by
  have hcard : (primitiveRoots (p ^ (k + 1)) A).card = p ^ k * (p - 1) := by
    rw [hζ'.card_primitiveRoots, Nat.totient_prime_pow_succ hp.out]
  have heval : (p : A) = ∏ μ ∈ primitiveRoots (p ^ (k + 1)) A, (1 - μ) := by
    have h1 := eval_one_cyclotomic_prime_pow (R := A) k (p := p)
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ'] at h1
    simp only [eval_prod, eval_sub, eval_X, eval_C] at h1
    rw [← h1]
  rw [heval]
  have hpos : 0 < p ^ (k + 1) := pow_pos hp.out.pos _
  have hassoc : ∀ μ ∈ primitiveRoots (p ^ (k + 1)) A, Associated (1 - μ) (ζ' - 1) := by
    intro μ hμ
    have hμp : IsPrimitiveRoot μ (p ^ (k + 1)) := isPrimitiveRoot_of_mem_primitiveRoots hμ
    obtain ⟨j, _, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hμp.pow_eq_one
    have hjc : j.Coprime (p ^ (k + 1)) := (hζ'.pow_iff_coprime hpos j).mp hμp
    rw [show (1 : A) - ζ' ^ j = -(ζ' ^ j - 1) by ring]
    exact (hζ'.associated_sub_one_pow_sub_one_of_coprime hjc).neg_right.symm
  calc Associated (∏ μ ∈ primitiveRoots (p ^ (k + 1)) A, (1 - μ))
        (∏ _μ ∈ primitiveRoots (p ^ (k + 1)) A, (ζ' - 1)) := Associated.prod _ _ _ hassoc
    _ = (ζ' - 1) ^ (p ^ k * (p - 1)) := by rw [Finset.prod_const, hcard]

/-- Planning source: ZetaProduct.lean:1592; ideal-count child. -/
theorem two_le_pow_mul_pred {p k : ℕ} (hp : p.Prime) (hbad : ¬ (p = 2 ∧ k = 0)) :
    2 ≤ p ^ k * (p - 1) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h ↦ hbad ⟨rfl, h⟩
    calc 2 = 2 ^ 1 * (2 - 1) := by norm_num
      _ ≤ 2 ^ k * (2 - 1) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hk)
  · have hp3 : 3 ≤ p := hp.two_le.lt_of_ne (Ne.symm hp2)
    calc 2 ≤ 1 * (p - 1) := by omega
      _ ≤ p ^ k * (p - 1) := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ hp.pos)

/-- Planning source: ZetaProduct.lean:1604; ideal-count child. -/
theorem factorization_two_ne_one_of_mod_four {m : ℕ} (hm0 : m ≠ 0) (hm : m % 4 ≠ 2) :
    m.factorization 2 ≠ 1 := by
  intro hf
  have h2dvd : 2 ∣ m := by
    have h : (2 : ℕ) ^ 1 ∣ m :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm0).mpr (by omega)
    simpa using h
  have h4ndvd : ¬ 4 ∣ m := fun h4 ↦
    absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm0).mp
      (by rwa [show (4 : ℕ) = 2 ^ 2 by norm_num] at h4)) (by omega)
  exact hm (by omega)

/-- Planning source: ZetaProduct.lean:1618; ideal-count child. -/
theorem span_singleton_natCast_eq_of_finrank_eq_one (K : Type*) [Field K] [NumberField K]
    (hd1 : Module.finrank ℚ K = 1) (p : ℕ) (hp : p.Prime) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hmem : (p : 𝓞 K) ∈ 𝔭) : Ideal.span {(p : 𝓞 K)} = 𝔭 := by
  have hrank : Module.finrank ℤ (𝓞 K) = 1 := by rw [NumberField.RingOfIntegers.rank, hd1]
  have hNspan : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p := by
    rw [Ideal.absNorm_span_singleton,
      show ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by push_cast; rfl,
      Algebra.norm_algebraMap, hrank, Int.natAbs_pow, Int.natAbs_natCast, pow_one]
  have hle : Ideal.span {(p : 𝓞 K)} ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).mpr hmem
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hNmul : Ideal.absNorm 𝔭 * Ideal.absNorm C = p := by rw [← map_mul, ← hC, hNspan]
  have hN𝔭1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ ‹𝔭.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hN𝔭eq : Ideal.absNorm 𝔭 = p :=
    (Nat.Prime.eq_one_or_self_of_dvd hp _ ⟨_, hNmul.symm⟩).resolve_left hN𝔭1
  have hNC1 : Ideal.absNorm C = 1 := by
    rw [hN𝔭eq] at hNmul
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by rwa [mul_one])
  rw [hC, Ideal.absNorm_eq_one_iff.mp hNC1, Ideal.mul_top]

/-- Planning source: ZetaProduct.lean:1653; ideal-count child. -/
theorem coprime_absNorm_of_unramified_of_finrank_eq_one (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L]
    (hd1 : Module.finrank ℚ K = 1) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥)
    (hunr : UnramifiedIn K L 𝔭) (hm : m % 4 ≠ 2) : (Ideal.absNorm 𝔭).Coprime m := by
  classical
  by_contra hncop
  obtain ⟨p, hpm, hpmem𝔭⟩ := exists_primeFactor_natCast_mem_of_not_coprime K m 𝔭 h𝔭 hncop
  have hp : p.Prime := (Nat.mem_primeFactors.mp hpm).1
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hpm
  have hm0 : m ≠ 0 := (Nat.mem_primeFactors.mp hpm).2.2
  set v := m.factorization p with hv
  have hv1 : 1 ≤ v := by rw [hv]; exact hp.factorization_pos_of_dvd hm0 hpdvd
  obtain ⟨k, hk⟩ : ∃ k, v = k + 1 := ⟨v - 1, by omega⟩
  have hbad : ¬ (p = 2 ∧ k = 0) := by
    rintro ⟨rfl, rfl⟩
    exact factorization_two_ne_one_of_mod_four hm0 hm (by rw [← hv, hk])
  have hpvdvd : p ^ v ∣ m := by rw [hv]; exact Nat.ordProj_dvd m p
  obtain ⟨ζm, hζm⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot K L (Set.mem_singleton m) (NeZero.ne m)
  set q := m / p ^ v with hq
  have hqdvd : q ∣ m := Nat.div_dvd_of_dvd hpvdvd
  have hq0 : q ≠ 0 := Nat.div_ne_zero_iff.mpr
    ⟨pow_ne_zero _ hp.ne_zero, Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hpvdvd⟩
  set ζ' : 𝓞 L := hζm.toInteger ^ q
  have hmq : m / q = p ^ (k + 1) := by rw [hq, Nat.div_div_self hpvdvd hm0, ← hk]
  have hζ' : IsPrimitiveRoot ζ' (p ^ (k + 1)) := by
    have h := hζm.toInteger_isPrimitiveRoot.pow_of_dvd hq0 hqdvd
    rwa [hmq] at h
  have hassoc : Associated (p : 𝓞 L) ((ζ' - 1) ^ (p ^ k * (p - 1))) :=
    associated_natCast_sub_one_pow hζ'
  have hφ2 : 2 ≤ p ^ k * (p - 1) := two_le_pow_mul_pred hp hbad
  have hspan𝔭 : Ideal.span {(p : 𝓞 K)} = 𝔭 :=
    span_singleton_natCast_eq_of_finrank_eq_one K hd1 p hp 𝔭 hpmem𝔭
  haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal h𝔭
  obtain ⟨𝔓, h𝔓max, h𝔓lo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 K) (S := 𝓞 L) 𝔭
  haveI : 𝔓.IsPrime := h𝔓max.isPrime
  haveI := h𝔓lo
  have hnotdvd : ¬ 𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    rw [not_dvd_differentIdeal_iff (A := 𝓞 K) (B := 𝓞 L)]
    exact hunr.2 𝔓 h𝔓max h𝔓lo
  apply hnotdvd
  have hdvd2 : 𝔓 ^ 2 ∣ 𝔭.map (algebraMap (𝓞 K) (𝓞 L)) := by
    have hmapeq : 𝔭.map (algebraMap (𝓞 K) (𝓞 L)) = Ideal.span {(p : 𝓞 L)} := by
      rw [← hspan𝔭, Ideal.map_span, Set.image_singleton, map_natCast]
    have hspanL : Ideal.span {(p : 𝓞 L)} = (Ideal.span {ζ' - 1}) ^ (p ^ k * (p - 1)) := by
      rw [Ideal.span_singleton_pow]
      exact Ideal.span_singleton_eq_span_singleton.mpr hassoc
    have hpmem𝔓 : (p : 𝓞 L) ∈ 𝔓 := by
      have h1 : algebraMap (𝓞 K) (𝓞 L) (p : 𝓞 K) ∈ 𝔓 := by
        rw [h𝔓lo.over] at hpmem𝔭; exact hpmem𝔭
      rwa [map_natCast] at h1
    have hsub𝔓 : ζ' - 1 ∈ 𝔓 := by
      have hpow : (ζ' - 1) ^ (p ^ k * (p - 1)) ∈ 𝔓 := by
        obtain ⟨u, hu⟩ := hassoc
        rw [← hu]; exact Ideal.mul_mem_right _ _ hpmem𝔓
      exact ‹𝔓.IsPrime›.mem_of_pow_mem _ hpow
    have hdvd1 : 𝔓 ∣ Ideal.span {ζ' - 1} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hsub𝔓)
    rw [hmapeq, hspanL]
    exact dvd_trans (pow_dvd_pow 𝔓 hφ2) (pow_dvd_pow_of_dvd hdvd1 _)
  simpa using pow_sub_one_dvd_differentIdeal (𝓞 K) 𝔓 2 h𝔭 hdvd2

/-- Planning source: ZetaProduct.lean:1721; ideal-count child. -/
theorem card_fibre_bound_eq_one (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ m)
    (hd1 : Module.finrank ℚ K = 1) (hm : m % 4 ≠ 2) :
    ∃ κ C' : ℝ, ∀ g : Gal(L/K), ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g} : ℝ)
          - κ * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨κ₀, C₀, hunif⟩ := exists_kappa_uniform K L m hζ
  refine ⟨κ₀, C₀, fun g N hN1 ↦ ?_⟩
  have hbadtop : (finite_isBadPart K L m N).toFinset = {⊤} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun 𝔟 h𝔟 ↦ ?_⟩
    · rw [Set.Finite.mem_toFinset]
      refine ⟨by rw [Ne, ← Ideal.one_eq_top]; exact one_ne_zero, fun 𝔭 h𝔭 ↦ ?_, ?_⟩
      · rw [← Ideal.one_eq_top, normalizedFactors_one] at h𝔭
        exact absurd h𝔭 (Multiset.notMem_zero _)
      · rw [Ideal.absNorm_top]; exact hN1
    · rw [Set.Finite.mem_toFinset] at h𝔟
      obtain ⟨h0, hfac, _⟩ := h𝔟
      by_contra htop
      have hfac0 : normalizedFactors 𝔟 ≠ 0 := by
        intro h
        have : 𝔟 = 1 := by
          have hp := Ideal.prod_normalizedFactors_eq_self h0
          rw [h, Multiset.prod_zero] at hp; exact hp.symm
        rw [Ideal.one_eq_top] at this; exact htop this
      obtain ⟨𝔭, h𝔭⟩ := Multiset.exists_mem_of_ne_zero hfac0
      have hprime := prime_of_normalized_factor 𝔭 h𝔭
      haveI : 𝔭.IsPrime := Ideal.isPrime_of_prime hprime
      exact (hfac 𝔭 h𝔭).2 (coprime_absNorm_of_unramified_of_finrank_eq_one K L m hd1 𝔭
        hprime.ne_zero (hfac 𝔭 h𝔭).1 hm)
  rw [card_L2_eq_sum_residue K L m hζ g N, hbadtop, Finset.sum_singleton,
    frobeniusIdeal_one, inv_one, mul_one, Ideal.absNorm_top, Nat.div_one]
  exact hunif (hζ.autToPow K g) ⟨g, rfl⟩ N hN1

end Cox.Chebotarev
