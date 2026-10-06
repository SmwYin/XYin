/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevArtin
import XYin.PhD.Cox.Theorem11_1.ChebotarevCharacters
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Source-local cyclotomic analytic prerequisites

Source: AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87`; not an imported dependency.
-/
noncomputable section
open Filter NumberField Topology Set
namespace Cox.Chebotarev
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

open scoped Classical in
/-- Planning source: Cyclotomic.lean:166; planning contract. -/
theorem sum_galoisCharacter_eq_card_or_zero
    (G : Type*) [Group G] [IsMulCommutative G] [Finite G] [Fintype (G →* ℂˣ)] (g : G) :
    (∑ χ : G →* ℂˣ, (χ g : ℂ)) = if g = 1 then (Nat.card G : ℂ) else 0 := by
  let : CommGroup G := { mul_comm := mul_comm' }
  have : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent G) := inferInstance
  split_ifs with hg
  · subst hg
    simpa only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card]
      using congrArg Nat.cast (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ)
  · exact sum_char_apply_eq_zero_of_ne_one hg

open scoped Classical in
/-- Planning source: Cyclotomic.lean:180; planning contract. -/
theorem sum_galoisCharacter_mul_inv_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] [Fintype (galoisCharacter K L)] (σ τ : Gal(L/K)) :
    (∑ χ : galoisCharacter K L, (χ σ : ℂ) * ((χ τ : ℂ))⁻¹)
      = if σ * τ⁻¹ = 1 then (Nat.card Gal(L/K) : ℂ) else 0 := by
  rw [← sum_galoisCharacter_eq_card_or_zero Gal(L/K) (σ * τ⁻¹)]
  exact Finset.sum_congr rfl fun χ _ ↦ by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]

/-- Planning source: Cyclotomic.lean:192; planning contract. -/
theorem character_orthogonality_cyclotomic_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    [Fintype (galoisCharacter K L)] (σ : Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (_hunr : UnramifiedIn K L 𝔭) (_h : frobeniusClass K L 𝔭 = ConjClasses.mk σ) :
    (∑ χ : galoisCharacter K L,
        (χ σ : ℂ) * ((χ (frobeniusClass K L 𝔭).out : ℂ))⁻¹)
      = (Nat.card Gal(L/K) : ℂ) := by
  have : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
  set τ := (frobeniusClass K L 𝔭).out
  have hmk : ConjClasses.mk τ = frobeniusClass K L 𝔭 := Quotient.out_eq _
  have heq : σ * τ⁻¹ = 1 := by
    obtain ⟨c, hc⟩ : IsConj τ σ :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hmk.trans _h)
    rw [SemiconjBy, mul_comm' (c : Gal(L/K))] at hc
    rw [mul_right_cancel hc, mul_inv_cancel]
  rw [sum_galoisCharacter_mul_inv_eq K L σ τ, if_pos heq]

/-- Planning source: Cyclotomic.lean:657; planning contract. -/
theorem sum_charTwist_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    [Fintype (galoisCharacter K L)] (σ : Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : UnramifiedIn K L 𝔭) (h : frobeniusClass K L 𝔭 = ConjClasses.mk σ) :
    (∑ χ : galoisCharacter K L,
        ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭).out : ℂ)) = (Nat.card Gal(L/K) : ℂ) := by
  rw [← character_orthogonality_cyclotomic_eq K L m σ 𝔭 hunr h,
    ← Equiv.sum_comp (Equiv.inv (galoisCharacter K L))
      fun χ : galoisCharacter K L ↦ (χ σ : ℂ) * ((χ (frobeniusClass K L 𝔭).out : ℂ))⁻¹]
  refine Finset.sum_congr rfl fun χ _ ↦ ?_
  rw [Equiv.inv_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, inv_inv, mul_comm]

/-- Planning source: Cyclotomic.lean:213; planning contract. -/
theorem character_orthogonality_cyclotomic_ne
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    [Fintype (galoisCharacter K L)] (σ : Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (_hunr : UnramifiedIn K L 𝔭) (_h : frobeniusClass K L 𝔭 ≠ ConjClasses.mk σ) :
    (∑ χ : galoisCharacter K L,
        (χ σ : ℂ) * ((χ (frobeniusClass K L 𝔭).out : ℂ))⁻¹) = 0 := by
  have : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
  set τ := (frobeniusClass K L 𝔭).out
  have hmk : ConjClasses.mk τ = frobeniusClass K L 𝔭 := Quotient.out_eq _
  have hne : σ * τ⁻¹ ≠ 1 := fun hσ ↦
    _h <| hmk.symm.trans (congrArg ConjClasses.mk (mul_inv_eq_one.mp hσ)).symm
  rw [sum_galoisCharacter_mul_inv_eq K L σ τ, if_neg hne]

/-- Planning source: Cyclotomic.lean:673; planning contract. -/
theorem sum_charTwist_ne
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    [Fintype (galoisCharacter K L)] (σ : Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : UnramifiedIn K L 𝔭) (h : frobeniusClass K L 𝔭 ≠ ConjClasses.mk σ) :
    (∑ χ : galoisCharacter K L,
        ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭).out : ℂ)) = 0 := by
  rw [← character_orthogonality_cyclotomic_ne K L m σ 𝔭 hunr h,
    ← Equiv.sum_comp (Equiv.inv (galoisCharacter K L))
      fun χ : galoisCharacter K L ↦ (χ σ : ℂ) * ((χ (frobeniusClass K L 𝔭).out : ℂ))⁻¹]
  refine Finset.sum_congr rfl fun χ _ ↦ ?_
  rw [Equiv.inv_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, inv_inv, mul_comm]

/-- The unramified-prime subtype embeds in the `primeIdealZetaSum` index subtype
(AINTLIB Cyclotomic.lean:58). -/
theorem unramifiedPrime_toPrimeNeBot_injective
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Function.Injective (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2⟩, 𝔭.2.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩ :
        {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})) :=
  fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)

/-- Planning source: Cyclotomic.lean:411; planning contract. -/
theorem summable_twistedPrimeSum
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))) := by
  have hs0 : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
    ((summable_prime_absNorm_rpow K _ hs).comp_injective
      (unramifiedPrime_toPrimeNeBot_injective K L)).congr fun 𝔭 ↦ rfl
  have hnorm1 : ∀ c : ConjClasses Gal(L/K), ‖(χ c.out : ℂ)‖ = 1 := fun c ↦
    (((Units.coeHom ℂ).comp χ).isOfFinOrder (isOfFinOrder_of_finite c.out)).norm_eq_one
  have hnormterm : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      ‖(χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ =
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun 𝔭 ↦ by
    have hpos : 0 < Ideal.absNorm 𝔭.1 := by
      have hne : Ideal.absNorm 𝔭.1 ≠ 0 := fun h ↦
        UnramifiedIn.ne_bot K L 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
      omega
    rw [norm_mul, hnorm1, one_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re,
      Complex.ofReal_re]
  exact Summable.of_norm (hs0.congr fun 𝔭 ↦ (hnormterm 𝔭).symm)

/-- Planning source: Cyclotomic.lean:403; planning contract. -/
def twistedPrimeSum (χ : galoisCharacter K L) (s : ℝ) : ℂ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
    (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))

/-- Planning source: Cyclotomic.lean:765; planning contract. -/
theorem sum_charTwist_mul_twistedPrimeSum_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    [Fintype (galoisCharacter K L)] (σ : Gal(L/K)) {s : ℝ} (hs : 1 < s) :
    (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s)
      = (Nat.card Gal(L/K) : ℂ) *
        (primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ} s : ℂ) := by
  classical
  have hfreal : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) = ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) : ℝ) := fun 𝔭 ↦ by
    rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast]
  have hinterchange : (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s)
      = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭.1).out : ℂ))
            * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) := by
    have hstep : ∀ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s
        = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
            ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭.1).out : ℂ)
              * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) := fun χ ↦ by
      rw [twistedPrimeSum, ← tsum_mul_left]
      exact tsum_congr fun 𝔭 ↦ by ring
    rw [Finset.sum_congr rfl fun χ _ ↦ hstep χ,
      ← Summable.tsum_finsetSum (fun χ _ ↦
        ((summable_twistedPrimeSum K L χ hs).mul_left ((χ σ : ℂ))⁻¹).congr fun 𝔭 ↦ by ring)]
    exact tsum_congr fun 𝔭 ↦ (Finset.sum_mul _ _ _).symm
  have hcollapse : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭.1).out : ℂ))
          * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))
        = if frobeniusClass K L 𝔭.1 = ConjClasses.mk σ then
            (Nat.card Gal(L/K) : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) else 0 := fun 𝔭 ↦ by
    have := 𝔭.2.1
    by_cases h : frobeniusClass K L 𝔭.1 = ConjClasses.mk σ
    · rw [sum_charTwist_eq K L m σ 𝔭.1 𝔭.2.2 h, if_pos h]
    · rw [sum_charTwist_ne K L m σ 𝔭.1 𝔭.2.2 h, if_neg h, zero_mul]
  have hfinj : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ} ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
        (⟨𝔭.1, 𝔭.2.1.1, 𝔭.2.1.2.1⟩ : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭})) :=
    fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)
  have hfibre : primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ} s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
        (if frobeniusClass K L 𝔭.1 = ConjClasses.mk σ then (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) else 0) :=
    by
    rw [primeIdealZetaSum_def, ← hfinj.tsum_eq
      (f := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
        if frobeniusClass K L 𝔭.1 = ConjClasses.mk σ then (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) else 0)
      ?_]
    · exact tsum_congr fun 𝔭 ↦ (if_pos 𝔭.2.1.2.2).symm
    · rintro 𝔭 h𝔭
      have h : frobeniusClass K L 𝔭.1 = ConjClasses.mk σ := by
        by_contra hne
        exact h𝔭 (if_neg hne)
      exact ⟨⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2, h⟩, 𝔭.2.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩, rfl⟩
  rw [hinterchange, tsum_congr hcollapse, hfibre, Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun 𝔭 ↦ ?_
  rw [apply_ite (Complex.ofReal), mul_ite, Complex.ofReal_zero, mul_zero, hfreal 𝔭]

/-- Planning source: Cyclotomic.lean:736; planning contract. -/
theorem twistedPrimeSum_one_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (s : ℝ) :
    twistedPrimeSum K L 1 s
      = (primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s : ℂ) := by
  have hinj : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ∧
          𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
        (⟨𝔭.1, 𝔭.2.1.1, 𝔭.2.1.2⟩ : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭})) :=
    fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)
  have hsurj : Function.Surjective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ∧
          𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
        (⟨𝔭.1, 𝔭.2.1.1, 𝔭.2.1.2⟩ : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭})) :=
    fun 𝔭 ↦ ⟨⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2⟩, 𝔭.2.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩, rfl⟩
  rw [twistedPrimeSum, primeIdealZetaSum_def, Complex.ofReal_tsum,
    ← hinj.tsum_eq (f := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      ((1 : galoisCharacter K L) (frobeniusClass K L 𝔭.1).out : ℂ)
        * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))
      (by rw [hsurj.range_eq]; exact Set.subset_univ _)]
  refine tsum_congr fun 𝔭 ↦ ?_
  rw [show ((1 : galoisCharacter K L) (frobeniusClass K L 𝔭.1).out : ℂ) = 1 by simp, one_mul,
    show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast]

/-- Planning source: Cyclotomic.lean:828; planning contract. -/
theorem card_mul_frobeniusFibre_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    [Fintype (galoisCharacter K L)] [DecidableEq (galoisCharacter K L)] (σ : Gal(L/K))
    {s : ℝ} (hs : 1 < s) :
    (Nat.card Gal(L/K) : ℝ) *
        primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
      = primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s
        + (∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
            ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s).re := by
  classical
  set U : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}
  have hMb : (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s)
      = (primeIdealZetaSum U s : ℂ)
        + ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
            ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : galoisCharacter K L)),
      show ((1 : galoisCharacter K L) σ : ℂ) = 1 by simp, inv_one, one_mul, twistedPrimeSum_one_eq]
  have heq := (sum_charTwist_mul_twistedPrimeSum_eq K L m σ hs).symm.trans hMb
  have := congrArg Complex.re heq
  simpa [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im] using this

/-- Planning source: Cyclotomic.lean:434; planning contract. -/
theorem two_le_absNorm_prime
    (K : Type*) [Field K] [NumberField K] (𝔭 : Ideal (𝓞 K)) (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) :
    2 ≤ Ideal.absNorm 𝔭 := by
  have hne0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ hne (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ hp.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

/-- Planning source: Cyclotomic.lean:344; planning contract. -/
theorem cexp_logSum_eq_tprod
    {ι : Type*} (w : ι → ℂ) (hsumw : Summable w) (hslit : ∀ i, (1 - w i) ∈ Complex.slitPlane) :
    Complex.exp (∑' i, -Complex.log (1 - w i)) = ∏' i, (1 - w i)⁻¹ := by
  set f : ι → ℂ := fun i ↦ (1 - w i)⁻¹ with hf
  have hfn : ∀ i, f i ≠ 0 := fun i ↦ inv_ne_zero (Complex.slitPlane_ne_zero (hslit i))
  have hlogf : ∀ i, Complex.log (f i) = -Complex.log (1 - w i) := fun i ↦ by
    rw [hf, Complex.log_inv _ (Complex.slitPlane_arg_ne_pi (hslit i))]
  have hsumlog : Summable (fun i ↦ Complex.log (f i)) :=
    (hsumw.clog_one_sub.neg).congr fun i ↦ (hlogf i).symm
  simp_rw [← hlogf]
  exact Complex.cexp_tsum_eq_tprod hfn hsumlog

/-- Planning source: Cyclotomic.lean:236; planning contract. -/
theorem differentiableAt_logSum_of_two_le
    {ι : Type*} (N : ι → ℕ) (c : ι → ℂ) (s₀ : ℝ) (hs₀ : 1 < s₀)
    (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ = 1)
    (hsummr : ∀ r : ℝ, 1 < r → Summable (fun i ↦ (N i : ℝ) ^ (-r))) :
    DifferentiableAt ℝ
      (fun s : ℝ ↦ ∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))) s₀ := by
  set ε : ℝ := (s₀ - 1) / 2 with hε
  set t : Set ℝ := Set.Ioi (1 + ε) with ht
  have htopen : IsOpen t := isOpen_Ioi
  have htconn : IsPreconnected t := (convex_Ioi _).isPreconnected
  have hs₀t : s₀ ∈ t := by rw [ht]; simp only [Set.mem_Ioi]; rw [hε]; linarith
  set g : ι → ℝ → ℂ := fun i s ↦ -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) with hg
  set g' : ι → ℝ → ℂ := fun i s ↦
    -((-(c i * ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1)))) /
        (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))) with hg'
  set u : ι → ℝ := fun i ↦ 2 * Real.log (N i) * (N i : ℝ) ^ (-(1 + ε)) with hu
  have hNRpos : ∀ i, (0 : ℝ) < N i := fun i ↦ by have := hN i; positivity
  have hN1 : ∀ i, (1 : ℝ) ≤ N i := fun i ↦ by have := hN i; exact_mod_cast Nat.one_le_of_lt this
  have hlog0 : ∀ i, 0 ≤ Real.log (N i) := fun i ↦ Real.log_nonneg (hN1 i)
  have hwn : ∀ i, ∀ s : ℝ, ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ = (N i : ℝ) ^ (-s) := fun i s ↦ by
    rw [norm_mul, hc, one_mul, Complex.norm_natCast_cpow_of_pos (by have := hN i; omega),
      Complex.neg_re, Complex.ofReal_re]
  have hN2s : ∀ i, ∀ s : ℝ, 1 ≤ s → (2 : ℝ) ≤ (N i : ℝ) ^ s := fun i s hs ↦ by
    have h2N : (2 : ℝ) ≤ N i := by have := hN i; exact_mod_cast this
    exact h2N.trans (Real.self_le_rpow_of_one_le (by linarith) hs)
  have hwle : ∀ i, ∀ s ∈ t, ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ ≤ 1 / 2 := by
    intro i s hst
    simp only [ht, Set.mem_Ioi] at hst
    rw [hwn, Real.rpow_neg (hNRpos i).le,
      inv_le_comm₀ (Real.rpow_pos_of_pos (hNRpos i) _) (by norm_num)]
    linarith [hN2s i s (by linarith)]
  have hslit : ∀ i, ∀ s ∈ t, (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) ∈ Complex.slitPlane := by
    intro i s hst
    have hlt : ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ < 1 := lt_of_le_of_lt (hwle i s hst) (by norm_num)
    rw [sub_eq_add_neg]
    exact Complex.mem_slitPlane_of_norm_lt_one
      (z := -(c i * (N i : ℂ) ^ (-(s : ℂ)))) (by simpa using hlt)
  have husum : Summable u := by
    have hδpos : 0 < ε / 2 := by linarith
    have hr'1 : 1 < (1 + ε) - ε / 2 := by linarith
    refine Summable.of_nonneg_of_le ?_ ?_ ((hsummr ((1 + ε) - ε / 2) hr'1).mul_left (2 / (ε / 2)))
    · intro i; rw [hu]; have := hlog0 i; positivity
    · intro i
      rw [hu]
      set n : ℝ := (N i : ℝ)
      have hlog : Real.log n ≤ n ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div (hNRpos i).le hδpos
      calc 2 * Real.log n * n ^ (-(1 + ε)) ≤ 2 * (n ^ (ε / 2) / (ε / 2)) * n ^ (-(1 + ε)) := by
            gcongr
        _ = (2 / (ε / 2)) * n ^ (-((1 + ε) - ε / 2)) := by
              rw [show -((1 + ε) - ε / 2) = (ε / 2) + (-(1 + ε)) by ring, Real.rpow_add (hNRpos i)]
              field_simp
              ring
  have hderiv : ∀ i, ∀ s ∈ t, HasDerivAt (g i) (g' i s) s := by
    intro i s hst
    have hN0 : (N i : ℂ) ≠ 0 := by exact_mod_cast (by have := hN i; omega : N i ≠ 0)
    have hpow : HasDerivAt (fun z : ℂ ↦ (N i : ℂ) ^ (-z))
        ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1)) (s : ℂ) := by
      have houter : HasDerivAt (fun z : ℂ ↦ (N i : ℂ) ^ z)
          ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ)) (-(s : ℂ)) :=
        (Complex.hasStrictDerivAt_const_cpow (Or.inl hN0)).hasDerivAt
      exact houter.comp (s : ℂ) (hasDerivAt_neg' (s : ℂ))
    have hin : HasDerivAt (fun z : ℂ ↦ 1 - c i * (N i : ℂ) ^ (-z))
        (-(c i * ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1)))) (s : ℂ) := by
      simpa using (hpow.const_mul (c i)).const_sub 1
    have hlog : HasDerivAt (fun z : ℂ ↦ Complex.log (1 - c i * (N i : ℂ) ^ (-z)))
        ((-(c i * ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1)))) /
          (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))) (s : ℂ) := hin.clog (by simpa using hslit i s hst)
    exact (hlog.neg).comp_ofReal
  have hbound : ∀ i, ∀ s ∈ t, ‖g' i s‖ ≤ u i := by
    intro i s hst
    simp only [ht, Set.mem_Ioi] at hst
    set w : ℂ := c i * (N i : ℂ) ^ (-(s : ℂ)) with hw
    have hwlei : ‖w‖ ≤ 1 / 2 := hwle i s (by simp [ht, hst])
    have hden : (1 : ℝ) / 2 ≤ ‖1 - w‖ := by
      have := norm_sub_norm_le (1 : ℂ) w; rw [norm_one] at this; linarith
    have hdenpos : 0 < ‖1 - w‖ := by linarith
    have hnum : ‖(-(c i * ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1))))‖
        = (N i : ℝ) ^ (-s) * Real.log (N i) := by
      rw [show c i * ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1))
          = -(c i * (N i : ℂ) ^ (-(s : ℂ))) * Complex.log (N i : ℂ) by ring]
      rw [norm_neg, norm_mul, norm_neg, ← hw, hwn,
        show Complex.log (N i : ℂ) = ((Real.log (N i) : ℝ) : ℂ) by
          rw [← Complex.ofReal_natCast, Complex.ofReal_log (hNRpos i).le],
        Complex.norm_real, Real.norm_of_nonneg (hlog0 i)]
    rw [hg', norm_neg, norm_div, hnum, hu, div_le_iff₀ hdenpos]
    have hrns : 0 ≤ (N i : ℝ) ^ (-s) := Real.rpow_nonneg (hNRpos i).le _
    have hmono : (N i : ℝ) ^ (-s) ≤ (N i : ℝ) ^ (-(1 + ε)) := by
      apply Real.rpow_le_rpow_of_exponent_le (hN1 i); linarith
    have hrn1 : 0 ≤ (N i : ℝ) ^ (-(1 + ε)) := Real.rpow_nonneg (hNRpos i).le _
    nlinarith [hden, hlog0 i, hrns, hmono, mul_nonneg hrns (hlog0 i), mul_nonneg hrn1 (hlog0 i)]
  have hg0 : Summable fun i ↦ g i s₀ := by
    have hbase : Summable (fun i ↦ (N i : ℝ) ^ (-s₀)) := hsummr s₀ hs₀
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun i ↦ norm_nonneg _) (fun i ↦ ?_) (hbase.mul_left 2)
    set w : ℂ := c i * (N i : ℂ) ^ (-(s₀ : ℂ)) with hw
    have hwlei : ‖w‖ ≤ 1 / 2 := hwle i s₀ hs₀t
    have hkey : ‖Complex.log (1 - w)‖ ≤ 3 / 2 * ‖w‖ := by
      simpa [sub_eq_add_neg] using
        Complex.norm_log_one_add_half_le_self (z := -w) (by simpa using hwlei)
    rw [hg, norm_neg]
    calc ‖Complex.log (1 - w)‖ ≤ 3 / 2 * ‖w‖ := hkey
      _ ≤ 2 * ‖w‖ := by nlinarith [norm_nonneg w]
      _ = 2 * (N i : ℝ) ^ (-s₀) := by rw [hwn i s₀]
  exact (hasDerivAt_tsum_of_isPreconnected husum htopen htconn hderiv hbound hs₀t hg0
    hs₀t).differentiableAt

/-- Planning source: Cyclotomic.lean:358; planning contract. -/
theorem hasDerivAt_logSum_eq_logDeriv
    (G : ℝ → ℂ) (G' : ℂ) (s₀ : ℝ) (hs₀ : 1 < s₀) (Lf : ℂ → ℂ) (hG : HasDerivAt G G' s₀)
    (hLfdiff : DifferentiableAt ℂ Lf (s₀ : ℂ))
    (heq : ∀ s : ℝ, 1 < s → Complex.exp (G s) = Lf (s : ℂ)) (hLf0 : Lf (s₀ : ℂ) ≠ 0) :
    G' = deriv Lf (s₀ : ℂ) / Lf (s₀ : ℂ) := by
  have hexpG : HasDerivAt (fun s : ℝ ↦ Complex.exp (G s)) (G' * Complex.exp (G s₀)) s₀ := by
    simpa [mul_comm] using hG.cexp
  have hLfreal : HasDerivAt (fun s : ℝ ↦ Lf (s : ℂ)) (deriv Lf (s₀ : ℂ)) s₀ :=
    (hLfdiff.hasDerivAt).comp_ofReal
  have hev : (fun s : ℝ ↦ Complex.exp (G s)) =ᶠ[𝓝 s₀] (fun s : ℝ ↦ Lf (s : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hs₀] with s hs using heq s hs
  have hdereq : G' * Complex.exp (G s₀) = deriv Lf (s₀ : ℂ) :=
    hexpG.unique (hLfreal.congr_of_eventuallyEq hev)
  rw [heq s₀ hs₀] at hdereq
  field_simp at hdereq ⊢
  linear_combination hdereq

/-- Planning source: Cyclotomic.lean:377; planning contract. -/
theorem norm_bounded_nhdsGT_of_deriv_continuousOn
    (G : ℝ → ℂ) (F : ℝ → ℂ) (hGderiv : ∀ s : ℝ, 1 < s → HasDerivAt G (F s) s)
    (hFcont : ContinuousOn F (Set.Icc 1 2)) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖G s‖ ≤ C := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ s ∈ Set.Icc (1 : ℝ) 2, ‖F s‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn hFcont
  refine ⟨‖G 2‖ + M, ?_⟩
  have h2 : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 := nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, h2] with s hs1 hs2
  simp only [Set.mem_Ioi] at hs1
  have hsub : Set.Icc s 2 ⊆ Set.Icc (1 : ℝ) 2 := Set.Icc_subset_Icc hs1.le le_rfl
  have hdiff : ∀ x ∈ Set.Icc s 2, DifferentiableAt ℝ G x := fun x hx ↦
    (hGderiv x (lt_of_lt_of_le hs1 hx.1)).differentiableAt
  have hbnd : ∀ x ∈ Set.Icc s 2, ‖deriv G x‖ ≤ M := fun x hx ↦ by
    rw [(hGderiv x (lt_of_lt_of_le hs1 hx.1)).deriv]; exact hM x (hsub hx)
  have hmvt : ‖G s - G 2‖ ≤ M * ‖s - 2‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbnd (convex_Icc s 2)
      (Set.right_mem_Icc.mpr hs2.le) (Set.left_mem_Icc.mpr hs2.le)
  have hsm : ‖s - 2‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 1 (by norm_num))
  calc ‖G s‖ ≤ ‖G s - G 2‖ + ‖G 2‖ := norm_le_norm_sub_add _ _
    _ ≤ ‖G 2‖ + M := by nlinarith [hsm]

/-- Planning source: Cyclotomic.lean:483; planning contract. -/
theorem norm_logSum_bounded_nhdsGT_aux
    {ι : Type*} (N : ι → ℕ) (c : ι → ℂ) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ = 1)
    (hsummr : ∀ r : ℝ, 1 < r → Summable (fun i ↦ (N i : ℝ) ^ (-r)))
    (Lf : ℂ → ℂ) (D : Set ℂ) (hDopen : IsOpen D) (hmemD : ∀ s : ℝ, 1 ≤ s → (s : ℂ) ∈ D)
    (hLf_an : AnalyticOn ℂ Lf D) (hLf0 : Lf 1 ≠ 0)
    (hexpeq : ∀ s : ℝ, 1 < s →
      Complex.exp (∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))) = Lf (s : ℂ)) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))‖ ≤ C := by
  set G : ℝ → ℂ := fun s ↦ ∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) with hGdef
  have hLf_ne : ∀ s : ℝ, 1 ≤ s → Lf (s : ℂ) ≠ 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs with hs1 | hs1
    · rw [← hs1]; simpa using hLf0
    · rw [← hexpeq s hs1]; exact Complex.exp_ne_zero _
  have hanNhd : AnalyticOnNhd ℂ Lf D := (hDopen.analyticOn_iff_analyticOnNhd).mp hLf_an
  have hLfdiff : ∀ s : ℝ, 1 ≤ s → DifferentiableAt ℂ Lf (s : ℂ) := fun s hs ↦
    (hanNhd (s : ℂ) (hmemD s hs)).differentiableAt
  set F : ℝ → ℂ := fun s ↦ deriv Lf (s : ℂ) / Lf (s : ℂ) with hF
  have hFcont : ContinuousOn F (Set.Icc 1 2) := by
    have hLfca : ∀ s : ℝ, 1 ≤ s → ContinuousAt (fun s : ℝ ↦ Lf (s : ℂ)) s := fun s hs ↦
      ((hanNhd (s : ℂ) (hmemD s hs)).continuousAt).comp Complex.continuous_ofReal.continuousAt
    have hdLfca : ∀ s : ℝ, 1 ≤ s → ContinuousAt (fun s : ℝ ↦ deriv Lf (s : ℂ)) s := fun s hs ↦
      (((hanNhd (s : ℂ) (hmemD s hs)).deriv).continuousAt).comp
        Complex.continuous_ofReal.continuousAt
    refine ContinuousOn.div ?_ ?_ (fun s hs ↦ hLf_ne s hs.1)
    · exact fun s hs ↦ (hdLfca s hs.1).continuousWithinAt
    · exact fun s hs ↦ (hLfca s hs.1).continuousWithinAt
  have hGderiv : ∀ s : ℝ, 1 < s → HasDerivAt G (F s) s := by
    intro s hs
    have hGdiff : DifferentiableAt ℝ G s :=
      differentiableAt_logSum_of_two_le N c s hs hN hc hsummr
    have hval : deriv G s = F s :=
      hasDerivAt_logSum_eq_logDeriv G (deriv G s) s hs Lf hGdiff.hasDerivAt
        (hLfdiff s hs.le) hexpeq (hLf_ne s hs.le)
    rw [hF] at hval ⊢
    rw [← hval]
    exact hGdiff.hasDerivAt
  exact norm_bounded_nhdsGT_of_deriv_continuousOn G F hGderiv hFcont

/-- Planning source: Cyclotomic.lean:443; planning contract. -/
theorem norm_logSumTerm_sub_self_le_aux
    {ι : Type*} (N : ι → ℕ) (c : ι → ℂ) (s : ℝ) (hs : 1 < s)
    (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ = 1) (i : ι) :
    ‖-Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) - c i * (N i : ℂ) ^ (-(s : ℂ))‖
      ≤ (N i : ℝ) ^ (-(2 : ℝ)) := by
  have hNRpos : (0 : ℝ) < N i := by have := hN i; positivity
  have hwn : ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ = (N i : ℝ) ^ (-s) := by
    rw [norm_mul, hc, one_mul, Complex.norm_natCast_cpow_of_pos (by have := hN i; omega),
      Complex.neg_re, Complex.ofReal_re]
  have hslit : (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) ∈ Complex.slitPlane := by
    have h1N : (1 : ℝ) < N i := by have := hN i; exact_mod_cast (by omega : 1 < N i)
    have hlt : ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ < 1 := by
      rw [hwn]; exact Real.rpow_lt_one_of_one_lt_of_neg h1N (by linarith)
    rw [sub_eq_add_neg]
    exact Complex.mem_slitPlane_of_norm_lt_one
      (z := -(c i * (N i : ℂ) ^ (-(s : ℂ)))) (by simpa using hlt)
  set w : ℂ := c i * (N i : ℂ) ^ (-(s : ℂ)) with hw
  have h2N : (2 : ℝ) ≤ N i := by have := hN i; exact_mod_cast this
  have hwle : ‖w‖ ≤ 1 / 2 := by
    rw [hw, hwn]
    have hNs : (2 : ℝ) ≤ (N i : ℝ) ^ s :=
      le_trans h2N ((Real.rpow_one (N i : ℝ)).symm.trans_le
        (Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le))
    rw [Real.rpow_neg hNRpos.le, inv_le_comm₀ (Real.rpow_pos_of_pos hNRpos _) (by norm_num)]
    linarith
  have hlt : ‖w‖ < 1 := by linarith
  have hkey := Complex.norm_log_one_sub_inv_sub_self_le hlt
  rw [Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit)] at hkey
  have h1 : (1 - ‖w‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hsq : ‖-Complex.log (1 - w) - w‖ ≤ ‖w‖ ^ 2 := by
    refine hkey.trans ?_; nlinarith [sq_nonneg ‖w‖, h1, norm_nonneg w]
  have hwsq : ‖w‖ ^ 2 = (N i : ℝ) ^ (-(2 * s)) := by
    rw [hw, hwn, ← Real.rpow_natCast ((N i : ℝ) ^ (-s)) 2, ← Real.rpow_mul hNRpos.le]
    ring_nf
  exact hsq.trans (hwsq.trans_le (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)))

/-- Planning source: Cyclotomic.lean:526; planning contract. -/
theorem norm_tsumLinear_bounded_of_logSum_bounded_aux
    {ι : Type*} (N : ι → ℕ) (c : ι → ℂ) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ = 1)
    (hsummr : ∀ r : ℝ, 1 < r → Summable (fun i ↦ (N i : ℝ) ^ (-r)))
    (hGbdd : ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))‖ ≤ C) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖∑' i, c i * (N i : ℂ) ^ (-(s : ℂ))‖ ≤ C := by
  obtain ⟨Cg, hCg⟩ := hGbdd
  have hsumN2 : Summable (fun i ↦ (N i : ℝ) ^ (-(2 : ℝ))) := hsummr 2 one_lt_two
  have hwn : ∀ i, ∀ s : ℝ, ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ = (N i : ℝ) ^ (-s) := fun i s ↦ by
    rw [norm_mul, hc, one_mul, Complex.norm_natCast_cpow_of_pos (by have := hN i; omega),
      Complex.neg_re, Complex.ofReal_re]
  have hsumlin : ∀ s : ℝ, 1 < s → Summable (fun i ↦ c i * (N i : ℂ) ^ (-(s : ℂ))) := fun s hs ↦
    Summable.of_norm ((hsummr s hs).congr fun i ↦ (hwn i s).symm)
  have hsumtail : ∀ s : ℝ, 1 < s →
      Summable (fun i ↦ -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))
        - c i * (N i : ℂ) ^ (-(s : ℂ))) := fun s hs ↦
    Summable.of_norm (Summable.of_nonneg_of_le (fun i ↦ norm_nonneg _)
      (fun i ↦ norm_logSumTerm_sub_self_le_aux N c s hs hN hc i) hsumN2)
  refine ⟨Cg + ∑' i, (N i : ℝ) ^ (-(2 : ℝ)), ?_⟩
  filter_upwards [hCg, self_mem_nhdsWithin] with s hCgs hs1
  simp only [Set.mem_Ioi] at hs1
  have hsumG : Summable (fun i ↦ -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))) := by
    simpa using (hsumtail s hs1).add (hsumlin s hs1)
  have hPsub : (∑' i, c i * (N i : ℂ) ^ (-(s : ℂ)))
      = (∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ))))
        - ∑' i, (-Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))
          - c i * (N i : ℂ) ^ (-(s : ℂ))) := by
    rw [← hsumG.tsum_sub ((hsumG.sub (hsumlin s hs1)).congr fun i ↦ rfl)]
    exact tsum_congr fun i ↦ by ring
  rw [hPsub]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  exact (norm_tsum_le_tsum_norm (hsumtail s hs1).norm).trans
    (((hsumtail s hs1).norm.tsum_le_tsum
      (fun i ↦ norm_logSumTerm_sub_self_le_aux N c s hs1 hN hc i) hsumN2))

/-- Planning source: Cyclotomic.lean:567; planning contract. -/
theorem artinLSeries_prime_sum_bounded_of_analytic_extension
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L)
    (_hχ : χ ≠ 1) (Lf : ℂ → ℂ)
    (hLf_an : AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re})
    (hLf_eq : ∀ s : ℂ, 1 < s.re →
      Lf s = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
        galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s))
    (hLf0 : Lf 1 ≠ 0) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ ≤ C := by
  classical
  set ι := {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}
  set N : ι → ℕ := fun 𝔭 ↦ Ideal.absNorm 𝔭.1
  set c : ι → ℂ := fun 𝔭 ↦ (χ (frobeniusClass K L 𝔭.1).out : ℂ) with hc
  set G : ℝ → ℂ := fun s ↦ ∑' 𝔭 : ι, -Complex.log (1 - c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ))) with hGdef
  have hc1 : ∀ 𝔭 : ι, ‖c 𝔭‖ = 1 := fun 𝔭 ↦
    (((Units.coeHom ℂ).comp χ).isOfFinOrder
      (isOfFinOrder_of_finite (frobeniusClass K L 𝔭.1).out)).norm_eq_one
  have hN2 : ∀ 𝔭 : ι, 2 ≤ N 𝔭 := fun 𝔭 ↦
    two_le_absNorm_prime K 𝔭.1 𝔭.2.1 (UnramifiedIn.ne_bot K L 𝔭.2.2)
  have hsummr : ∀ r : ℝ, 1 < r → Summable (fun 𝔭 : ι ↦ (N 𝔭 : ℝ) ^ (-r)) := fun r hr ↦
    ((summable_prime_absNorm_rpow K _ hr).comp_injective
      (unramifiedPrime_toPrimeNeBot_injective K L)).congr fun 𝔭 ↦ rfl
  have hwn : ∀ 𝔭 : ι, ∀ s : ℝ, ‖c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ))‖ = (N 𝔭 : ℝ) ^ (-s) := by
    intro 𝔭 s
    rw [norm_mul, hc1, one_mul, Complex.norm_natCast_cpow_of_pos (by have := hN2 𝔭; omega),
      Complex.neg_re, Complex.ofReal_re]
  have hslit : ∀ 𝔭 : ι, ∀ s : ℝ, 1 < s →
      (1 - c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ))) ∈ Complex.slitPlane := by
    intro 𝔭 s hs
    have h1N : (1 : ℝ) < N 𝔭 := by have := hN2 𝔭; exact_mod_cast (by omega : 1 < N 𝔭)
    have hlt : ‖c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ))‖ < 1 := by
      rw [hwn]; exact Real.rpow_lt_one_of_one_lt_of_neg h1N (by linarith)
    rw [sub_eq_add_neg]
    exact Complex.mem_slitPlane_of_norm_lt_one
      (z := -(c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ)))) (by simpa using hlt)
  have hexpeq : ∀ s : ℝ, 1 < s → Complex.exp (G s) = Lf (s : ℂ) := by
    intro s hs
    have hsc : 1 < ((s : ℂ)).re := by simpa using hs
    have hsumw : Summable (fun 𝔭 : ι ↦ c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ))) :=
      summable_twistedPrimeSum K L χ hs
    rw [hGdef, cexp_logSum_eq_tprod _ hsumw (fun 𝔭 ↦ hslit 𝔭 s hs)]
    rw [show (fun 𝔭 : ι ↦ (1 - c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ)))⁻¹)
        = (fun 𝔭 : ι ↦ (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ)
            * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))⁻¹) from rfl,
      exists_artinLSeries_eulerProduct_abelian K L χ (s : ℂ) hsc, ← hLf_eq (s : ℂ) hsc]
  set D : Set ℂ := {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} with hD
  have hDopen : IsOpen D := by rw [hD]; exact isOpen_lt continuous_const Complex.continuous_re
  have hmemD : ∀ s : ℝ, 1 ≤ s → (s : ℂ) ∈ D := fun s hs ↦ by
    rw [hD]; simp only [Set.mem_setOf_eq, Complex.ofReal_re]
    have hfr : 0 < Module.finrank ℚ K := Module.finrank_pos
    have : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ := by positivity
    linarith
  exact norm_tsumLinear_bounded_of_logSum_bounded_aux N c hN2 hc1 hsummr
    (norm_logSum_bounded_nhdsGT_aux N c hN2 hc1 hsummr Lf D hDopen hmemD hLf_an hLf0 hexpeq)

/-- Planning source: Cyclotomic.lean:632; planning contract. -/
theorem artinLSeries_prime_sum_bounded_of_ne_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    [hAb : IsMulCommutative Gal(L/K)] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ ≤ C := by
  obtain ⟨Lf, hLf_an, hLf_eq⟩ := artinLSeries_analytic_extension K L m hm χ hχ
  exact artinLSeries_prime_sum_bounded_of_analytic_extension K L χ hχ Lf hLf_an hLf_eq
    (artinLSeries_one_ne_zero K L m hm χ hχ Lf hLf_an hLf_eq)

/-- Planning source: Cyclotomic.lean:855; planning contract. -/
theorem exists_sum_charTwist_erase_norm_bounded
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2)
    [Fintype (galoisCharacter K L)] [DecidableEq (galoisCharacter K L)] (σ : Gal(L/K)) :
    ∃ CB : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      ‖∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
          ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ ≤ CB := by
  have : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
  have hterm : ∀ χ : galoisCharacter K L, χ ≠ 1 → ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ ≤ C := fun χ hχ ↦ by
    obtain ⟨C, hC⟩ := artinLSeries_prime_sum_bounded_of_ne_one K L m hm χ hχ
    refine ⟨C, ?_⟩
    filter_upwards [hC] with s hs
    have hnorm1 : ‖((χ σ : ℂ))⁻¹‖ = 1 := by
      rw [norm_inv, inv_eq_one]
      exact (((Units.coeHom ℂ).comp χ).isOfFinOrder (isOfFinOrder_of_finite σ)).norm_eq_one
    rw [norm_mul, hnorm1, one_mul]
    exact hs
  have hCfun : ∀ χ : galoisCharacter K L, ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      χ ∈ Finset.univ.erase (1 : galoisCharacter K L) →
        ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ ≤ C := fun χ ↦ by
    by_cases hχ : χ = 1
    · refine ⟨0, ?_⟩
      filter_upwards with s hmem
      exact absurd (Finset.mem_erase.mp hmem).1 (not_not.mpr hχ)
    · obtain ⟨C, hC⟩ := hterm χ hχ
      refine ⟨C, ?_⟩
      filter_upwards [hC] with s hs _
      exact hs
  choose C hC using hCfun
  refine ⟨∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L), C χ, ?_⟩
  have hall : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
      ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ ≤ C χ :=
    (eventually_all_finset _).mpr fun χ hmem ↦ (hC χ).mono fun s hs ↦ hs hmem
  filter_upwards [hall] with s hs
  calc ‖∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L), ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖
      ≤ ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
          ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ := norm_sum_le _ _
    _ ≤ ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L), C χ :=
      Finset.sum_le_sum fun χ hχ ↦ hs χ hχ

/-- Planning source: Cyclotomic.lean:690; planning contract. -/
theorem primeIdealZetaSum_unramified_div_log_tendsto_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s
          / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) := by
  set U : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}
  set R : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}
  have hdisj : Disjoint U R :=
    Set.disjoint_left.mpr fun 𝔭 hu hr ↦ hr.2.2 hu.2
  have hcover : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ U ∪ R := fun 𝔭 hp hne ↦ by
    by_cases hunr : UnramifiedIn K L 𝔭
    · exact Or.inl ⟨hp, hunr⟩
    · exact Or.inr ⟨hp, hne, hunr⟩
  have hRfin : R.Finite := finite_ramifiedIn K L
  obtain ⟨CR, hCR⟩ : ∃ CR : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), primeIdealZetaSum R s ≤ CR := by
    refine ⟨Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ R ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Ioi] at hs
    exact primeIdealZetaSum_le_card_of_finite K hRfin (by linarith)
  have hRzero : Tendsto (fun s : ℝ ↦ primeIdealZetaSum R s / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 0) := by
    have hL := tendsto_log_one_div_sub_one_atTop
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop tendsto_const_nhds hL (a := CR))
    filter_upwards [hCR, hL.eventually_gt_atTop 0] with s hub hLpos
    have hRnn : 0 ≤ primeIdealZetaSum R s := by
      rw [primeIdealZetaSum_def]
      exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (div_nonneg hRnn hLpos.le)]
    gcongr
  have hcomb : Tendsto (fun s : ℝ ↦
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s / Real.log (1 / (s - 1))
        - primeIdealZetaSum R s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) := by
    simpa using (primeIdealZetaSum_univ_tendsto_log K).sub hRzero
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hadd : primeIdealZetaSum U s + primeIdealZetaSum R s =
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s := by
    rw [← primeIdealZetaSum_union_of_disjoint K hdisj hs,
      primeIdealZetaSum_eq_univ_of_forall_prime_mem K hcover s]
  rw [← sub_div, ← hadd, add_sub_cancel_right]

/-- Planning source: Cyclotomic.lean:898; planning contract. -/
theorem primeIdealZetaSum_frobeniusFibre_asymp
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2)
    (σ : Gal(L/K)) :
    Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 ((Nat.card Gal(L/K) : ℝ)⁻¹)) := by
  classical
  have : Fintype (galoisCharacter K L) := Fintype.ofFinite _
  set N : ℕ := Nat.card Gal(L/K) with hN
  have hNpos : 0 < N := Nat.card_pos
  set B : ℝ → ℂ := fun s ↦ ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
    ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s
  obtain ⟨CB, hCB⟩ : ∃ CB : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖B s‖ ≤ CB :=
    exists_sum_charTwist_erase_norm_bounded K L m hm σ
  have hBlog : Tendsto (fun s : ℝ ↦ (B s).re / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) := by
    have hL := tendsto_log_one_div_sub_one_atTop
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop tendsto_const_nhds hL (a := CB))
    filter_upwards [hCB, hL.eventually_gt_atTop 0] with s hub hLpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hLpos]
    gcongr
    exact (RCLike.abs_re_le_norm (B s)).trans hub
  have hlim : Tendsto (fun s : ℝ ↦ (N : ℝ)⁻¹ *
      (primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s
          / Real.log (1 / (s - 1))
        + (B s).re / Real.log (1 / (s - 1)))) (𝓝[>] 1) (𝓝 ((N : ℝ)⁻¹)) := by
    have := ((primeIdealZetaSum_unramified_div_log_tendsto_one K L).add hBlog).const_mul (N : ℝ)⁻¹
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hmaster : (N : ℝ) *
      primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
      = primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s + (B s).re := by
    rw [hN]
    exact card_mul_frobeniusFibre_eq K L m σ hs
  rw [← add_div, ← hmaster, mul_div_assoc, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hNpos.ne'), one_mul]

/-- Planning source: Cyclotomic.lean:941; planning contract. -/
theorem tendsto_ratio_of_log_asymp_numerator
    (num den : ℝ → ℝ) (c : ℝ)
    (hnum : Tendsto (fun s : ℝ ↦ num s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 c))
    (hden : Tendsto (fun s : ℝ ↦ den s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1)) :
    Tendsto (fun s : ℝ ↦ num s / den s) (𝓝[>] 1) (𝓝 c) := by
  have hL : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), Real.log (1 / (s - 1)) ≠ 0 := by
    have h2 : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, h2] with s hs1 hs2
    have hpos : (0 : ℝ) < s - 1 := sub_pos.mpr hs1
    exact (Real.log_pos ((one_lt_div₀ hpos).2 (by linarith))).ne'
  exact (div_one c ▸ hnum.div hden one_ne_zero).congr'
    (hL.mono fun s hs ↦ div_div_div_cancel_right₀ hs (num s) (den s))

/-- Planning source: Cyclotomic.lean:962; planning contract. -/
theorem cyclotomic_density_from_two_sided_asymp
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2)
    (σ : Gal(L/K)) :
    Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 ((Nat.card Gal(L/K) : ℝ)⁻¹)) :=
  tendsto_ratio_of_log_asymp_numerator _ _ _
    (primeIdealZetaSum_frobeniusFibre_asymp K L m hm σ)
    (primeIdealZetaSum_univ_tendsto_log K)

/-- Planning source: Cyclotomic.lean:982; planning contract. -/
theorem chebotarev_cyclotomic
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2)
    (σ : Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) :=
  cyclotomic_density_from_two_sided_asymp K L m hm σ

end Cox.Chebotarev
