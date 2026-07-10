/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.PowerBasis

/-!
# Common lemmas for number field examples

This file contains shared algebraic helpers used by several number field examples.
-/

namespace NumberField.FieldExamples

/-- A divisor of `p²` for prime `p` is `p` once the cases `1` and `p²` are excluded. -/
theorem eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq {m p : ℕ} (hp : p.Prime)
    (hdvd : m ∣ p ^ 2) (h1 : m ≠ 1) (hp2 : m ≠ p ^ 2) : m = p := by
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases k
  · exact (h1 (by simpa using hkeq)).elim
  · simpa using hkeq
  · exact (hp2 hkeq).elim

/-- If two non-unit natural numbers multiply to `p²`, the left factor is `p`. -/
theorem left_eq_prime_of_mul_eq_prime_sq_of_ne_one {m n p : ℕ} (hp : p.Prime)
    (hmul : m * n = p ^ 2) (hm1 : m ≠ 1) (hn1 : n ≠ 1) : m = p :=
  eq_prime_of_dvd_prime_sq_of_ne_one_of_ne_sq hp ⟨n, hmul.symm⟩ hm1 fun hm2 ↦
    hn1 <| Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by simpa [hm2] using hmul)

/-- A nonzero residue modulo a prime has a natural-number representative for an integer inverse. -/
theorem exists_int_inverse_mod_prime (p : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : (a : ZMod p) ≠ 0) : ∃ m : ℕ, ∃ k : ℤ, (m : ℤ) * a - 1 = (p : ℤ) * k := by
  refine ⟨(((a : ZMod p)⁻¹).val), ?_⟩
  have hm : (((((a : ZMod p)⁻¹).val : ℕ) : ZMod p) * (a : ZMod p)) = 1 := by
    rw [ZMod.natCast_rightInverse]
    exact inv_mul_cancel₀ ha
  have hlift : (p : ℤ) ∣ (((((a : ZMod p)⁻¹).val : ℕ) : ℤ) * a - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination hm
  obtain ⟨k, hk⟩ := hlift
  exact ⟨k, hk⟩

/-- Nonzero ideals with equal absolute norms are equal when one is contained in the other. -/
theorem eq_of_le_of_absNorm_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] {I J : Ideal R} (hle : I ≤ J) {n : ℕ}
    (hI : Ideal.absNorm I = n) (hJ : Ideal.absNorm J = n) (hn : n ≠ 0) : I = J := by
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hmul := _root_.map_mul Ideal.absNorm J C
  rw [← hC, hI, hJ] at hmul
  have hC1 : Ideal.absNorm C = 1 :=
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
      (by rw [mul_one]; exact hmul)).symm
  rw [hC, Ideal.absNorm_eq_one_iff.mp hC1, Ideal.mul_top]

/-- Turn a strict rational absolute-value comparison between integers into a `natAbs`
comparison. -/
theorem natAbs_lt_of_abs_ratCast_lt {m n : ℤ} (h : |(m : ℚ)| < |(n : ℚ)|) :
    m.natAbs < n.natAbs := by
  have hltZ : |m| < |n| := by exact_mod_cast h
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hltZ
  exact_mod_cast hltZ

/-- The homomorphism from a finite cyclic additive index to powers of a torsion element. -/
def torsionPowerHom {G : Type*} [Group G] (n : ℕ) [NeZero n] (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  MonoidHom.mk' (fun a => g ^ (Multiplicative.toAdd a).val) fun a b => by
    have hpow : ∀ k : ℕ, g ^ k = g ^ (k % n) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod k n]
      rw [pow_add, pow_mul, hg, one_pow, one_mul]
    calc g ^ (Multiplicative.toAdd (a * b)).val =
        g ^ ((Multiplicative.toAdd (a * b)).val % n) := hpow _
      _ = g ^ (((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) % n) := by
          rw [toAdd_mul, ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_refl n)]
      _ = g ^ ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) := (hpow _).symm
      _ = g ^ (Multiplicative.toAdd a).val * g ^ (Multiplicative.toAdd b).val :=
          pow_add _ _ _

/-- The homomorphism from the rank-one free coordinate to powers of a chosen unit. -/
def rankOnePowerHom {G : Type*} [Group G] (η : G) : Multiplicative (Fin 1 → ℤ) →* G :=
  MonoidHom.mk' (fun f => η ^ (Multiplicative.toAdd f 0)) fun f g => by
    change η ^ ((Multiplicative.toAdd f + Multiplicative.toAdd g) 0) = _
    rw [Pi.add_apply, zpow_add]

/-- A square containment of a mapped prime ideal forces ramification index at least two. -/
theorem two_le_ramificationIdx_of_map_le_sq_of_not_le_pow_succ {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R} {P : Ideal S} {n : ℕ}
    (hle2 : Ideal.map (algebraMap R S) p ≤ P ^ 2)
    (hnle : ¬ Ideal.map (algebraMap R S) p ≤ P ^ (n + 1)) :
    2 ≤ Ideal.ramificationIdx p P := by
  classical
  have hbounded : ∃ m, ∀ k, Ideal.map (algebraMap R S) p ≤ P ^ k → k ≤ m := by
    refine ⟨n, fun k hk ↦ le_of_not_gt fun hnk ↦ ?_⟩
    exact hnle (hk.trans (Ideal.pow_le_pow_right hnk))
  rw [Ideal.ramificationIdx_eq_find hbounded]
  exact Nat.find_spec hbounded 2 hle2

/-- A square containment of a mapped prime ideal makes the ramification index nontrivial. -/
theorem ramificationIdx_ne_one_of_map_le_sq_of_not_le_pow_succ {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R} {P : Ideal S} {n : ℕ}
    (hle2 : Ideal.map (algebraMap R S) p ≤ P ^ 2)
    (hnle : ¬ Ideal.map (algebraMap R S) p ≤ P ^ (n + 1)) :
    Ideal.ramificationIdx p P ≠ 1 := by
  have htwo := two_le_ramificationIdx_of_map_le_sq_of_not_le_pow_succ hle2 hnle
  omega

/-- A square containment over `(p)` makes the prime ramified. -/
theorem not_isUnramifiedAt_of_map_span_natCast_le_sq_of_not_le_pow_succ {R : Type*}
    [CommRing R] [Algebra ℤ R] [IsDedekindDomain R] [Algebra.EssFiniteType ℤ R]
    [Algebra.IsIntegral ℤ R] {P : Ideal R} [P.IsPrime] {p n : ℕ} (hp : p.Prime)
    (hmem : ((p : ℕ) : R) ∈ P) (hPbot : P ≠ ⊥)
    (hle2 : Ideal.map (algebraMap ℤ R) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ 2)
    (hnle : ¬ Ideal.map (algebraMap ℤ R) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ (n + 1)) :
    ¬ Algebra.IsUnramifiedAt ℤ P := by
  have hidx : Ideal.ramificationIdx (Ideal.span {((p : ℕ) : ℤ)}) P ≠ 1 :=
    ramificationIdx_ne_one_of_map_le_sq_of_not_le_pow_succ hle2 hnle
  have hpz : Prime (((p : ℕ) : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hmem' : algebraMap ℤ R ((p : ℕ) : ℤ) ∈ P := by
    convert hmem using 1
    norm_num
  have hund : Ideal.under ℤ P = Ideal.span {((p : ℕ) : ℤ)} :=
    ((Ideal.liesOver_span_iff (show P ≠ ⊤ from Ideal.IsPrime.ne_top inferInstance) hpz).mpr
      hmem').over.symm
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot, hund]
  exact hidx

/-- Norm comparison rules out containment in the next power of a prime ideal. -/
theorem not_map_span_natCast_le_pow_succ_of_absNorm_span_eq_pow {R : Type*}
    [CommRing R] [Algebra ℤ R] [IsDedekindDomain R] [Module.Free ℤ R] {P : Ideal R}
    {p n k : ℕ} (hp : p.Prime)
    (habsp : Ideal.absNorm (Ideal.span {((p : ℕ) : R)}) = p ^ n)
    (habsP : Ideal.absNorm P = p ^ k) (hk0 : k ≠ 0) :
    ¬ Ideal.map (algebraMap ℤ R) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P ^ (n + 1) := by
  intro hle
  have hle' : Ideal.span {((p : ℕ) : R)} ≤ P ^ (n + 1) := by
    simpa [Ideal.map_span, Set.image_singleton] using hle
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle'
  rw [map_pow, habsp, habsP, ← pow_mul] at hd
  rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hd
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  nlinarith

/-- Euclidean-step inequality. If, under the embedding `𝓞 K ↪ K`, a remainder factors as
`r = b * e` with `0 < |N(b)|` and `|N(e)| ≤ c < 1` (where `N` is the field norm to `ℚ`), then
the integer norms satisfy `|N(r)| < |N(b)|`. This is the contraction step behind
norm-Euclideanity of a ring of integers. -/
theorem abs_intNorm_lt_of_abs_norm_le {K : Type*} [Field K] [NumberField K]
    {b r : 𝓞 K} {bK e : K} {c : ℚ}
    (hbK : bK = algebraMap (𝓞 K) K b)
    (hrK : algebraMap (𝓞 K) K r = bK * e)
    (hb_pos : 0 < |Algebra.norm ℚ bK|)
    (hc : c < 1)
    (hnorm_e : |Algebra.norm ℚ e| ≤ c) :
    |((Algebra.norm ℤ r : ℤ) : ℚ)| < |((Algebra.norm ℤ b : ℤ) : ℚ)| := by
  rw [Algebra.coe_norm_int, Algebra.coe_norm_int]
  change |Algebra.norm ℚ (algebraMap (𝓞 K) K r)| < |Algebra.norm ℚ (algebraMap (𝓞 K) K b)|
  rw [hrK, map_mul, abs_mul, ← hbK]
  calc |Algebra.norm ℚ bK| * |Algebra.norm ℚ e| ≤ |Algebra.norm ℚ bK| * c :=
        mul_le_mul_of_nonneg_left hnorm_e (abs_nonneg _)
    _ < |Algebra.norm ℚ bK| := mul_lt_of_lt_one_right hb_pos hc

/-!
## Generic reduction-mod-`p` (Kummer–Dedekind) machinery

For a ring of integers `𝓞 K` with an integral power basis `pb` and a prime `p`, a root `r`
of the generator's minimal polynomial mod `p` produces a surjection `𝓞 K → ZMod p` whose
kernel is the maximal ideal `(p, pb.gen - r)` of absolute norm `p`. This packages the
per-field "residue map" machinery used to read off the splitting of `p`.
-/

section ResidueHom

variable {K : Type*} [Field K] (pb : PowerBasis ℤ (𝓞 K)) (p : ℕ) (r : ℤ)
  (hr : (Polynomial.aeval ((r : ZMod p))) (minpoly ℤ pb.gen) = 0)

include hr

/-- The reduction homomorphism `𝓞 K → ZMod p` sending the power-basis generator to the
residue `r`, where `r` is a root of the generator's minimal polynomial mod `p`. -/
noncomputable def genResidueHom : 𝓞 K →ₐ[ℤ] ZMod p :=
  pb.lift ((r : ZMod p)) hr

theorem genResidueHom_gen : genResidueHom pb p r hr pb.gen = (r : ZMod p) :=
  pb.lift_gen _ _

theorem genResidueHom_surjective : Function.Surjective (genResidueHom pb p r hr) := by
  intro z
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective z
  exact ⟨((m : ℤ) : 𝓞 K), by rw [map_intCast]; exact hm⟩

theorem ker_genResidueHom :
    RingHom.ker (genResidueHom pb p r hr).toRingHom =
      Ideal.span {(p : 𝓞 K), pb.gen - (r : 𝓞 K)} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [RingHom.mem_ker] at hx
    obtain ⟨q, -, hq⟩ := pb.exists_eq_aeval x
    have key : x - ((q.eval r : ℤ) : 𝓞 K) ∈ Ideal.span {pb.gen - (r : 𝓞 K)} := by
      rw [Ideal.mem_span_singleton, hq]
      have hdvd := Polynomial.sub_dvd_eval_sub pb.gen ((r : ℤ) : 𝓞 K)
        (q.map (algebraMap ℤ (𝓞 K)))
      have e1 : (q.map (algebraMap ℤ (𝓞 K))).eval pb.gen = Polynomial.aeval pb.gen q := by
        rw [Polynomial.eval_map, ← Polynomial.aeval_def]
      have e2 : (q.map (algebraMap ℤ (𝓞 K))).eval ((r : ℤ) : 𝓞 K)
          = ((q.eval r : ℤ) : 𝓞 K) := by
        have hcast : ((r : ℤ) : 𝓞 K) = algebraMap ℤ (𝓞 K) r := by simp [algebraMap_int_eq]
        rw [Polynomial.eval_map, hcast, Polynomial.eval₂_at_apply]
        simp [algebraMap_int_eq]
      rw [e1, e2] at hdvd
      exact hdvd
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp key
    have hphi : ((q.eval r : ℤ) : ZMod p) = 0 := by
      have h1 : genResidueHom pb p r hr (x - ((q.eval r : ℤ) : 𝓞 K)) = 0 := by
        rw [hd, map_mul, map_sub, genResidueHom_gen, map_intCast, sub_self, zero_mul]
      rw [map_sub, map_intCast, show genResidueHom pb p r hr x = 0 from hx, zero_sub,
        neg_eq_zero] at h1
      exact h1
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hphi
    have hx_eq : x = (pb.gen - (r : 𝓞 K)) * d + (p : 𝓞 K) * ((m : ℤ) : 𝓞 K) := by
      have h2 : x = (pb.gen - (r : 𝓞 K)) * d + ((q.eval r : ℤ) : 𝓞 K) := by rw [← hd]; ring
      rw [h2, hm]; push_cast; ring
    rw [hx_eq]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
    · simp
    · simp
  · rw [Ideal.span_le]
    rintro y (rfl | rfl)
    · rw [SetLike.mem_coe, RingHom.mem_ker]; simp
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      have h0 : (genResidueHom pb p r hr) (pb.gen - (r : 𝓞 K)) = 0 := by
        rw [map_sub, genResidueHom_gen, map_intCast, sub_self]
      exact h0

theorem isMaximal_span_gen_sub [Fact p.Prime] :
    (Ideal.span {(p : 𝓞 K), pb.gen - (r : 𝓞 K)}).IsMaximal := by
  rw [← ker_genResidueHom pb p r hr]
  exact RingHom.ker_isMaximal_of_surjective _ (genResidueHom_surjective pb p r hr)

theorem absNorm_span_gen_sub [NumberField K] :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K), pb.gen - (r : 𝓞 K)}) = p := by
  rw [← ker_genResidueHom pb p r hr, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (genResidueHom_surjective pb p r hr)).toEquiv]
  exact Nat.card_zmod p

end ResidueHom

end NumberField.FieldExamples
