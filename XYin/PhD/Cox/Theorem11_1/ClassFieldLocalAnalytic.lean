/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldLogExp
import XYin.PhD.Cox.Theorem11_1.ClassFieldPrincipalUnits
import XYin.PhD.Cox.Theorem11_1.ClassFieldPowerSeries
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-! # Janusz V.3: the local logarithm and exponential

On a sufficiently deep ideal of the completed integers the rational logarithm and
exponential series converge and are mutually inverse. This gives the logarithm
isomorphism of deep principal units (V.3.5) and shows that deep units are nth powers
(V.3.6).
-/

open NumberField IsDedekindDomain Filter
open scoped Topology

noncomputable section

namespace Cox.ClassFieldTheory.LocalCyclic

variable (K : Type*) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

/-- Elements smaller than the square of a positive norm satisfy the common radius bound. -/
theorem sq_inv_mul_norm_lt_one (p x : v.adicCompletion K) (hp0 : 0 < ‖p‖)
    (hx : ‖x‖ < ‖p‖ ^ 2) : (‖p‖⁻¹) ^ 2 * ‖x‖ < 1 := by
  calc (‖p‖⁻¹) ^ 2 * ‖x‖ < (‖p‖⁻¹) ^ 2 * ‖p‖ ^ 2 :=
        mul_lt_mul_of_pos_left hx (pow_pos (inv_pos.mpr hp0) 2)
    _ = 1 := by rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hp0.ne')]

/-- The convergent logarithm and exponential composition is the identity on a deep ideal. -/
theorem exists_log_exp_inverse :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
        logValue K v (expValue K v (x : v.adicCompletion K) - 1) = x := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨p, hp, hp1⟩ := exists_prime_norm_lt_one K v
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < ‖(p : v.adicCompletion K)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  obtain ⟨t₀, ht₀⟩ := exists_ideal_depth_norm_lt K v _ (pow_pos hp0 2)
  exact ⟨t₀, fun t ht x hx => log_exp_inverse_small K v p hp1 _
    (sq_inv_mul_norm_lt_one K v _ _ hp0 (ht₀ t ht x hx))⟩

/-- The other convergent composition gives one plus the original small element. -/
theorem exists_exp_log_inverse :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
        expValue K v (logValue K v (x : v.adicCompletion K)) = 1 + x := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨p, hp, hp1⟩ := exists_prime_norm_lt_one K v
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < ‖(p : v.adicCompletion K)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  obtain ⟨t₀, ht₀⟩ := exists_ideal_depth_norm_lt K v _ (pow_pos hp0 2)
  exact ⟨t₀, fun t ht x hx => exp_log_inverse_small K v p hp1 _
    (sq_inv_mul_norm_lt_one K v _ _ hp0 (ht₀ t ht x hx))⟩

/-- Multiplication of deep principal units becomes addition under the logarithm. -/
theorem exists_log_mul :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ x y : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
        y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
          logValue K v ((x : v.adicCompletion K) + y + x * y) =
            logValue K v (x : v.adicCompletion K) + logValue K v (y : v.adicCompletion K) := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨p, hp, hp1⟩ := exists_prime_norm_lt_one K v
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < ‖(p : v.adicCompletion K)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  obtain ⟨t₀, ht₀⟩ := exists_ideal_depth_norm_lt K v _ (pow_pos hp0 2)
  exact ⟨t₀, fun t ht x y hx hy => log_mul_small K v p hp1 _ _
    (sq_inv_mul_norm_lt_one K v _ _ hp0 (ht₀ t ht x hx))
    (sq_inv_mul_norm_lt_one K v _ _ hp0 (ht₀ t ht y hy))⟩

/-- Janusz V.3.5: convergence and the inverse identities give the actual deep-unit
logarithm isomorphism, characterized by both convergent power series. -/
theorem exists_logIso :
    ∃ t₀ : ℕ, ∀ t ≥ t₀,
      ∃ e : localUnitFiltration K v t ≃*
          Multiplicative ↥(IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t),
        (∀ u : localUnitFiltration K v t,
          HasSum (logTerm K v (((u : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) - 1))
          ((Multiplicative.toAdd (e u)).val : v.adicCompletion K)) ∧
        (∀ y : Multiplicative ↥(IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t),
          HasSum (expTerm K v ((Multiplicative.toAdd y).val : v.adicCompletion K))
          ((e.symm y : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K)) := by
  classical
  let a : ℕ := (exists_log_preserves_filtration K v).choose
  have ha : ∀ t ≥ a, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
      ∃ y : v.adicCompletionIntegers K,
        y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t ∧
        (y : v.adicCompletion K) = logValue K v (x : v.adicCompletion K) :=
    (exists_log_preserves_filtration K v).choose_spec
  let b : ℕ := (exists_exp_preserves_filtration K v).choose
  have hb : ∀ t ≥ b, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
      ∃ y : v.adicCompletionIntegers K,
        y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t ∧
        (y : v.adicCompletion K) = expValue K v (x : v.adicCompletion K) - 1 :=
    (exists_exp_preserves_filtration K v).choose_spec
  let c : ℕ := (exists_log_exp_inverse K v).choose
  have hc : ∀ t ≥ c, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
      logValue K v (expValue K v (x : v.adicCompletion K) - 1) = (x : v.adicCompletion K) :=
    (exists_log_exp_inverse K v).choose_spec
  let d : ℕ := (exists_exp_log_inverse K v).choose
  have hd : ∀ t ≥ d, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
      expValue K v (logValue K v (x : v.adicCompletion K)) = 1 + (x : v.adicCompletion K) :=
    (exists_exp_log_inverse K v).choose_spec
  let e₀ : ℕ := (exists_log_mul K v).choose
  have he₀ : ∀ t ≥ e₀, ∀ x y : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
      y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
      logValue K v ((x : v.adicCompletion K) + y + x * y) =
        logValue K v (x : v.adicCompletion K) + logValue K v (y : v.adicCompletion K) :=
    (exists_log_mul K v).choose_spec
  let f₀ : ℕ := (exists_exp_summable K v).choose
  have hf₀ : ∀ t ≥ f₀, ∀ x : v.adicCompletionIntegers K,
      x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t →
      Summable (expTerm K v (x : v.adicCompletion K)) :=
    (exists_exp_summable K v).choose_spec
  refine ⟨1 + a + b + c + d + e₀ + f₀, ?_⟩
  intro t ht
  have htpos : 0 < t := by omega
  have hat : a ≤ t := by omega
  have hbt : b ≤ t := by omega
  have hct : c ≤ t := by omega
  have hdt : d ≤ t := by omega
  have het : e₀ ≤ t := by omega
  have hft : f₀ ≤ t := by omega
  let I : Ideal (v.adicCompletionIntegers K) :=
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t
  let U : Subgroup (v.adicCompletionIntegers K)ˣ := localUnitFiltration K v t
  have hsmall : ∀ z : v.adicCompletionIntegers K, z ∈ I →
      z ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    intro z hz
    exact Ideal.pow_le_self (Nat.ne_of_gt htpos) hz
  have hdiff (u : U) : (u : (v.adicCompletionIntegers K)ˣ).val - 1 ∈ I :=
    (mem_localUnitFiltration_iff K v t (u : (v.adicCompletionIntegers K)ˣ)).mp u.property
  have hchooseL : ∀ u : U, ∃ y : I,
      ((y : v.adicCompletionIntegers K) : v.adicCompletion K) =
        logValue K v (((u : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) - 1) := by
    intro u
    obtain ⟨y, hy, hyval⟩ :=
      ha t hat ((u : (v.adicCompletionIntegers K)ˣ).val - 1) (hdiff u)
    exact ⟨⟨y, hy⟩, by simpa using hyval⟩
  choose L hL using hchooseL
  have hchooseE : ∀ y : I, ∃ u : U,
      ((u : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) =
        expValue K v ((y : v.adicCompletionIntegers K) : v.adicCompletion K) := by
    intro y
    obtain ⟨z, hz, hzval⟩ := hb t hbt (y : v.adicCompletionIntegers K) y.property
    have hzunit := isUnit_one_add_of_mem_maximalIdeal z (hsmall z hz)
    let u : (v.adicCompletionIntegers K)ˣ := hzunit.unit
    have hu : (u : v.adicCompletionIntegers K) = 1 + z := hzunit.unit_spec
    have humem : u ∈ U := by
      apply (mem_localUnitFiltration_iff K v t u).mpr
      simpa [hu] using hz
    refine ⟨⟨u, humem⟩, ?_⟩
    change ((u : v.adicCompletionIntegers K) : v.adicCompletion K) =
      expValue K v ((y : v.adicCompletionIntegers K) : v.adicCompletion K)
    rw [hu]
    change 1 + (z : v.adicCompletion K) =
      expValue K v ((y : v.adicCompletionIntegers K) : v.adicCompletion K)
    rw [hzval]
    ring
  choose E hE using hchooseE
  have hIext (y z : I)
      (h : ((y : v.adicCompletionIntegers K) : v.adicCompletion K) =
        ((z : v.adicCompletionIntegers K) : v.adicCompletion K)) : y = z :=
    Subtype.ext (Subtype.ext h)
  have hUext (u w : U)
      (h : ((u : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) =
        ((w : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K)) : u = w := by
    apply Subtype.ext
    apply Units.ext
    exact Subtype.ext h
  have hleft (u : U) : E (L u) = u := by
    apply hUext
    rw [hE, hL]
    simpa using hd t hdt ((u : (v.adicCompletionIntegers K)ˣ).val - 1) (hdiff u)
  have hright (y : I) : L (E y) = y := by
    apply hIext
    rw [hL, hE]
    exact hc t hct (y : v.adicCompletionIntegers K) y.property
  have hadd (u w : U) : L (u * w) = L u + L w := by
    apply hIext
    change ((L (u * w) : v.adicCompletionIntegers K) : v.adicCompletion K) =
      ((L u : v.adicCompletionIntegers K) : v.adicCompletion K) +
        ((L w : v.adicCompletionIntegers K) : v.adicCompletion K)
    rw [hL, hL, hL]
    have hprod : (((u * w : U) : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) - 1 =
        (((u : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) - 1) +
          (((w : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) - 1) +
          (((u : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) - 1) *
            (((w : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) - 1) := by
      change (((u : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) *
        ((w : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K)) - 1 = _
      ring
    rw [hprod]
    simpa using he₀ t het ((u : (v.adicCompletionIntegers K)ˣ).val - 1)
      ((w : (v.adicCompletionIntegers K)ˣ).val - 1) (hdiff u) (hdiff w)
  let e : U ≃* Multiplicative I :=
    { toFun := fun u ↦ Multiplicative.ofAdd (L u)
      invFun := fun y ↦ E (Multiplicative.toAdd y)
      left_inv := by intro u; exact hleft u
      right_inv := by
        intro y
        apply Multiplicative.toAdd.injective
        change L (E (Multiplicative.toAdd y)) = Multiplicative.toAdd y
        exact hright _
      map_mul' := by
        intro u w
        change Multiplicative.ofAdd (L (u * w)) = Multiplicative.ofAdd (L u + L w)
        exact congrArg Multiplicative.ofAdd (hadd u w) }
  refine ⟨e, ?_, ?_⟩
  · intro u
    change HasSum (logTerm K v (((u : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) - 1))
      ((L u : v.adicCompletionIntegers K) : v.adicCompletion K)
    rw [hL]
    simpa [logValue] using
      (log_summable K v ((u : (v.adicCompletionIntegers K)ˣ).val - 1)
        (hsmall _ (hdiff u))).hasSum
  · intro y
    change HasSum (expTerm K v ((Multiplicative.toAdd y).val : v.adicCompletion K))
      ((E (Multiplicative.toAdd y) : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K)
    rw [hE]
    exact (hf₀ t hft (Multiplicative.toAdd y).val (Multiplicative.toAdd y).property).hasSum

/-- A continuous field automorphism commutes with the convergent rational logarithm
series, which supplies the equivariance needed in V.3.9. -/
theorem log_equivariant (σ : v.adicCompletion K ≃+* v.adicCompletion K)
    (hσ : Continuous σ) (x y : v.adicCompletion K) (h : HasSum (logTerm K v x) y) :
    HasSum (logTerm K v (σ x)) (σ y) := by
  exact Cox.ClassFieldConvergentSeries.hasSum_logSeries_map σ.toRingHom hσ x y h

/-- Janusz V.3.6: dividing the logarithm by n and exponentiating gives deep nth roots. -/
theorem deep_units_are_powers (n : ℕ) (hn : 0 < n) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, localUnitFiltration K v t ≤
      (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →*
        (v.adicCompletionIntegers K)ˣ).range := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_logIso K v
  let s := s₀ + 1
  obtain ⟨e, helog, heexp⟩ := hs₀ s (by dsimp [s]; omega)
  obtain ⟨a, ha⟩ := exists_div_mem_deep_ideal K v (n : v.adicCompletion K) s
  obtain ⟨b, hb⟩ := exists_log_preserves_filtration K v
  refine ⟨s + a + b, ?_⟩
  intro t ht u hu
  have hst : s ≤ t := by omega
  have hat : a ≤ t := by omega
  have hbt : b ≤ t := by omega
  have htpos : 0 < t := by dsimp [s] at hst; omega
  let x : v.adicCompletionIntegers K := (u : v.adicCompletionIntegers K) - 1
  have hx : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t :=
    (mem_localUnitFiltration_iff K v t u).mp hu
  obtain ⟨y, hy, hyval⟩ := hb t hbt x hx
  obtain ⟨z, hz, hzval⟩ := ha t hat y hy
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hn0 : (n : v.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hnz : (n : v.adicCompletion K) * (z : v.adicCompletion K) = (y : v.adicCompletion K) := by
    simp [hzval, div_eq_mul_inv, hn0, mul_left_comm]
  let us : localUnitFiltration K v s :=
    ⟨u, localUnitFiltration_antitone K v hst hu⟩
  have hysum : HasSum (logTerm K v (x : v.adicCompletion K)) (y : v.adicCompletion K) := by
    rw [hyval]
    exact (log_summable K v x (Ideal.pow_le_self (Nat.ne_of_gt htpos) hx)).hasSum
  have heus :
      ((Multiplicative.toAdd (e us)).val : v.adicCompletion K) = (y : v.adicCompletion K) := by
    have huSum := helog us
    change HasSum (logTerm K v (x : v.adicCompletion K)) _ at huSum
    exact huSum.unique hysum
  let w : localUnitFiltration K v s := e.symm (Multiplicative.ofAdd ⟨z, hz⟩)
  have hwcoord : ((Multiplicative.toAdd (e (w ^ n))).val : v.adicCompletion K) =
      (n : v.adicCompletion K) * (z : v.adicCompletion K) := by
    simp [w, map_pow, nsmul_eq_mul]
  have hwu : w ^ n = us := by
    apply e.injective
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hwcoord.trans (hnz.trans heus.symm)
  refine ⟨(w : (v.adicCompletionIntegers K)ˣ), ?_⟩
  simpa using congrArg
    (fun q : localUnitFiltration K v s ↦ (q : (v.adicCompletionIntegers K)ˣ)) hwu

end Cox.ClassFieldTheory.LocalCyclic
