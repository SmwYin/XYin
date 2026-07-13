import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import XYin.PhD.IntegralPowerSeries.IntegralPowerSeries
import XYin.PhD.Modularforms.Eisenstein

set_option linter.style.header false

open Complex
open ModularForm hiding E₄ E₆
open ModularFormClass ArithmeticFunction UpperHalfPlane IntegralPowerSeries

noncomputable section

abbrev E4 := _root_.E₄
abbrev E6 := _root_.E₆

private lemma E4_qExpansion_coeff_aux (n : ℕ) :
    (qExpansion 1 E4).coeff n =
      if n = 0 then 1 else (240 : ℂ) * sigma 3 n := by
  have hE4 : (E4 : ℍ → ℂ) = (ModularForm.E₄ : ℍ → ℂ) := by rfl
  rw [hE4, EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) ⟨2, rfl⟩ n]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false]
    norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_four]

private lemma E6_qExpansion_coeff_aux (n : ℕ) :
    (qExpansion 1 E6).coeff n =
      if n = 0 then 1 else -(504 : ℂ) * sigma 5 n := by
  have hE6 : (E6 : ℍ → ℂ) = (ModularForm.E₆ : ℍ → ℂ) := by rfl
  rw [hE6, EisensteinSeries.E_qExpansion_coeff (k := 6) (by norm_num) ⟨3, rfl⟩ n]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false]
    norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_six]

lemma E4IsIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 E4) := by
  rw [int_iff]
  intro n
  rw [E4_qExpansion_coeff_aux]
  by_cases hn : n = 0
  · exact ⟨1, by simp [hn]⟩
  · refine ⟨(240 : ℤ) * sigma 3 n, ?_⟩
    simp [hn]

lemma E6IsIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 E6) := by
  rw [int_iff]
  intro n
  rw [E6_qExpansion_coeff_aux]
  by_cases hn : n = 0
  · exact ⟨1, by simp [hn]⟩
  · refine ⟨(-504 : ℤ) * sigma 5 n, ?_⟩
    simp [hn]

def integralE4 : PowerSeries ℤ := toIntegralPowerSeries E4IsIntegralPowerSeries

def integralE6 : PowerSeries ℤ := toIntegralPowerSeries E6IsIntegralPowerSeries

lemma E4CubedIsIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3)) := by
  have hq : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := by simp) E4 3
  rw [hq]
  exact IntegralPowerSeriesSubring.pow_mem E4IsIntegralPowerSeries 3

lemma Delta_exp_zero : (qExpansion 1 Delta).coeff 0 = 0 := by
  simpa [qExpansion_coeff] using
    (CuspFormClass.cuspFunction_apply_zero Delta (by norm_num) (by simp))

lemma mod3 (d : ℕ) : 3 ∣ (5 * d ^ 3 + 7 * d ^ 5) := by
  rw [← Int.natCast_dvd_natCast]
  have h : ∀ x : ZMod 3, (5 * x ^ 3 + 7 * x ^ 5 : ZMod 3) = 0 := by decide
  have h2 : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 3) = 0 := by exact_mod_cast h d
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2

lemma mod4 (d : ℕ) : 4 ∣ (5 * d ^ 3 + 7 * d ^ 5) := by
  rw [← Int.natCast_dvd_natCast]
  have h : ∀ x : ZMod 4, (5 * x ^ 3 + 7 * x ^ 5 : ZMod 4) = 0 := by decide
  have h2 : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 4) = 0 := by exact_mod_cast h d
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2

lemma mod12 (d : ℕ) : 12 ∣ (5 * d ^ 3 + 7 * d ^ 5) := by
  have h : Nat.Coprime 3 4 := by decide
  simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd h (mod3 d) (mod4 d)

lemma sigmamod12 (n : ℕ) : 12 ∣ 5 * sigma 3 n + 7 * sigma 5 n := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  have hsum : 12 ∣ Finset.sum n.divisors (fun d => 5 * d ^ 3 + 7 * d ^ 5) := by
    refine Finset.dvd_sum ?_
    intro d hd
    exact mod12 d
  simpa [Finset.mul_sum, Finset.sum_add_distrib, left_distrib, right_distrib, add_assoc, add_comm,
    add_left_comm] using hsum

lemma E4coeffmod240 (n : ℕ) (hn : n ≥ 1) : 240 ∣ integralE4.coeff n := by
  have h := congrArg (PowerSeries.coeff n)
    (coeTo_of_toIntegralPowerSeries E4IsIntegralPowerSeries)
  change ((integralE4.coeff n : ℤ) : ℂ) = (qExpansion 1 E4).coeff n at h
  rw [E4_qExpansion_coeff_aux, if_neg (by omega)] at h
  have hcoeff' : integralE4.coeff n = (240 : ℤ) * sigma 3 n := by
    exact_mod_cast h
  exact ⟨sigma 3 n, hcoeff'⟩

lemma E6coeffmod504 (n : ℕ) (hn : n ≥ 1) : 504 ∣ integralE6.coeff n := by
  have h := congrArg (PowerSeries.coeff n)
    (coeTo_of_toIntegralPowerSeries E6IsIntegralPowerSeries)
  change ((integralE6.coeff n : ℤ) : ℂ) = (qExpansion 1 E6).coeff n at h
  rw [E6_qExpansion_coeff_aux, if_neg (by omega)] at h
  have hcoeff' : integralE6.coeff n = -((504 : ℤ) * sigma 5 n) := by
    exact_mod_cast h
  refine ⟨-(sigma 5 n : ℤ), ?_⟩
  calc
  _ = -((504 : ℤ) * sigma 5 n) := hcoeff'
  _ = _ := by ring

lemma integralE4_coeff_zero : integralE4.coeff 0 = 1 := by
  have h := congrArg (PowerSeries.coeff 0)
    (coeTo_of_toIntegralPowerSeries E4IsIntegralPowerSeries)
  change ((integralE4.coeff 0 : ℤ) : ℂ) = (qExpansion 1 E4).coeff 0 at h
  rw [E4_qExpansion_coeff_aux] at h
  exact_mod_cast h

lemma integralE6_coeff_zero : integralE6.coeff 0 = 1 := by
  have h := congrArg (PowerSeries.coeff 0)
    (coeTo_of_toIntegralPowerSeries E6IsIntegralPowerSeries)
  change ((integralE6.coeff 0 : ℤ) : ℂ) = (qExpansion 1 E6).coeff 0 at h
  rw [E6_qExpansion_coeff_aux] at h
  exact_mod_cast h

lemma integralE4_constantCoeff : PowerSeries.constantCoeff integralE4 = 1 := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using integralE4_coeff_zero

lemma integralE6_constantCoeff : PowerSeries.constantCoeff integralE6 = 1 := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using integralE6_coeff_zero

lemma integralE4_coeff_pos (n : ℕ) (hn : n ≥ 1) : integralE4.coeff n = (240 : ℤ) * sigma 3 n := by
  have h := congrArg (PowerSeries.coeff n)
    (coeTo_of_toIntegralPowerSeries E4IsIntegralPowerSeries)
  change ((integralE4.coeff n : ℤ) : ℂ) = (qExpansion 1 E4).coeff n at h
  rw [E4_qExpansion_coeff_aux, if_neg (by omega)] at h
  exact_mod_cast h

lemma integralE6_coeff_pos (n : ℕ) (hn : n ≥ 1) :
    integralE6.coeff n = -((504 : ℤ) * sigma 5 n) := by
  have h := congrArg (PowerSeries.coeff n)
    (coeTo_of_toIntegralPowerSeries E6IsIntegralPowerSeries)
  change ((integralE6.coeff n : ℤ) : ℂ) = (qExpansion 1 E6).coeff n at h
  rw [E6_qExpansion_coeff_aux, if_neg (by omega)] at h
  exact_mod_cast h

def E4bar : PowerSeries ℤ := integralE4 - 1

def E6bar : PowerSeries ℤ := integralE6 - 1

lemma E4bar_coeff_mod (m : ℕ) : 240 ∣ E4bar.coeff m := by
  by_cases hm0 : m = 0
  · subst hm0
    have h0 : E4bar.coeff 0 = 0 := by simp [E4bar, integralE4_constantCoeff]
    rw [h0]
    exact dvd_zero 240
  · have hm1 : m ≥ 1 := by omega
    simpa [E4bar, hm0] using E4coeffmod240 m hm1

lemma E6bar_coeff_mod (m : ℕ) : 504 ∣ E6bar.coeff m := by
  by_cases hm0 : m = 0
  · subst hm0
    have h0 : E6bar.coeff 0 = 0 := by simp [E6bar, integralE6_constantCoeff]
    rw [h0]
    exact dvd_zero 504
  · have hm1 : m ≥ 1 := by omega
    simpa [E6bar, hm0] using E6coeffmod504 m hm1

lemma coeff_mul_mod (a b : ℤ) (f g : PowerSeries ℤ)
    (hf : ∀ m, a ∣ f.coeff m) (hg : ∀ m, b ∣ g.coeff m) :
    ∀ m, a * b ∣ (f * g).coeff m := by
  intro m
  rw [PowerSeries.coeff_mul]
  refine Finset.dvd_sum ?_
  intro p hp
  rcases hf p.1 with ⟨u, hu⟩
  rcases hg p.2 with ⟨v, hv⟩
  refine ⟨u * v, ?_⟩
  calc
  _ = (a * u) * (b * v) := by simp [hu, hv]
  _ = _ := by ring

lemma mod144_remainder_dvd (n : ℕ) : (1728 : ℤ) ∣
    (E4bar ^ 3 + 3 * E4bar ^ 2 - E6bar ^ 2).coeff n := by
  have hA2div : ∀ m, (240 : ℤ) * 240 ∣ (E4bar ^ 2).coeff m := by
    intro m
    simpa [pow_two] using coeff_mul_mod 240 240 E4bar E4bar E4bar_coeff_mod E4bar_coeff_mod m
  have hA3div : ∀ m, (240 : ℤ) * 240 * 240 ∣ (E4bar ^ 3).coeff m := by
    intro m
    have hAA : ∀ k, (240 : ℤ) * 240 ∣ (E4bar ^ 2).coeff k := hA2div
    simpa [pow_succ, pow_two, mul_assoc] using
      coeff_mul_mod ((240 : ℤ) * 240) 240 (E4bar ^ 2) E4bar hAA E4bar_coeff_mod m
  have hB2div : ∀ m, (504 : ℤ) * 504 ∣ (E6bar ^ 2).coeff m := by
    intro m
    simpa [pow_two] using coeff_mul_mod 504 504 E6bar E6bar E6bar_coeff_mod E6bar_coeff_mod m
  have h1 : (1728 : ℤ) ∣ (E4bar ^ 3).coeff n := by
    exact dvd_trans (by norm_num : (1728 : ℤ) ∣ (240 : ℤ) * 240 * 240) (hA3div n)
  have h2a : (1728 : ℤ) ∣ 3 * (E4bar ^ 2).coeff n := by
    have hmult : (1728 : ℤ) ∣ (3 : ℤ) * ((240 : ℤ) * 240) := by norm_num
    have hstep : (3 : ℤ) * ((240 : ℤ) * 240) ∣ 3 * (E4bar ^ 2).coeff n := by
      simpa [mul_assoc] using Int.mul_dvd_mul_left 3 (hA2div n)
    exact dvd_trans hmult hstep
  have h2 : (1728 : ℤ) ∣ (3 * E4bar ^ 2).coeff n := by
    have hcoef : (3 * E4bar ^ 2).coeff n = 3 * (E4bar ^ 2).coeff n := by
      simpa using (PowerSeries.coeff_C_mul n (E4bar ^ 2) (3 : ℤ))
    exact hcoef ▸ h2a
  have h3 : (1728 : ℤ) ∣ (E6bar ^ 2).coeff n := by
    exact dvd_trans (by norm_num : (1728 : ℤ) ∣ (504 : ℤ) * 504) (hB2div n)
  have h13 : (1728 : ℤ) ∣ (E4bar ^ 3 + 3 * E4bar ^ 2).coeff n := by
    simpa using Int.dvd_add h1 h2
  simpa using Int.dvd_sub h13 h3

lemma mod144_bridge (n : ℕ) : Int.ModEq 1728
    ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) ((3 * E4bar - 2 * E6bar).coeff n) := by
  rw [Int.modEq_iff_dvd]
  have hid : integralE4 ^ 3 - integralE6 ^ 2 - (3 * E4bar - 2 * E6bar) =
      E4bar ^ 3 + 3 * E4bar ^ 2 - E6bar ^ 2 := by
    have hEA : integralE4 = E4bar + 1 := by simp [E4bar]
    have hEB : integralE6 = E6bar + 1 := by simp [E6bar]
    calc
    _ = (E4bar + 1) ^ 3 - (E6bar + 1) ^ 2 - (3 * E4bar - 2 * E6bar) := by simp [hEA, hEB]
    _ = _ := by ring
  have hcoeff : ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) - ((3 * E4bar - 2 * E6bar).coeff n) =
      (E4bar ^ 3 + 3 * E4bar ^ 2 - E6bar ^ 2).coeff n := by
    simpa using congrArg (PowerSeries.coeff n) hid
  let x : ℤ := (integralE4 ^ 3 - integralE6 ^ 2).coeff n
  let y : ℤ := (3 * E4bar - 2 * E6bar).coeff n
  let z : ℤ := (E4bar ^ 3 + 3 * E4bar ^ 2 - E6bar ^ 2).coeff n
  have hxyz : x - y = z := by simpa [x, y, z] using hcoeff
  have hyx : y - x = -z := by linarith
  have hneg : (1728 : ℤ) ∣ -z := Int.dvd_neg.mpr (by simpa [z] using mod144_remainder_dvd n)
  simpa [x, y, z] using (hyx ▸ hneg)

lemma mod144_linear (n : ℕ) (hn0 : n ≠ 0) :
    ((3 * E4bar - 2 * E6bar).coeff n) = 144 * (5 * sigma 3 n + 7 * sigma 5 n) := by
  have hn1 : n ≥ 1 := by omega
  have hAcoeff : E4bar.coeff n = integralE4.coeff n := by simp [E4bar, hn0]
  have hBcoeff : E6bar.coeff n = integralE6.coeff n := by simp [E6bar, hn0]
  have h3A : (3 * E4bar).coeff n = 3 * E4bar.coeff n := by
    simpa using (PowerSeries.coeff_C_mul n E4bar (3 : ℤ))
  have h2B : (2 * E6bar).coeff n = 2 * E6bar.coeff n := by
    simpa using (PowerSeries.coeff_C_mul n E6bar (2 : ℤ))
  calc
  _ = (3 * E4bar).coeff n - (2 * E6bar).coeff n := by simp
  _ = 3 * E4bar.coeff n - 2 * E6bar.coeff n := by simp [h3A, h2B]
  _ = 3 * integralE4.coeff n - 2 * integralE6.coeff n := by simp [hAcoeff, hBcoeff]
  _ = 3 * ((240 : ℤ) * sigma 3 n) - 2 * (-((504 : ℤ) * sigma 5 n)) := by
    simp [integralE4_coeff_pos n hn1, integralE6_coeff_pos n hn1]
  _ = _ := by ring

lemma mod144 (n : ℕ) : Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n)
    (144 * (5 * sigma 3 n + 7 * sigma 5 n)) := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [Int.ModEq]
    simp [integralE4_constantCoeff, integralE6_constantCoeff]
  · simpa [mod144_linear n hn0] using mod144_bridge n

lemma mod1728 (n : ℕ) : 1728 ∣ (integralE4 ^ 3 - integralE6 ^ 2).coeff n := by
  have hmod : Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n)
      (144 * (5 * sigma 3 n + 7 * sigma 5 n)) := mod144 n
  have h12 : (12 : ℤ) ∣ (5 * sigma 3 n + 7 * sigma 5 n : ℤ) := by exact_mod_cast (sigmamod12 n)
  have h1728 : (1728 : ℤ) ∣ (144 * (5 * sigma 3 n + 7 * sigma 5 n) : ℤ) := by
    rcases h12 with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
    _ = 144 * (12 * t) := by simp [ht]
    _ = _ := by ring
  have hmod0 : Int.ModEq 1728 (144 * (5 * sigma 3 n + 7 * sigma 5 n)) 0 :=
    (Int.modEq_zero_iff_dvd).2 h1728
  have hfinal : Int.ModEq 1728 ((integralE4 ^ 3 - integralE6 ^ 2).coeff n) 0 := hmod.trans hmod0
  exact (Int.modEq_zero_iff_dvd).1 hfinal

lemma aux1 : (coeToComplexPowerSeries.ringHom ℤ) (integralE4 ^ 3 - integralE6 ^ 2)
    = qExpansion 1 (E4 ^ 3 - E6 ^ 2) := by
  have hE4 := coeTo_of_toIntegralPowerSeries E4IsIntegralPowerSeries
  have hE6 := coeTo_of_toIntegralPowerSeries E6IsIntegralPowerSeries
  have hpow4 : qExpansion 1 (E4 ^ 3) = (qExpansion 1 E4) ^ 3 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (4 : ℤ)) (hh := by norm_num) (hΓ := by simp) E4 3
  have hpow6 : qExpansion 1 (E6 ^ 2) = (qExpansion 1 E6) ^ 2 := by
    simpa [DirectSum.ofPow] using qExpansion_of_pow (Γ := CongruenceSubgroup.Gamma 1) (h := (1 : ℝ))
      (k := (6 : ℤ)) (hh := by norm_num) (hΓ := by simp) E6 2
  calc
  _ = (coeToComplexPowerSeries.ringHom ℤ) (integralE4 ^ 3)
      - (coeToComplexPowerSeries.ringHom ℤ) (integralE6 ^ 2) := by
    simp [map_sub]
  _ = ((coeToComplexPowerSeries.ringHom ℤ) integralE4) ^ 3
      - ((coeToComplexPowerSeries.ringHom ℤ) integralE6) ^ 2 := by simp [map_pow]
  _ = (qExpansion 1 E4) ^ 3 - (qExpansion 1 E6) ^ 2 := by
    rw [integralE4, integralE6, hE4, hE6]
  _ = qExpansion 1 (E4 ^ 3) - qExpansion 1 (E6 ^ 2) := by rw [← hpow4, ← hpow6]
  _ = qExpansion 1 (E4.mul (E4.mul E4)) - qExpansion 1 (E6.mul E6) := by
    have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
    have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
    simp [pow_three, pow_two, hf, hg]
  _ = qExpansion 1 ((E4.mul (E4.mul E4)) - (E6.mul E6)) := by
    rw [ModularForm.qExpansion_sub (hh := by norm_num)
      (hΓ := by simp)]
  _ = _ := by
    have hf : (⇑E4 * (⇑E4 * ⇑E4)) = ⇑(E4.mul (E4.mul E4)) := by rfl
    have hg : (⇑E6 * ⇑E6) = ⇑(E6.mul E6) := by rfl
    simp [pow_three, pow_two, hf, hg]

lemma E4E6IsIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 (E4 ^ 3 - E6 ^ 2)) := by
  rw [IsIntegralPowerSeries]
  exact ⟨integralE4 ^ 3 - integralE6 ^ 2, aux1⟩

lemma aux1' :
    toIntegralPowerSeries E4E6IsIntegralPowerSeries = integralE4 ^ 3 - integralE6 ^ 2 := by
  apply (PowerSeries.map_injective (algebraMap ℤ ℂ) Int.cast_injective)
  change (coeToComplexPowerSeries.ringHom ℤ) (toIntegralPowerSeries E4E6IsIntegralPowerSeries)
    = (coeToComplexPowerSeries.ringHom ℤ) (integralE4 ^ 3 - integralE6 ^ 2)
  rw [coeTo_of_toIntegralPowerSeries]
  exact aux1.symm

lemma mod1728' (n : ℕ) :
    Int.ModEq 1728 ((toIntegralPowerSeries E4E6IsIntegralPowerSeries).coeff n) 0 := by
  rw [aux1']
  exact (Int.modEq_zero_iff_dvd).2 (mod1728 n)

lemma Deltaaux : qExpansion 1 Delta = (1/1728 : ℂ) • qExpansion 1 (E4 ^ 3 - E6 ^ 2) := by
  let H : ModularForm (CongruenceSubgroup.Gamma 1) 12 :=
    ModularForm.mcast (by decide) (E4.pow 3) -
      ModularForm.mcast (by decide) (E6.pow 2)
  have hHfun : (⇑H : ℍ → ℂ) = (⇑E4 ^ 3 - ⇑E6 ^ 2) := by
    funext z
    simp only [H, ModularForm.coe_mcast, ModularForm.coe_pow, ModularForm.sub_apply,
      Pi.pow_apply, Pi.sub_apply]
  have hDeltaPointwise (z : ℍ) : Delta z = (E4 z ^ 3 - E6 z ^ 2) / 1728 := by
    rw [Delta_apply, Delta_eq_eta_pow]
    simpa [ModularForm.discriminant] using
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  have hDeltaFun : (⇑Delta : ℍ → ℂ) = (1 / 1728 : ℂ) • (⇑H : ℍ → ℂ) := by
    funext z
    change Delta z = (1 / 1728 : ℂ) * H z
    rw [hDeltaPointwise]
    have hHz : H z = E4 z ^ 3 - E6 z ^ 2 := congrFun hHfun z
    rw [hHz]
    ring
  have hHan : AnalyticAt ℂ (cuspFunction 1 (⇑H : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero H (by norm_num) (by simp)
  calc
    _ = qExpansion 1 ((1 / 1728 : ℂ) • (⇑H : ℍ → ℂ)) := by rw [hDeltaFun]
    _ = (1 / 1728 : ℂ) • qExpansion 1 (⇑H : ℍ → ℂ) :=
      UpperHalfPlane.qExpansion_smul hHan _
    _ = _ := by rw [hHfun]

lemma DeltaIsIntegralPowerSeries : IsIntegralPowerSeries (qExpansion 1 Delta) := by
  rw [Deltaaux]
  apply IsIntegralPowerSeriesmod
  · decide
  · intro n
    exact mod1728' n

def IntegralDelta : PowerSeries ℤ := toIntegralPowerSeries DeltaIsIntegralPowerSeries

def Ramanujan_tau : ℕ → ℤ := fun n => IntegralDelta.coeff n

end
