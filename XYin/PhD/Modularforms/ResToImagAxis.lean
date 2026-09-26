/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
module

public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.NumberTheory.ModularForms.Identities
public import Mathlib.NumberTheory.ModularForms.QExpansion

public import XYin.PhD.Modularforms.AtImInfty

/-!
# Restriction to the positive imaginary axis

Reality, positivity, and polynomial decay of modular forms restricted to the imaginary axis.

## Main definitions

* `Function.resToImagAxis F`: the function `t ↦ F (I * t)` (and `0` for `t ≤ 0`).
* `ResToImagAxis.Real F`, `ResToImagAxis.Pos F`, `ResToImagAxis.EventuallyPos F`: `F` is real,
  real and positive, real and eventually positive on the imaginary axis.
-/

@[expose] public section

open UpperHalfPlane hiding I

open Real Complex Filter Asymptotics ModularGroup CongruenceSubgroup

open scoped Topology Manifold ModularForm MatrixGroups

namespace Function

/--
Restrict a function `F : ℍ → ℂ` to the positive imaginary axis, i.e. `t ↦ F (I * t)`.
If $t \le 0$, then `F (I * t)` is not defined, and we return `0` in that case.
-/
noncomputable def resToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  fun t ↦ if ht : 0 < t then F ⟨(I * t), by simp [ht]⟩ else 0

@[simp] lemma resToImagAxis_of_pos (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    F.resToImagAxis t = F ⟨I * t, by simp [ht]⟩ :=
  dif_pos ht

@[simp] lemma resToImagAxis_of_nonpos (F : ℍ → ℂ) {t : ℝ} (ht : t ≤ 0) :
    F.resToImagAxis t = 0 :=
  dif_neg ht.not_gt

@[simp] lemma resToImagAxis_add_apply (F G : ℍ → ℂ) (t : ℝ) :
    (F + G).resToImagAxis t = F.resToImagAxis t + G.resToImagAxis t := by
  by_cases ht : 0 < t <;> simp [resToImagAxis, ht]

@[simp] lemma resToImagAxis_mul_apply (F G : ℍ → ℂ) (t : ℝ) :
    (F * G).resToImagAxis t = F.resToImagAxis t * G.resToImagAxis t := by
  by_cases ht : 0 < t <;> simp [resToImagAxis, ht]

@[simp] lemma resToImagAxis_smul_apply (c : ℝ) (F : ℍ → ℂ) (t : ℝ) :
    (c • F).resToImagAxis t = c • F.resToImagAxis t := by
  by_cases ht : 0 < t <;> simp [resToImagAxis, ht]

end Function

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is real-valued,
i.e. imaginary part is zero.
-/
@[fun_prop]
noncomputable def ResToImagAxis.Real (F : ℍ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → (F.resToImagAxis t).im = 0

/--
Function $F : \mathbb{H} \to \mathbb{C}$ is real and positive on the imaginary axis.
-/
@[fun_prop]
noncomputable def ResToImagAxis.Pos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∀ t : ℝ, 0 < t → 0 < (F.resToImagAxis t).re

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is eventually
positive, i.e. there exists $t_0 > 0$ such that for all $t \ge t_0$, $F(it)$ is real and positive.
-/
@[fun_prop]
noncomputable def ResToImagAxis.EventuallyPos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, t₀ ≤ t → 0 < (F.resToImagAxis t).re

/-- The restriction of a holomorphic function to the imaginary axis is real-differentiable. -/
@[fun_prop]
theorem ResToImagAxis.Differentiable (F : ℍ → ℂ) (hF : MDiff F) (t : ℝ)
    (ht : 0 < t) : DifferentiableAt ℝ F.resToImagAxis t := by
  have hcdiff := hF ⟨Complex.I * t, by norm_num [Complex.I_re, ht]⟩
  rw [mdifferentiableAt_iff] at hcdiff
  have h_diff :
      DifferentiableAt ℝ (fun t : ℝ ↦ F (ofComplex (Complex.I * t))) t := by
    haveI : IsScalarTower ℝ ℂ ℂ := IsScalarTower.complexToReal
    convert hcdiff.restrictScalars ℝ |> DifferentiableAt.comp t <|
      DifferentiableAt.const_mul ofRealCLM.differentiableAt _ using 1
  apply h_diff.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with t ht
  rw [Function.resToImagAxis_of_pos _ ht, ofComplex_apply_of_im_pos]

/--
Restriction and slash action under S: $(F |_k S) (it) = i^{-k} t^{-k} F(i/t)$.
-/
theorem ResToImagAxis.SlashActionS (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    (F ∣[k] S).resToImagAxis t = (Complex.I) ^ (-k) * t ^ (-k) * F.resToImagAxis (1 / t) := by
  set z : ℍ := ⟨I * t, by simp [ht]⟩ with hzdef
  set z' : ℍ := ⟨I * (1 / t : ℝ), by simpa [one_div_pos.2 ht]⟩ with hz'def
  have h : mk (-z)⁻¹ z.im_inv_neg_coe_pos = z' :=
    UpperHalfPlane.ext (by simp [hzdef, hz'def, mul_comm])
  have hS : (F ∣[k] S) z = I ^ (-k) * t ^ (-k) * F z' := by
    rw [SlashInvariantForm.slash_S_apply, h]
    simp [hzdef, mul_zpow I (t : ℂ) (-k), mul_comm (F z')]
  simpa [ht, hz'def] using hS

/-! ## Closure properties

Realness, positivity and eventual positivity are closed under addition and multiplication. -/

/-- Real constants are real on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.const (c : ℝ) : ResToImagAxis.Real (fun _ ↦ c) := by
  intro t ht
  simp [ht]

@[fun_prop]
theorem ResToImagAxis.Real.zero : ResToImagAxis.Real (fun _ ↦ 0) := ResToImagAxis.Real.const 0

@[fun_prop]
theorem ResToImagAxis.Real.one : ResToImagAxis.Real (fun _ ↦ 1) := ResToImagAxis.Real.const 1

@[fun_prop]
theorem ResToImagAxis.Real.neg {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (-F) := by
  intro t ht
  simpa [ht] using congrArg Neg.neg (hF t ht)

@[fun_prop]
theorem ResToImagAxis.Real.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F + G) := by
  intro t ht
  simp only [Function.resToImagAxis_add_apply, Complex.add_im, hF t ht, hG t ht, add_zero]

@[fun_prop]
theorem ResToImagAxis.Real.sub {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F - G) := by
  simpa [sub_eq_add_neg] using ResToImagAxis.Real.add hF hG.neg

@[fun_prop]
theorem ResToImagAxis.Real.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F * G) := by
  intro t ht
  simp only [Function.resToImagAxis_mul_apply, Complex.mul_im, hF t ht, hG t ht,
    mul_zero, zero_mul, add_zero]

@[fun_prop]
theorem ResToImagAxis.Real.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (c • F) := by
  intro t ht
  simp only [Function.resToImagAxis_smul_apply, Complex.smul_im, hF t ht, smul_zero]

@[fun_prop]
theorem ResToImagAxis.Real.pow {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) (n : ℕ) :
    ResToImagAxis.Real (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.Real.one
  | succ n hn => exact hn.mul hF

@[fun_prop]
theorem ResToImagAxis.Pos.const (c : ℝ) (hc : 0 < c) : ResToImagAxis.Pos (fun _ ↦ c) :=
  ⟨ResToImagAxis.Real.const c, fun t ht ↦ by simp [ht, hc]⟩

@[fun_prop]
theorem ResToImagAxis.Pos.one : ResToImagAxis.Pos (fun _ ↦ 1) :=
  ResToImagAxis.Pos.const 1 one_pos

@[fun_prop]
theorem ResToImagAxis.Pos.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F + G) := by
  refine ⟨hF.1.add hG.1, fun t ht ↦ ?_⟩
  simpa only [Function.resToImagAxis_add_apply, Complex.add_re] using
    add_pos (hF.2 t ht) (hG.2 t ht)

@[fun_prop]
theorem ResToImagAxis.Pos.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F * G) := by
  refine ⟨hF.1.mul hG.1, fun t ht ↦ ?_⟩
  simpa only [Function.resToImagAxis_mul_apply, Complex.mul_re, hF.1 t ht, hG.1 t ht,
    mul_zero, sub_zero] using mul_pos (hF.2 t ht) (hG.2 t ht)

@[fun_prop]
theorem ResToImagAxis.Pos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Pos F)
    (hc : 0 < c) : ResToImagAxis.Pos (c • F) := by
  refine ⟨hF.1.smul, fun t ht ↦ ?_⟩
  simpa only [Function.resToImagAxis_smul_apply, Complex.smul_re, smul_eq_mul] using
    mul_pos hc (hF.2 t ht)

@[fun_prop]
theorem ResToImagAxis.Pos.pow {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F) (n : ℕ) :
    ResToImagAxis.Pos (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.Pos.one
  | succ n hn => exact hn.mul hF

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.from_pos {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F) :
    ResToImagAxis.EventuallyPos F :=
  ⟨hF.1, 1, one_pos, fun t ht ↦ hF.2 t (one_pos.trans_le ht)⟩

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.one :
    ResToImagAxis.EventuallyPos (fun _ ↦ 1) :=
  ResToImagAxis.EventuallyPos.from_pos ResToImagAxis.Pos.one

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.const (c : ℝ) (hc : 0 < c) :
    ResToImagAxis.EventuallyPos (fun _ ↦ c) :=
  ResToImagAxis.EventuallyPos.from_pos (ResToImagAxis.Pos.const c hc)

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.add {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F + G) := by
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  refine ⟨hF.1.add hG.1, max tF tG, hF0.trans_le (le_max_left _ _), fun t ht ↦ ?_⟩
  simpa only [Function.resToImagAxis_add_apply, Complex.add_re] using
    add_pos (hFpos t ((le_max_left _ _).trans ht)) (hGpos t ((le_max_right _ _).trans ht))

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.mul {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F * G) := by
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  refine ⟨hF.1.mul hG.1, max tF tG, hF0.trans_le (le_max_left _ _), fun t ht ↦ ?_⟩
  have htF := (le_max_left tF tG).trans ht
  have htG := (le_max_right tF tG).trans ht
  have ht0 := hF0.trans_le htF
  simpa only [Function.resToImagAxis_mul_apply, Complex.mul_re, hF.1 t ht0, hG.1 t ht0,
    mul_zero, sub_zero] using mul_pos (hFpos t htF) (hGpos t htG)

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.pow {F : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (n : ℕ) :
    ResToImagAxis.EventuallyPos (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.EventuallyPos.one
  | succ n hn => exact hn.mul hF

@[fun_prop]
theorem ResToImagAxis.EventuallyPos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.EventuallyPos F)
    (hc : 0 < c) : ResToImagAxis.EventuallyPos (c • F) := by
  obtain ⟨t₀, ht₀, hpos⟩ := hF.2
  refine ⟨hF.1.smul, t₀, ht₀, fun t ht ↦ ?_⟩
  simpa only [Function.resToImagAxis_smul_apply, Complex.smul_re, smul_eq_mul] using
    mul_pos hc (hpos t ht)

/-- If `F` is real-valued, then `F` is equal to the real part of itself on imaginary axis. -/
theorem ResToImagAxis.Real.eq_real_part {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) (t : ℝ) :
    F.resToImagAxis t = (F.resToImagAxis t).re := by
  rcases lt_or_ge 0 t with ht | ht
  · exact Complex.ext rfl (by simpa using hF t ht)
  · simp [ht]

/-! ## Reality of series and products -/

/-- The real embedding commutes with infinite products (no multipliability assumption). -/
lemma Complex.ofReal_tprod {ι : Type*} (f : ι → ℝ) : ((∏' i, f i : ℝ) : ℂ) = ∏' i, (f i : ℂ) :=
  Function.LeftInverse.map_tprod (g := Complex.ofRealHom) f continuous_ofReal continuous_re
    ofReal_re

/-- A series of complex numbers with real terms has a real sum. -/
lemma Complex.im_tsum_eq_zero_of_im_eq_zero {ι : Type*} (f : ι → ℂ) (h : ∀ i, (f i).im = 0) :
    (∑' i, f i).im = 0 := by
  rw [tsum_congr fun i ↦ (Complex.ext (by simp) (by simp [h]) : f i = ((f i).re : ℂ)),
    ← Complex.ofReal_tsum, ofReal_im]

/-- A product of complex numbers with real factors is real. -/
lemma Complex.im_tprod_eq_zero_of_im_eq_zero {ι : Type*} (f : ι → ℂ) (h : ∀ i, (f i).im = 0) :
    (∏' i, f i).im = 0 := by
  rw [tprod_congr fun i ↦ (Complex.ext (by simp) (by simp [h]) : f i = ((f i).re : ℂ)),
    ← Complex.ofReal_tprod, ofReal_im]

/-- On the imaginary axis the `q`-parameter is real: `e^{2πi · it} = e^{-2πt}`. -/
lemma cexp_two_pi_I_mul_I_mul (t : ℝ) :
    cexp (2 * π * Complex.I * (Complex.I * t)) = Real.exp (-2 * π * t) := by
  rw [ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring

/-!
## Polynomial decay of functions with exponential bounds

This section establishes that if a function `F : ℍ → ℂ` is `O(exp(-c * im τ))` at infinity,
then `t^s * F(it) → 0` as `t → ∞` for any real power `s`.

One application is to cusp forms, which satisfy such exponential decay bounds.
-/

/-- The positive imaginary axis `t ↦ it` tends to `i∞` as `t → ∞`. -/
lemma tendsto_ofComplex_I_mul_atTop :
    Tendsto (fun t : ℝ ↦ ofComplex (I * t)) atTop atImInfty := by
  apply tendsto_comap_im_ofComplex.comp
  simpa [tendsto_comap_iff, Function.comp_def] using
    (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop)

/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty`, then the restriction to the imaginary axis
`t ↦ F(it)` is `O(exp(-c * t))` at `atTop`.
-/
lemma isBigO_resToImagAxis_of_isBigO_atImInfty {F : ℍ → ℂ} {c : ℝ}
    (hF : F =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) :
    F.resToImagAxis =O[atTop] fun t ↦ Real.exp (-c * t) := by
  refine (hF.comp_tendsto tendsto_ofComplex_I_mul_atTop).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht
    simp [ht, ofComplex_apply_of_im_pos]
  · filter_upwards [eventually_gt_atTop 0] with t ht
    simp [ofComplex_apply_of_im_pos, ht]

/--
The analytic kernel: if `g : ℝ → ℂ` is eventually bounded by `C * exp(-b * t)` for some
`b > 0`, then `t^s * g(t) → 0` as `t → ∞` for any real power `s`.

This follows from the fact that `t^s * exp(-b * t) → 0` (mathlib's
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`) combined with the big-O transfer lemma.
-/
lemma tendsto_rpow_mul_of_isBigO_exp {g : ℝ → ℂ} {s b : ℝ} (hb : 0 < b)
    (hg : g =O[atTop] fun t ↦ rexp (-b * t)) :
    Tendsto (fun t : ℝ ↦ (t : ℂ) ^ (s : ℂ) * g t) atTop (𝓝 0) := by
  refine ((isBigO_refl _ _).mul (Complex.isBigO_ofReal_right.mpr hg)).trans_tendsto ?_
  refine (tendsto_ofReal_iff.mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht)]

/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
`t^s * F(it) → 0` as `t → ∞` for any real power `s`.
-/
theorem tendsto_rpow_mul_resToImagAxis_of_isBigO_exp {F : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : F =O[atImInfty] fun τ ↦ rexp (-c * τ.im)) (s : ℝ) :
    Tendsto (fun t : ℝ ↦ (t : ℂ) ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0) :=
  tendsto_rpow_mul_of_isBigO_exp hc (isBigO_resToImagAxis_of_isBigO_atImInfty hF)

/--
For a cusp form `f` of level `Γ(n)`, we have `t^s * f(it) → 0` as `t → ∞` for any real power `s`.

This follows from the exponential decay of cusp forms at infinity: `f = O(exp(-2π τ.im / n))`.
-/
theorem cuspForm_rpow_mul_resToImagAxis_tendsto_zero {n : ℕ} {k : ℤ} {F : Type*}
    [NeZero n] [FunLike F ℍ ℂ] [CuspFormClass F Γ(n) k] (f : F) (s : ℝ) :
    Tendsto (fun t : ℝ ↦ (t : ℂ) ^ (s : ℂ) * (f : ℍ → ℂ).resToImagAxis t) atTop (𝓝 0) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hmem : (n : ℝ) ∈ (Γ(n) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp only [strictPeriods_Gamma]
    exact AddSubgroup.mem_zmultiples (n : ℝ)
  have hdecay' : (f : ℍ → ℂ) =O[atImInfty] fun τ ↦ rexp (-(2 * π / n) * τ.im) := by
    convert CuspFormClass.exp_decay_atImInfty hn_pos hmem (f := f) using 2 with τ; field_simp
  exact tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (div_pos (by positivity) hn_pos) hdecay' s

/-!
## Fourier expansion approach for polynomial decay

This section provides an alternative approach to polynomial decay that works directly from
Fourier expansions. If `F` has a Fourier expansion `∑_{m≥0} a_m exp(2πi(m+n₀)z)` with `n₀ > 0`,
then `F = O(exp(-2π n₀ · im z))` at `atImInfty`, which gives `t^s * F(it) → 0`.

This is useful for functions with q-expansions starting at a positive index (like `(E₂E₄ - E₆)²`).
-/

/--
If `F` has a Fourier expansion `∑_{m≥0} a_m exp(2πi(m+n₀)z)` and the coefficients are absolutely
summable at height `im z = c`, then `F = O(exp(-2π n₀ · im z))` at `atImInfty`.

The key bound is: for `im z ≥ c`,
  `‖F(z)‖ ≤ (∑_m ‖a_m‖ · exp(-2π c m)) · exp(-2π n₀ · im z)`
-/
lemma isBigO_atImInfty_of_fourier_shift
    {F : ℍ → ℂ} {a : ℕ → ℂ} {n₀ : ℕ} {c : ℝ}
    (hF : ∀ z : ℍ, F z =
      ∑' m : ℕ, a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * (z : ℂ)))
    (ha : Summable (fun m : ℕ ↦ ‖a m‖ * rexp (-(2 * π * c) * (m : ℝ)))) :
    F =O[atImInfty] fun z : ℍ ↦ rexp (-(2 * π * (n₀ : ℝ)) * z.im) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨∑' m, ‖a m‖ * rexp (-(2 * π * c) * m), ?_⟩
  rw [Filter.eventually_atImInfty]
  refine ⟨c, fun z hz ↦ ?_⟩
  rw [hF z, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply tsum_of_norm_bounded (ha.hasSum.mul_right (rexp (-(2 * π * n₀) * z.im)))
  intro m
  rw [norm_mul, norm_exp, mul_assoc (‖a m‖), ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [Real.exp_le_exp]
  -- The real part of 2πi(m+n₀)z is -2π(m+n₀) · im z.
  norm_num [Complex.mul_re, Complex.mul_im]
  -- For y ≥ c, exp(-2π(m+n₀)y) ≤ exp(-2πcm) * exp(-2πn₀y).
  have hm : (2 * π * (m : ℝ)) * c ≤ (2 * π * m) * z.im :=
    mul_le_mul_of_nonneg_left hz (by positivity)
  nlinarith

/--
If `F` has a Fourier expansion starting at index `n₀ > 0` with absolutely summable coefficients
at height `c`, then `t^s * F(it) → 0` as `t → ∞` for any real power `s`.

This converts a Fourier expansion representation directly into polynomial decay on the
imaginary axis.
-/
theorem tendsto_rpow_mul_resToImagAxis_of_fourier_shift
    {F : ℍ → ℂ} {a : ℕ → ℂ} {n₀ : ℕ} {c : ℝ} (hn₀ : 0 < n₀)
    (hF : ∀ z : ℍ, F z =
      ∑' m : ℕ, a m * Complex.exp (2 * π * Complex.I * ((m + n₀ : ℕ) : ℂ) * (z : ℂ)))
    (ha : Summable (fun m : ℕ ↦ ‖a m‖ * rexp (-(2 * π * c) * (m : ℝ)))) (s : ℝ) :
    Tendsto (fun t : ℝ ↦ t ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0) :=
  tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (by positivity)
    (isBigO_atImInfty_of_fourier_shift hF ha) s

/-- Extract the imaginary part condition at a specific point from `ResToImagAxis.Real`. -/
lemma ResToImagAxis.Real.im_eq_zero_at {F : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    {t : ℝ} (ht : 0 < t) (z : ℍ) (hz : z = ⟨Complex.I * t, by simp [ht]⟩) :
    (F z).im = 0 := by
  subst hz; simpa [ht] using hF t ht

/-- Extract the positivity condition at a specific point from `ResToImagAxis.Pos`. -/
lemma ResToImagAxis.Pos.re_pos_at {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    {t : ℝ} (ht : 0 < t) (z : ℍ) (hz : z = ⟨Complex.I * t, by simp [ht]⟩) :
    0 < (F z).re := by
  subst hz; simpa [ht] using hF.2 t ht

/-- Tendsto conversion: if F tends to c at atImInfty, then F.resToImagAxis tends to c at atTop. -/
lemma tendsto_resToImagAxis_of_tendsto_atImInfty {F : ℍ → ℂ} {c : ℂ}
    (hF : Tendsto F atImInfty (𝓝 c)) :
    Tendsto F.resToImagAxis atTop (𝓝 c) := by
  apply (hF.comp tendsto_ofComplex_I_mul_atTop).congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ht, ofComplex_apply_of_im_pos]
