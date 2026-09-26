# Inventory: XYin/PhD/Modularforms/ResToImagAxis.lean  (403 lines)

Restriction `t ↦ F(it)` of a function `F : ℍ → ℂ` to the positive imaginary axis (`ResToImagAxis F`, alias `F.resToImagAxis`), the predicates `Real` / `Pos` / `EventuallyPos` (real-valued / positive / eventually positive on the axis) with their closure lemmas (tagged `@[fun_prop]`), real-differentiability of the restriction of a holomorphic function, the behaviour of the restriction under the slash action by `S`, and polynomial decay `t^s·F(it) → 0` for functions that are `O(exp(-c·Im τ))` at i∞ (cusp forms; functions with a Fourier expansion starting at a positive index). Downstream (Delta.lean, Eisenstein.lean) only the definition and the predicates `ResToImagAxis.Real` / `ResToImagAxis.Pos` are used.

## Declarations

### `noncomputable def ResToImagAxis`
- **Type**: `(F : ℍ → ℂ) : ℝ → ℂ`
- **What**: `t ↦ F(it)` for `t > 0`, and `0` for `t ≤ 0`.
- **How**: `fun t => if ht : 0 < t then F ⟨I * t, _⟩ else 0` (dependent `if`).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: Function.resToImagAxis, resToImagAxis_eq_resToImagAxis, resToImagAxis_apply, ResToImagAxis.Differentiable, ResToImagAxis.SlashActionS, resToImagAxis_add_apply/mul_apply/smul_apply, ResToImagAxis.Real.const, .Real.neg, .Pos.const, .Real.eq_real_part, isBigO_resToImagAxis_of_isBigO_atImInfty, .Real.im_eq_zero_at, .Pos.re_pos_at, tendsto_resToImagAxis_of_tendsto_atImInfty; externally Delta.lean:331/370 and Eisenstein.lean:474/542 (unfolded by `simp [ResToImagAxis, ht]`)
- **Visibility**: public
- **Lines**: 32–33, body 1 line
- **Notes**: docstring. No mathlib analogue (searched `imaginary axis`, `resToImagAxis`, `I * t` in `Mathlib/Analysis/Complex/UpperHalfPlane/` and `Mathlib/NumberTheory/ModularForms/`; only the `atImInfty.NeBot` proof uses `⟨I * t, _⟩`). No `_apply`/`_of_pos` simp lemma: every consumer unfolds it with `simp [ResToImagAxis, ht]`.

### `noncomputable def Function.resToImagAxis`
- **Type**: `(F : ℍ → ℂ) : ℝ → ℂ`
- **What**: Dot-notation alias `F.resToImagAxis` for `ResToImagAxis F`.
- **How**: `ResToImagAxis F`.
- **Hypotheses**: none.
- **Uses from project**: ResToImagAxis
- **Used by**: every statement from L40 onward; externally Delta.lean:358
- **Visibility**: public
- **Lines**: 38, body 1 line
- **Notes**: docstring. Two names for one function; the simp lemma below rewrites the alias *away*, so the simp-normal form is the non-dot spelling.

### `@[simp] lemma Function.resToImagAxis_eq_resToImagAxis`
- **Type**: `(F : ℍ → ℂ) : F.resToImagAxis = ResToImagAxis F`
- **What**: The alias unfolds.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: Function.resToImagAxis, ResToImagAxis
- **Used by**: ResToImagAxis.Differentiable
- **Visibility**: public
- **Lines**: 40–41, body 1 line
- **Notes**: `@[simp]`.

### `@[simp] lemma Function.resToImagAxis_apply`
- **Type**: `(F : ℍ → ℂ) (t : ℝ) : F.resToImagAxis t = ResToImagAxis F t`
- **What**: Pointwise version of the previous lemma.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: Function.resToImagAxis, ResToImagAxis
- **Used by**: ResToImagAxis.Real.const
- **Visibility**: public
- **Lines**: 43–44, body 1 line
- **Notes**: `@[simp]`; redundant with the previous simp lemma.

### `@[fun_prop] noncomputable def ResToImagAxis.Real`
- **Type**: `(F : ℍ → ℂ) : Prop`
- **What**: `F(it)` is real for every `t > 0`.
- **How**: `∀ t : ℝ, 0 < t → (F.resToImagAxis t).im = 0`.
- **Hypotheses**: none.
- **Uses from project**: Function.resToImagAxis
- **Used by**: ResToImagAxis.Pos, .EventuallyPos, all `.Real.*` lemmas, .Real.eq_real_part, .Real.im_eq_zero_at; externally Delta.lean:329 (Delta_imag_axis_real), Eisenstein.lean:472/530/535/540
- **Visibility**: public
- **Lines**: 53–54, body 1 line
- **Notes**: docstring; `@[fun_prop]` registers it as a function property. Marked `noncomputable` although it is a `Prop`.

### `@[fun_prop] noncomputable def ResToImagAxis.Pos`
- **Type**: `(F : ℍ → ℂ) : Prop`
- **What**: `F(it)` is real and strictly positive for every `t > 0`.
- **How**: `ResToImagAxis.Real F ∧ ∀ t, 0 < t → 0 < (F.resToImagAxis t).re`.
- **Hypotheses**: none.
- **Uses from project**: ResToImagAxis.Real, Function.resToImagAxis
- **Used by**: all `.Pos.*` lemmas, .EventuallyPos.from_pos, .Pos.re_pos_at; externally Delta.lean:398 (Delta_imag_axis_pos)
- **Visibility**: public
- **Lines**: 60–61, body 1 line
- **Notes**: docstring; `@[fun_prop]`.

### `@[fun_prop] noncomputable def ResToImagAxis.EventuallyPos`
- **Type**: `(F : ℍ → ℂ) : Prop`
- **What**: `F(it)` is real for all `t > 0` and positive for all sufficiently large `t`.
- **How**: `ResToImagAxis.Real F ∧ ∃ t₀, 0 < t₀ ∧ ∀ t, t₀ ≤ t → 0 < (F.resToImagAxis t).re`.
- **Hypotheses**: none.
- **Uses from project**: ResToImagAxis.Real, Function.resToImagAxis
- **Used by**: all `.EventuallyPos.*` lemmas
- **Visibility**: public
- **Lines**: 68–69, body 1 line
- **Notes**: docstring; hand-rolled `∃ t₀, ∀ t ≥ t₀` = `∀ᶠ t in atTop, …` (`Filter.eventually_atTop`). Not used outside this file.

### `@[fun_prop] theorem ResToImagAxis.Differentiable`
- **Type**: `(F : ℍ → ℂ) (hF : MDiff F) (t : ℝ) (ht : 0 < t) : DifferentiableAt ℝ F.resToImagAxis t`
- **What**: The restriction to the axis of a holomorphic function on ℍ is real-differentiable at every `t > 0`.
- **How**: `mdifferentiableAt_iff` turns `MDiff` into complex differentiability of `F ∘ ofComplex` at `it`; restrict scalars (`DifferentiableAt.restrictScalars ℝ`, `IsScalarTower.complexToReal`) and compose with `t ↦ I·t` (`ofRealCLM.differentiableAt.const_mul`); transfer to `ResToImagAxis` by `congr_of_eventuallyEq` on `lt_mem_nhds ht` with `ofComplex_apply_of_im_pos`.
- **Hypotheses**: `F` is `MDifferentiable 𝓘(ℂ) 𝓘(ℂ)` (mathlib scoped notation `MDiff`, `Mathlib/Geometry/Manifold/Notation.lean:858`), `t > 0`.
- **Uses from project**: Function.resToImagAxis, resToImagAxis_eq_resToImagAxis, ResToImagAxis
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 72–85, body ≈ 12 lines
- **Notes**: unused anywhere. `@[fun_prop]` on a lemma with a side condition `0 < t` that `fun_prop` cannot discharge by default. `simp_all only` + `rw` at the end is fragile.

### `theorem ResToImagAxis.SlashActionS`
- **Type**: `(F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) : (F ∣[k] S).resToImagAxis t = (Complex.I) ^ (-k) * t ^ (-k) * F.resToImagAxis (1 / t)`
- **What**: On the axis, `(F|_k S)(it) = (it)^{-k}·F(i/t)`.
- **How**: `modular_slash_S_apply` gives `(F ∣[k] S) z = F(-1/z)·z^{-k}`; identifies `-1/(it)` with `i/t` by `UpperHalfPlane.ext`, and splits `(it)^{-k}` by `mul_zpow`.
- **Hypotheses**: `t > 0`.
- **Uses from project**: Function.resToImagAxis, ResToImagAxis, modular_slash_S_apply (SlashActionAuxil.lean)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 90–98, body ≈ 7 lines
- **Notes**: unused anywhere; docstring. The `(by rw […]; simp […] : …)` inline-typed proof term is hard to read. `modular_slash_S_apply` = mathlib `SlashInvariantForm.slash_S_apply` (`Identities.lean:47`).

### `private lemma resToImagAxis_add_apply`
- **Type**: `(F G : ℍ → ℂ) (t : ℝ) : (F + G).resToImagAxis t = F.resToImagAxis t + G.resToImagAxis t`
- **What**: Restriction is additive.
- **How**: case split on `0 < t`, `simp [ResToImagAxis, ht]`.
- **Hypotheses**: none.
- **Uses from project**: Function.resToImagAxis, ResToImagAxis
- **Used by**: ResToImagAxis.Real.add, .Pos.add, .EventuallyPos.add
- **Visibility**: private
- **Lines**: 100–102, body 1 line
- **Notes**: should be a public `@[simp]` lemma (`resToImagAxis_add`).

### `private lemma resToImagAxis_mul_apply`
- **Type**: `(F G : ℍ → ℂ) (t : ℝ) : (F * G).resToImagAxis t = F.resToImagAxis t * G.resToImagAxis t`
- **What**: Restriction is multiplicative.
- **How**: same case split + simp.
- **Hypotheses**: none.
- **Uses from project**: Function.resToImagAxis, ResToImagAxis
- **Used by**: .Real.mul, .Pos.mul, .EventuallyPos.mul
- **Visibility**: private
- **Lines**: 104–106, body 1 line
- **Notes**: same as above.

### `private lemma resToImagAxis_smul_apply`
- **Type**: `(c : ℝ) (F : ℍ → ℂ) (t : ℝ) : (c • F).resToImagAxis t = c • F.resToImagAxis t`
- **What**: Restriction commutes with real scalars.
- **How**: same case split + simp.
- **Hypotheses**: none.
- **Uses from project**: Function.resToImagAxis, ResToImagAxis
- **Used by**: .Real.smul, .Pos.smul, .EventuallyPos.smul
- **Visibility**: private
- **Lines**: 108–110, body 1 line
- **Notes**: same; the `_neg`, `_sub`, `_pow`, `_zero`, `_one`, `_const` companions are missing (neg is redone inline at L130).

### `@[fun_prop] theorem ResToImagAxis.Real.const`
- **Type**: `(c : ℝ) : ResToImagAxis.Real (fun _ => c)`
- **What**: Real constants are real on the axis.
- **How**: unfold; `ofReal_im`.
- **Hypotheses**: none.
- **Uses from project**: ResToImagAxis.Real, resToImagAxis_apply, ResToImagAxis
- **Used by**: .Real.zero, .Real.one, .Pos.const
- **Visibility**: public
- **Lines**: 116–118, body 2 lines
- **Notes**: docstring at L112–114 is a section comment mislabelled as a docstring for this lemma.

### `@[fun_prop] theorem ResToImagAxis.Real.zero`
- **Type**: `ResToImagAxis.Real (fun _ => 0)`
- **What**: Zero is real on the axis.
- **How**: `Real.const 0`.
- **Hypotheses**: none.
- **Uses from project**: ResToImagAxis.Real.const
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 121
- **Notes**: unused anywhere.

### `@[fun_prop] theorem ResToImagAxis.Real.one`
- **Type**: `ResToImagAxis.Real (fun _ => 1)`
- **What**: One is real on the axis.
- **How**: `Real.const 1`.
- **Hypotheses**: none.
- **Uses from project**: ResToImagAxis.Real.const
- **Used by**: .Real.pow
- **Visibility**: public
- **Lines**: 124
- **Notes**: none.

### `@[fun_prop] theorem ResToImagAxis.Real.neg`
- **Type**: `{F : ℍ → ℂ} (hF : ResToImagAxis.Real F) : ResToImagAxis.Real (-F)`
- **What**: Negation preserves realness.
- **How**: `congrArg Neg.neg (hF t ht)` after unfolding.
- **Hypotheses**: `F` real on the axis.
- **Uses from project**: ResToImagAxis.Real, Function.resToImagAxis, ResToImagAxis
- **Used by**: .Real.sub
- **Visibility**: public
- **Lines**: 127–130, body 2 lines
- **Notes**: reproves `resToImagAxis_neg_apply` inline.

### `@[fun_prop] theorem ResToImagAxis.Real.add`
- **Type**: `{F G} (hF : Real F) (hG : Real G) : ResToImagAxis.Real (F + G)`
- **What**: Sums of real-on-axis functions are real on the axis.
- **How**: `resToImagAxis_add_apply`, `Complex.add_im`.
- **Hypotheses**: `F`, `G` real on the axis.
- **Uses from project**: ResToImagAxis.Real, resToImagAxis_add_apply
- **Used by**: .Real.sub, .Pos.add, .EventuallyPos.add
- **Visibility**: public
- **Lines**: 133–136, body 2 lines
- **Notes**: none.

### `@[fun_prop] theorem ResToImagAxis.Real.sub`
- **Type**: `{F G} (hF) (hG) : ResToImagAxis.Real (F - G)`
- **What**: Differences preserve realness.
- **How**: `sub_eq_add_neg` + `Real.add hF hG.neg`.
- **Hypotheses**: as above.
- **Uses from project**: ResToImagAxis.Real, .Real.add, .Real.neg
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 139–141, body 1 line
- **Notes**: unused anywhere.

### `@[fun_prop] theorem ResToImagAxis.Real.mul`
- **Type**: `{F G} (hF) (hG) : ResToImagAxis.Real (F * G)`
- **What**: Products preserve realness.
- **How**: `resToImagAxis_mul_apply`, `Complex.mul_im`.
- **Hypotheses**: as above.
- **Uses from project**: ResToImagAxis.Real, resToImagAxis_mul_apply
- **Used by**: .Real.pow, .Pos.mul, .EventuallyPos.mul
- **Visibility**: public
- **Lines**: 144–148, body 2 lines
- **Notes**: none.

### `@[fun_prop] theorem ResToImagAxis.Real.smul`
- **Type**: `{F} {c : ℝ} (hF) : ResToImagAxis.Real (c • F)`
- **What**: Real scalar multiples preserve realness.
- **How**: `resToImagAxis_smul_apply`, `Complex.smul_im`.
- **Hypotheses**: `F` real on the axis.
- **Uses from project**: ResToImagAxis.Real, resToImagAxis_smul_apply
- **Used by**: .Pos.smul, .EventuallyPos.smul
- **Visibility**: public
- **Lines**: 151–154, body 2 lines
- **Notes**: none.

### `@[fun_prop] theorem ResToImagAxis.Real.pow`
- **Type**: `{F} (hF) (n : ℕ) : ResToImagAxis.Real (F ^ n)`
- **What**: Natural powers preserve realness.
- **How**: induction on `n`, `Real.one` and `Real.mul`.
- **Hypotheses**: `F` real on the axis.
- **Uses from project**: ResToImagAxis.Real, .Real.one, .Real.mul
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 157–161, body 3 lines
- **Notes**: unused anywhere.

### `theorem ResToImagAxis.Pos.const`
- **Type**: `(c : ℝ) (hc : 0 < c) : ResToImagAxis.Pos (fun _ => c)`
- **What**: Positive constants are positive on the axis.
- **How**: `⟨Real.const c, by simp [ResToImagAxis, ht, hc]⟩`.
- **Hypotheses**: `0 < c`.
- **Uses from project**: ResToImagAxis.Pos, .Real.const, ResToImagAxis
- **Used by**: .Pos.one, .EventuallyPos.const
- **Visibility**: public
- **Lines**: 163–164, body 1 line
- **Notes**: the only closure lemma without `@[fun_prop]` — inconsistent with its siblings.

### `@[fun_prop] theorem ResToImagAxis.Pos.one`
- **Type**: `ResToImagAxis.Pos (fun _ => 1)`
- **What**: One is positive on the axis.
- **How**: `Pos.const 1 one_pos`.
- **Hypotheses**: none.
- **Uses from project**: ResToImagAxis.Pos.const
- **Used by**: .Pos.pow, .EventuallyPos.one
- **Visibility**: public
- **Lines**: 167–168
- **Notes**: none.

### `@[fun_prop] theorem ResToImagAxis.Pos.add`
- **Type**: `{F G} (hF : Pos F) (hG : Pos G) : ResToImagAxis.Pos (F + G)`
- **What**: Sums of positive-on-axis functions are positive.
- **How**: `Real.add` for the real part, `add_pos` with `resToImagAxis_add_apply`/`Complex.add_re`.
- **Hypotheses**: as stated.
- **Uses from project**: ResToImagAxis.Pos, .Real.add, resToImagAxis_add_apply
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 171–174, body 2 lines
- **Notes**: unused anywhere.

### `@[fun_prop] theorem ResToImagAxis.Pos.mul`
- **Type**: `{F G} (hF) (hG) : ResToImagAxis.Pos (F * G)`
- **What**: Products preserve positivity.
- **How**: `Real.mul`; `Complex.mul_re` with the imaginary parts zero, `mul_pos`.
- **Hypotheses**: as stated.
- **Uses from project**: ResToImagAxis.Pos, .Real.mul, resToImagAxis_mul_apply
- **Used by**: .Pos.pow
- **Visibility**: public
- **Lines**: 177–181, body 3 lines
- **Notes**: none.

### `@[fun_prop] theorem ResToImagAxis.Pos.smul`
- **Type**: `{F} {c : ℝ} (hF : Pos F) (hc : 0 < c) : ResToImagAxis.Pos (c • F)`
- **What**: Positive scalar multiples preserve positivity.
- **How**: `Real.smul`; `Complex.smul_re`, `mul_pos`.
- **Hypotheses**: `0 < c`.
- **Uses from project**: ResToImagAxis.Pos, .Real.smul, resToImagAxis_smul_apply
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 184–187, body 2 lines
- **Notes**: unused anywhere.

### `@[fun_prop] theorem ResToImagAxis.Pos.pow`
- **Type**: `{F} (hF) (n : ℕ) : ResToImagAxis.Pos (F ^ n)`
- **What**: Natural powers preserve positivity.
- **How**: induction with `Pos.one`, `Pos.mul`.
- **Hypotheses**: `F` positive on the axis.
- **Uses from project**: ResToImagAxis.Pos, .Pos.one, .Pos.mul
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 190–194, body 3 lines
- **Notes**: unused anywhere.

### `@[fun_prop] theorem ResToImagAxis.EventuallyPos.from_pos`
- **Type**: `{F} (hF : Pos F) : ResToImagAxis.EventuallyPos F`
- **What**: Positive implies eventually positive.
- **How**: `t₀ = 1`.
- **Hypotheses**: as stated.
- **Uses from project**: ResToImagAxis.EventuallyPos, ResToImagAxis.Pos
- **Used by**: .EventuallyPos.one, .EventuallyPos.const
- **Visibility**: public
- **Lines**: 197–199, body 1 line
- **Notes**: mathlib naming would be `Pos.eventuallyPos`.

### `@[fun_prop] theorem ResToImagAxis.EventuallyPos.one`
- **Type**: `ResToImagAxis.EventuallyPos (fun _ => 1)`
- **What**: One is eventually positive.
- **How**: `from_pos Pos.one`.
- **Hypotheses**: none.
- **Uses from project**: .EventuallyPos.from_pos, .Pos.one
- **Used by**: .EventuallyPos.pow
- **Visibility**: public
- **Lines**: 202–204
- **Notes**: none.

### `@[fun_prop] theorem ResToImagAxis.EventuallyPos.const`
- **Type**: `(c : ℝ) (hc : 0 < c) : ResToImagAxis.EventuallyPos (fun _ => c)`
- **What**: Positive constants are eventually positive.
- **How**: `from_pos (Pos.const c hc)`.
- **Hypotheses**: `0 < c`.
- **Uses from project**: .EventuallyPos.from_pos, .Pos.const
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 207–209
- **Notes**: unused anywhere.

### `@[fun_prop] theorem ResToImagAxis.EventuallyPos.add`
- **Type**: `{F G} (hF : EventuallyPos F) (hG : EventuallyPos G) : ResToImagAxis.EventuallyPos (F + G)`
- **What**: Sums are eventually positive from `max` of the two thresholds.
- **How**: thresholds `max tF tG`, `add_pos`, `resToImagAxis_add_apply`.
- **Hypotheses**: as stated.
- **Uses from project**: ResToImagAxis.EventuallyPos, .Real.add, resToImagAxis_add_apply
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 212–219, body ≈ 5 lines
- **Notes**: unused anywhere; the `max`-threshold bookkeeping is what `Filter.Eventually.and` does automatically.

### `@[fun_prop] theorem ResToImagAxis.EventuallyPos.mul`
- **Type**: `{F G} (hF) (hG) : ResToImagAxis.EventuallyPos (F * G)`
- **What**: Products are eventually positive.
- **How**: same `max` bookkeeping plus `Complex.mul_re` with zero imaginary parts, `mul_pos`.
- **Hypotheses**: as stated.
- **Uses from project**: ResToImagAxis.EventuallyPos, .Real.mul, resToImagAxis_mul_apply
- **Used by**: .EventuallyPos.pow
- **Visibility**: public
- **Lines**: 222–233, body ≈ 9 lines
- **Notes**: none.

### `@[fun_prop] theorem ResToImagAxis.EventuallyPos.pow`
- **Type**: `{F} (hF) (n : ℕ) : ResToImagAxis.EventuallyPos (F ^ n)`
- **What**: Powers are eventually positive.
- **How**: induction with `.one`, `.mul`.
- **Hypotheses**: as stated.
- **Uses from project**: ResToImagAxis.EventuallyPos, .EventuallyPos.one, .EventuallyPos.mul
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 236–241, body 3 lines
- **Notes**: unused anywhere.

### `@[fun_prop] theorem ResToImagAxis.EventuallyPos.smul`
- **Type**: `{F} {c : ℝ} (hF) (hc : 0 < c) : ResToImagAxis.EventuallyPos (c • F)`
- **What**: Positive scalar multiples are eventually positive.
- **How**: same threshold, `mul_pos`.
- **Hypotheses**: `0 < c`.
- **Uses from project**: ResToImagAxis.EventuallyPos, .Real.smul, resToImagAxis_smul_apply
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 244–248, body 3 lines
- **Notes**: unused anywhere.

### `theorem ResToImagAxis.Real.eq_real_part`
- **Type**: `{F} (hF : Real F) (t : ℝ) : F.resToImagAxis t = (F.resToImagAxis t).re`
- **What**: A real-on-axis restriction equals (the cast of) its real part, for all `t` (both branches of the `if`).
- **How**: `split_ifs`, `Complex.ext` with `hF t ht` for the imaginary part.
- **Hypotheses**: `F` real on the axis.
- **Uses from project**: ResToImagAxis.Real, Function.resToImagAxis, ResToImagAxis
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 251–256, body 3 lines
- **Notes**: unused anywhere; docstring. Mathlib: `Complex.conj_eq_iff_re`/`Complex.ext_iff`.

### `private lemma tendsto_ofComplex_I_mul_atTop`
- **Type**: `Tendsto (fun t : ℝ ↦ ofComplex (I * t)) atTop atImInfty`
- **What**: `it → i∞` as `t → +∞`.
- **How**: mathlib `tendsto_comap_im_ofComplex` (`FunctionsBoundedAtInfty.lean:78`) composed with `tendsto_id`, via `tendsto_comap_iff`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: isBigO_resToImagAxis_of_isBigO_atImInfty, tendsto_resToImagAxis_of_tendsto_atImInfty
- **Visibility**: private
- **Lines**: 267–271, body 3 lines
- **Notes**: good candidate for a public lemma (`UpperHalfPlane.tendsto_ofComplex_I_mul_atTop`).

### `lemma isBigO_resToImagAxis_of_isBigO_atImInfty`
- **Type**: `{F : ℍ → ℂ} {c : ℝ} (_hc : 0 < c) (hF : F =O[atImInfty] fun τ => Real.exp (-c * τ.im)) : F.resToImagAxis =O[atTop] fun t => Real.exp (-c * t)`
- **What**: Exponential decay at i∞ restricts to exponential decay along the axis.
- **How**: `hF.comp_tendsto tendsto_ofComplex_I_mul_atTop`, then `IsBigO.congr'` on `eventually_gt_atTop 0` using `ofComplex_apply_of_im_pos` (`Topology.lean:162`).
- **Hypotheses**: `0 < c` (unused — named `_hc`).
- **Uses from project**: Function.resToImagAxis, ResToImagAxis, tendsto_ofComplex_I_mul_atTop
- **Used by**: tendsto_rpow_mul_resToImagAxis_of_isBigO_exp
- **Visibility**: public
- **Lines**: 277–285, body ≈ 6 lines
- **Notes**: docstring; the hypothesis `_hc` is dead and should be dropped.

### `lemma tendsto_rpow_mul_of_isBigO_exp`
- **Type**: `{g : ℝ → ℂ} {s b : ℝ} (hb : 0 < b) (hg : g =O[atTop] fun t => rexp (-b * t)) : Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * g t) atTop (𝓝 0)`
- **What**: Exponentially decaying functions on ℝ, multiplied by any real power, tend to 0.
- **How**: `IsBigO.mul` of `t^s` with `hg` (through `Complex.isBigO_ofReal_right`, `Mathlib/Analysis/Complex/Asymptotics.lean:39`), then `trans_tendsto` of mathlib `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` (`Pow/Asymptotics.lean:135`) cast to ℂ with `Complex.ofReal_cpow`.
- **Hypotheses**: `0 < b`.
- **Uses from project**: []
- **Used by**: tendsto_rpow_mul_resToImagAxis_of_isBigO_exp
- **Visibility**: public
- **Lines**: 294–300, body ≈ 4 lines
- **Notes**: docstring; a general real-analysis lemma unrelated to ℍ — belongs in a `ForMathlib` file (or upstream next to `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`).

### `theorem tendsto_rpow_mul_resToImagAxis_of_isBigO_exp`
- **Type**: `{F} {c : ℝ} (hc : 0 < c) (hF : F =O[atImInfty] fun τ => rexp (-c * τ.im)) (s : ℝ) : Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0)`
- **What**: Exponential decay at i∞ gives `t^s·F(it) → 0` for every real `s`.
- **How**: composition of the two previous lemmas.
- **Hypotheses**: `0 < c`.
- **Uses from project**: Function.resToImagAxis, tendsto_rpow_mul_of_isBigO_exp, isBigO_resToImagAxis_of_isBigO_atImInfty
- **Used by**: cuspForm_rpow_mul_resToImagAxis_tendsto_zero, tendsto_rpow_mul_resToImagAxis_of_fourier_shift
- **Visibility**: public
- **Lines**: 306–309, body 1 line
- **Notes**: docstring.

### `theorem cuspForm_rpow_mul_resToImagAxis_tendsto_zero`
- **Type**: `{n : ℕ} {k : ℤ} {F : Type*} [NeZero n] [FunLike F ℍ ℂ] [CuspFormClass F Γ(n) k] (f : F) (s : ℝ) : Tendsto (fun t : ℝ => (t : ℂ) ^ (s : ℂ) * (f : ℍ → ℂ).resToImagAxis t) atTop (𝓝 0)`
- **What**: For a cusp form of level `Γ(n)`, `t^s·f(it) → 0` for every real `s`.
- **How**: mathlib `CuspFormClass.exp_decay_atImInfty` (`QExpansion.lean:412`) with period `n ∈ strictPeriods Γ(n)` (`strictPeriods_Gamma`, `Cusps.lean:452`, via `AddSubgroup.mem_zmultiples`), normalised by `field_simp` to `exp(-(2π/n)·Im τ)`, then the previous theorem.
- **Hypotheses**: `n ≠ 0`, `f` a cusp form for `Γ(n)`.
- **Uses from project**: Function.resToImagAxis, tendsto_rpow_mul_resToImagAxis_of_isBigO_exp
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 316–325, body ≈ 7 lines
- **Notes**: unused anywhere; docstring.

### `lemma isBigO_atImInfty_of_fourier_shift`
- **Type**: `{F : ℍ → ℂ} {a : ℕ → ℂ} {n₀ : ℕ} {c : ℝ} (_hn₀ : 0 < n₀) (_hc : 0 < c) (hF : ∀ z : ℍ, F z = ∑' m : ℕ, a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * (z : ℂ))) (ha : Summable (fun m : ℕ => ‖a m‖ * rexp (-(2 * π * c) * (m : ℝ)))) : F =O[atImInfty] fun z : ℍ => rexp (-(2 * π * (n₀ : ℝ)) * z.im)`
- **What**: A function with Fourier expansion `∑ a_m q^{m+n₀}` whose coefficients are absolutely summable at height `c` is `O(exp(-2π n₀ Im z))` at i∞.
- **How**: `isBigO_iff` with constant `∑' ‖a_m‖ e^{-2πcm}`; for `Im z ≥ c` (`Filter.eventually_atImInfty`) bound the series termwise with `tsum_of_norm_bounded` against `ha.hasSum.mul_right`, using `norm_exp` and `Real.exp_add`; the exponent comparison `2πm·c ≤ 2πm·Im z` is closed by `nlinarith`.
- **Hypotheses**: `0 < n₀`, `0 < c` (both unused in the proof — named with underscores), pointwise Fourier expansion, absolute summability at height `c`.
- **Uses from project**: Filter.eventually_atImInfty (AtImInfty.lean)
- **Used by**: tendsto_rpow_mul_resToImagAxis_of_fourier_shift
- **Visibility**: public
- **Lines**: 345–366, body ≈ 16 lines
- **Notes**: docstring; hand-rolled `‖∑'‖ ≤ ∑'‖·‖` bound; `norm_num [Complex.mul_re, Complex.mul_im]` then `nlinarith` is heavy. No mathlib analogue (all `=O[atImInfty]` results in mathlib are for Δ or for periodic `IsZeroAtImInfty` functions: `Discriminant.lean:181/259`, `QExpansion.lean:326/351/373`).

### `theorem tendsto_rpow_mul_resToImagAxis_of_fourier_shift`
- **Type**: same hypotheses as above plus `(s : ℝ)`; conclusion `Tendsto (fun t : ℝ => t ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0)`
- **What**: Fourier expansions starting at a positive index give polynomial decay along the axis.
- **How**: previous lemma + `tendsto_rpow_mul_resToImagAxis_of_isBigO_exp`.
- **Hypotheses**: as above.
- **Uses from project**: Function.resToImagAxis, tendsto_rpow_mul_resToImagAxis_of_isBigO_exp, isBigO_atImInfty_of_fourier_shift
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 375–382, body 2 lines
- **Notes**: unused anywhere; docstring says it is for `(E₂E₄ − E₆)²`-type functions, but no caller exists.

### `lemma ResToImagAxis.Real.im_eq_zero_at`
- **Type**: `{F} (hF : Real F) {t : ℝ} (ht : 0 < t) (z : ℍ) (hz : z = ⟨Complex.I * t, _⟩) : (F z).im = 0`
- **What**: Pointwise extraction of realness at a point on the axis given as `z`.
- **How**: `subst hz; simpa [ResToImagAxis, ht] using hF t ht`.
- **Hypotheses**: `t > 0`, `z = it`.
- **Uses from project**: ResToImagAxis.Real, Function.resToImagAxis, ResToImagAxis
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 385–388, body 1 line
- **Notes**: unused anywhere; the `(z) (hz : z = …)` interface is awkward (just state it for `⟨I * t, _⟩`).

### `lemma ResToImagAxis.Pos.re_pos_at`
- **Type**: `{F} (hF : Pos F) {t} (ht : 0 < t) (z : ℍ) (hz : z = ⟨Complex.I * t, _⟩) : 0 < (F z).re`
- **What**: Pointwise extraction of positivity.
- **How**: same as above with `hF.2`.
- **Hypotheses**: as above.
- **Uses from project**: ResToImagAxis.Pos, Function.resToImagAxis, ResToImagAxis
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 391–394, body 1 line
- **Notes**: unused anywhere.

### `lemma tendsto_resToImagAxis_of_tendsto_atImInfty`
- **Type**: `{F : ℍ → ℂ} {c : ℂ} (hF : Tendsto F atImInfty (nhds c)) : Tendsto F.resToImagAxis atTop (nhds c)`
- **What**: A limit at i∞ restricts to a limit along the axis.
- **How**: `hF.comp tendsto_ofComplex_I_mul_atTop` and `congr'` on `eventually_gt_atTop 0` with `ofComplex_apply_of_im_pos`.
- **Hypotheses**: `F → c` at i∞.
- **Uses from project**: Function.resToImagAxis, ResToImagAxis, tendsto_ofComplex_I_mul_atTop
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 397–403, body 4 lines
- **Notes**: unused anywhere; docstring. Same skeleton as `isBigO_resToImagAxis_of_isBigO_atImInfty`.

## File Summary
- Total declarations: 45 (5 defs: ResToImagAxis, Function.resToImagAxis, ResToImagAxis.Real, ResToImagAxis.Pos, ResToImagAxis.EventuallyPos; 40 lemmas/theorems; 0 instances; 0 other)
- Key API (used by 3+ others in the file): ResToImagAxis (16), Function.resToImagAxis (≈40), ResToImagAxis.Real (14), ResToImagAxis.Pos (8), ResToImagAxis.EventuallyPos (8), resToImagAxis_add_apply (3), resToImagAxis_mul_apply (3), resToImagAxis_smul_apply (3), ResToImagAxis.Real.add (3), ResToImagAxis.Real.mul (3), ResToImagAxis.Real.const (3)
- Unused declarations (not used by anything in this file): ResToImagAxis.Differentiable, ResToImagAxis.SlashActionS, Real.zero, Real.sub, Real.pow, Pos.add, Pos.smul, Pos.pow, EventuallyPos.const, EventuallyPos.add, EventuallyPos.pow, EventuallyPos.smul, Real.eq_real_part, cuspForm_rpow_mul_resToImagAxis_tendsto_zero, tendsto_rpow_mul_resToImagAxis_of_fourier_shift, Real.im_eq_zero_at, Pos.re_pos_at, tendsto_resToImagAxis_of_tendsto_atImInfty. Project-wide, only `ResToImagAxis`, `Function.resToImagAxis`, `ResToImagAxis.Real`, `ResToImagAxis.Pos` are referenced outside this file (Delta.lean, Eisenstein.lean); none of the closure lemmas, `EventuallyPos`, or the decay section is.
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: isBigO_atImInfty_of_fourier_shift, 16 lines)

## Observations

### Mathlib API candidates
- `ResToImagAxis` (L32): no mathlib analogue found (searched `imaginary axis`, `resToImagAxis`, `fun t : ℝ ↦ … I * t` in `Mathlib/Analysis/Complex/UpperHalfPlane/`, `Mathlib/NumberTheory/ModularForms/`). The `0 < t` case split and `ofComplex` juggling (L83–85, L282–285, L401–403) would disappear if it were defined as `fun t => F (ofComplex (I * t))` (mathlib `UpperHalfPlane.ofComplex`, `Topology.lean:150/162`), since `ofComplex` already returns junk off ℍ.
- `ResToImagAxis.SlashActionS` (L90): the only ingredient is `modular_slash_S_apply` = mathlib `SlashInvariantForm.slash_S_apply` (`Mathlib/NumberTheory/ModularForms/Identities.lean:47`; verified identical statement by scratch typecheck this session).
- `tendsto_rpow_mul_of_isBigO_exp` (L294): pure ℝ/ℂ asymptotics; ℝ-valued core is mathlib `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` (`Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:135`); the ℂ lift uses `Complex.isBigO_ofReal_right` (`Analysis/Complex/Asymptotics.lean:39`). Upstreamable as stated.
- `cuspForm_rpow_mul_resToImagAxis_tendsto_zero` (L316): rides on `CuspFormClass.exp_decay_atImInfty` (`QExpansion.lean:412`) and `strictPeriods_Gamma` (`Cusps.lean:452`).
- `isBigO_atImInfty_of_fourier_shift` (L345): hand-rolled `‖tsum‖ ≤ tsum ‖·‖` with explicit `isBigO_iff` constant and manual exponent comparison; no mathlib analogue for shifted Fourier series (searched `=O[atImInfty]`: only `exp_isBigO_discriminant`, `exp_decay_isBigO_discriminant`, `exp_decay_atImInfty`). Hypotheses `_hn₀`, `_hc` are dead.
- `ResToImagAxis.EventuallyPos` (L68) is a hand-rolled `∀ᶠ t in atTop, 0 < (F.resToImagAxis t).re` (`Filter.eventually_atTop`); `.add`/`.mul` (L212–233) redo `Filter.Eventually.and`'s `max` bookkeeping by hand.
- `ResToImagAxis.Differentiable` (L72): composable from `mdifferentiableAt_iff`, `DifferentiableAt.restrictScalars`, `ofRealCLM` — all mathlib; nothing missing, but the lemma is unused.
- `tendsto_ofComplex_I_mul_atTop` (private, L267): `tendsto_comap_im_ofComplex` (`FunctionsBoundedAtInfty.lean:78`) + `tendsto_id`; worth making public.

### Missing API / repeated patterns
- Repeated fragment `by_cases ht : 0 < t <;> simp [Function.resToImagAxis, ResToImagAxis, ht]` (L102, L106, L110) and `simp [Function.resToImagAxis, ResToImagAxis, ht, ofComplex_apply_of_im_pos]` (L84, L282–283, L402–403; also Delta.lean:331/370, Eisenstein.lean:474/542): a public `@[simp] lemma resToImagAxis_of_pos (ht : 0 < t) : F.resToImagAxis t = F ⟨I * t, _⟩` and `resToImagAxis_of_nonpos` would replace every unfolding.
- The private `_add_apply/_mul_apply/_smul_apply` should be public `@[simp]`, with the missing companions `_neg`, `_sub`, `_pow`, `_zero`, `_one`, `_const` (neg is re-proved inline at L130; `Real.const` unfolds by hand at L118).
- Two names for one function (`ResToImagAxis F` vs `F.resToImagAxis`, L32/L38) plus two simp lemmas relating them (L40, L43): keep only `Function.resToImagAxis`.
- `Pos.const` (L163) lacks `@[fun_prop]` unlike all siblings; `Differentiable` (L71) carries `@[fun_prop]` but has a non-dischargeable side condition `0 < t`.
- Section comment L112–114 is formatted as a docstring on `Real.const`.

### Junk candidates
- Unused anywhere (in-file and project-wide): `ResToImagAxis.Differentiable` (L72), `SlashActionS` (L90), `Real.zero` (L121), `Real.sub` (L139), `Real.pow` (L157), `Pos.add` (L171), `Pos.smul` (L184), `Pos.pow` (L190), `EventuallyPos` and all seven `EventuallyPos.*` lemmas (L68, L197–248), `Real.eq_real_part` (L251), `cuspForm_rpow_mul_resToImagAxis_tendsto_zero` (L316), `tendsto_rpow_mul_resToImagAxis_of_fourier_shift` (L375) (hence also `isBigO_atImInfty_of_fourier_shift`, `tendsto_rpow_mul_resToImagAxis_of_isBigO_exp`, `isBigO_resToImagAxis_of_isBigO_atImInfty`, `tendsto_rpow_mul_of_isBigO_exp` — the whole decay section L258–382 has no external consumer), `Real.im_eq_zero_at` (L385), `Pos.re_pos_at` (L391), `tendsto_resToImagAxis_of_tendsto_atImInfty` (L397).
- Dead hypotheses: `_hc` (L277), `_hn₀`, `_hc` (L346).
- The `resToImagAxis_apply` simp lemma (L43) duplicates `resToImagAxis_eq_resToImagAxis` (L40).

### Moral duplicates within this batch
- The three closure families `Real.{add,mul,smul,pow,one,const}` / `Pos.{…}` / `EventuallyPos.{…}` share one skeleton each; `EventuallyPos.*` = `Pos.*` with `Filter.Eventually` threading.
- `isBigO_resToImagAxis_of_isBigO_atImInfty` (L277) and `tendsto_resToImagAxis_of_tendsto_atImInfty` (L397): same `comp tendsto_ofComplex_I_mul_atTop` + `congr'` skeleton (one for `=O`, one for `Tendsto`).
- `Real.im_eq_zero_at` (L385) / `Pos.re_pos_at` (L391): identical bodies.
- `ResToImagAxis.SlashActionS` (L90) re-derives from `modular_slash_S_apply` what mathlib's `slash_S_apply` states.

### Generalization notes
- `resToImagAxis_smul_apply`, `Real.smul`, `Pos.smul`, `EventuallyPos.smul` are stated for `c : ℝ`; the `_apply` lemma holds for any scalar action compatible with `ℂ` (`c : ℂ` too), and `Real.smul` for real `c` is the special case `Real.mul (Real.const c)`.
- `tendsto_rpow_mul_of_isBigO_exp` holds for `g : ℝ → E` into any normed space (only `IsBigO.mul`/`trans_tendsto` and the real kernel are used); stated for ℂ.
- `cuspForm_rpow_mul_resToImagAxis_tendsto_zero` is stated for `Γ(n)` but the proof only needs some positive period in `Γ.strictPeriods` — it holds for any `Γ` with `0 < h ∈ Γ.strictPeriods` (mathlib's `exp_decay_atImInfty` generality).
- `isBigO_atImInfty_of_fourier_shift`: `0 < n₀` and `0 < c` are not used; `n₀ = 0` gives boundedness.
