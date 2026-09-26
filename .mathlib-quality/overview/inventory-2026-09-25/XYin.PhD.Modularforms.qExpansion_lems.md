# Inventory: XYin/PhD/Modularforms/qExpansion_lems.lean  (113 lines)

Grab-bag of thin wrappers around mathlib's `ModularForm.qExpansion` / `cuspFunction` API (multiplicativity, smul, powers, vanishing) specialised to `Γ(n)` and level 1, plus a few `iteratedDeriv` one-liners and — dangerously — a global `instance : FunLike (ℍ → ℂ) ℍ ℂ`. Imported by `IsCuspForm.lean` (hence by `Eisenstein.lean`, `jLevelN.lean`, …); the only live consumers are `qExpansion_mul_coeff`, `qExpansion_smul2` (Eisenstein.lean:395,424) and `qExpansion_ext` (qExpansion_tactic/link.lean:250). No file header/docstring.

## Declarations

### `theorem modform_tendto_ndhs_zero`
- **Type**: `{k : ℤ} (n : ℕ) [ModularFormClass F Γ(n) k] [inst : NeZero n] : Tendsto (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (↑n) x)) (𝓝[≠] 0) (𝓝 (cuspFunction n f 0))`
- **What**: As q → 0 (q ≠ 0), f(invQParam q) tends to the value of the cusp function at 0.
- **How**: continuity of `cuspFunction n f` at 0 from `ModularFormClass.analyticAt_cuspFunction_zero` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:153`), then `Tendsto.congr'` with `Function.Periodic.cuspFunction_eq_of_nonzero` (`Mathlib/Analysis/Complex/Periodic.lean:119`) on `𝓝[≠] 0`.
- **Hypotheses**: n ≠ 0; f a modular form of level Γ(n).
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 21–30, proof body ≈ 7 lines
- **Notes**: = mathlib `Function.Periodic.tendsto_nhds_zero (analyticAt_cuspFunction_zero f _ _).continuousAt` (`Periodic.lean:139`). The binder `(n : ℕ)` shadows the section variable `n` (line 17). Dead project-wide.

### `theorem derivWithin_mul2`
- **Type**: `(f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s) (hd : DifferentiableOn ℂ g s) : s.restrict (derivWithin (fun y => f y * g y) s) = s.restrict (derivWithin f s * g + f * derivWithin g s)`
- **What**: Product rule for `derivWithin`, stated as equality of restrictions to s.
- **How**: `ext` + mathlib `derivWithin_fun_mul` (`Mathlib/Analysis/Calculus/Deriv/Mul.lean:278`).
- **Hypotheses**: f, g differentiable on s.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 32–38, proof body ≈ 3 lines
- **Notes**: Junk — `derivWithin_fun_mul` is stronger (pointwise, needs only `DifferentiableWithinAt` at the point). Dead project-wide.

### `lemma iteratedDerivWithin_mul'`
- **Type**: `(f g : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s) (x : ℂ) (hx : x ∈ s) (m : ℕ) (hf : ContDiffOn ℂ ⊤ f s) (hg : ContDiffOn ℂ ⊤ g s) : iteratedDerivWithin m (f * g) s x = ∑ i ∈ Finset.range m.succ, (m.choose i) * (iteratedDerivWithin i f s x) * (iteratedDerivWithin (m - i) g s x)`
- **What**: Leibniz rule for the m-th derivative of a product on an open set.
- **How**: mathlib `iteratedDerivWithin_mul` (`Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean:278`) with `ContDiffWithinAt` obtained from `ContDiffOn.of_le`.
- **Hypotheses**: s open, f, g smooth on s.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 40–47, proof body ≈ 2 lines
- **Notes**: Wrapper; mathlib's needs only `ContDiffWithinAt 𝕜 m` at x and `UniqueDiffOn`. Dead project-wide.

### `lemma iteratedDeriv_eq_iteratedDerivWithin`
- **Type**: `(n : ℕ) (f : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s) (z : ℂ) (hz : z ∈ s) : iteratedDeriv n f z = iteratedDerivWithin n f s z`
- **What**: On an open set, `iteratedDeriv` = `iteratedDerivWithin`.
- **How**: `(iteratedDerivWithin_of_isOpen hs hz).symm`.
- **Hypotheses**: s open, z ∈ s.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 49–51, proof body ≈ 1 line
- **Notes**: Exact symm of mathlib `iteratedDerivWithin_of_isOpen` (`IteratedDeriv/Defs.lean:318`, stated as `EqOn`). Dead project-wide.

### `lemma qExpansion_mul_coeff`
- **Type**: `(a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b) [hn : NeZero n] : qExpansion n (f.mul g) = qExpansion n f * qExpansion n g`
- **What**: The q-expansion (at width n) of a product of level-Γ(n) modular forms is the product of q-expansions.
- **How**: mathlib `ModularForm.qExpansion_mul` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:584`) with `hh : 0 < n` and `hΓ : n ∈ Γ(n).strictPeriods` discharged by `simp`.
- **Hypotheses**: n ≠ 0.
- **Uses from project**: []
- **Used by**: unused in file; Eisenstein.lean:395
- **Visibility**: public
- **Lines**: 53–58, proof body ≈ 3 lines
- **Notes**: Misnamed (`_coeff` but it is about the whole power series). Live.

### `lemma IteratedDeriv_smul`
- **Type**: `(a : ℂ) (f : ℂ → ℂ) (m : ℕ) : iteratedDeriv m (a • f) = a • iteratedDeriv m f`
- **What**: Scalars pull out of iterated derivatives (as functions).
- **How**: `funext` + mathlib `iteratedDeriv_const_smul_field` (`IteratedDeriv/Lemmas.lean:349`, `@[simp]`).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 63–66, proof body ≈ 2 lines
- **Notes**: Capitalised name violates convention; the pointwise mathlib simp lemma makes this redundant. Dead project-wide.

### `lemma qExpansion_smul2`
- **Type**: `(a : ℂ) (f : ModularForm Γ(n) k) [NeZero n] : (a • qExpansion n f) = (qExpansion n (a • f))`
- **What**: q-expansion commutes with scalar multiplication.
- **How**: `(ModularForm.qExpansion_smul … a f).symm` (`QExpansion.lean:556`).
- **Hypotheses**: n ≠ 0.
- **Uses from project**: []
- **Used by**: unused in file; Eisenstein.lean:424
- **Visibility**: public
- **Lines**: 68–71, proof body ≈ 2 lines
- **Notes**: Wrapper stated in the reversed (non-simp) direction. Live.

### `instance instFunLikeUpperHalfPlaneComplex : FunLike (ℍ → ℂ) ℍ ℂ`
- **Type**: `FunLike (ℍ → ℂ) ℍ ℂ` with `coe := id`, `coe_injective' := id`
- **What**: Makes every plain function `ℍ → ℂ` a `FunLike` so that `[FunLike F ℍ ℂ]`-generic lemmas apply to it.
- **How**: identity coercion.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: implicitly by `qExpansion_ext` (75), `cuspFunction_congr_funLike` (79), `qExpansion_ext2` (84) when instantiated at plain functions
- **Visibility**: public (global, unscoped)
- **Lines**: 73
- **Notes**: Anonymous instance. Mathlib deliberately has NO `FunLike (α → β) α β` instance (see the comment at `Mathlib/ModelTheory/Basic.lean:792`: "there is no instance of `FunLike (M → N) M N`"); adding one globally means every `⇑f` on a plain function elaborates through this instance, risks instance diamonds with `Pi` coercions and slows/perturbs elaboration in every downstream file (`IsCuspForm`, `Eisenstein`, `jLevelN`, …). Mathlib's own `qExpansion`/`cuspFunction` already take `f : ℍ → ℂ` directly (`QExpansion.lean:76,166`), so the instance is not needed for them. Should be `scoped`/`local` at most, or removed.

### `lemma qExpansion_ext`
- **Type**: `(f g : ℍ → ℂ) (h : f = g) : qExpansion 1 f = qExpansion 1 g`
- **What**: q-expansion respects equality of functions.
- **How**: `rw [h]`.
- **Hypotheses**: f = g.
- **Uses from project**: []
- **Used by**: unused in file; qExpansion_tactic/link.lean:250
- **Visibility**: public
- **Lines**: 75–77, proof body ≈ 1 line
- **Notes**: `congrArg (qExpansion 1) h` / `h ▸ rfl`. Live but trivial.

### `lemma cuspFunction_congr_funLike`
- **Type**: `{α β} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (n : ℕ) (f : α) (g : β) (h : ⇑f = ⇑g) : cuspFunction n f = cuspFunction n g`
- **What**: Cusp functions of two FunLike objects with equal coercions agree.
- **How**: `congrArg (cuspFunction n) h`.
- **Hypotheses**: ⇑f = ⇑g.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 79–82, proof body ≈ 1 line
- **Notes**: `congrArg` in disguise. Dead project-wide.

### `lemma qExpansion_ext2`
- **Type**: `{α β} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (f : α) (g : β) (h : ⇑f = ⇑g) : qExpansion 1 f = qExpansion 1 g`
- **What**: Same for q-expansions at level 1.
- **How**: `congrArg (qExpansion 1) h`.
- **Hypotheses**: ⇑f = ⇑g.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 84–86, proof body ≈ 1 line
- **Notes**: Dead project-wide.

### `lemma IteratedDeriv_zero_fun`
- **Type**: `(n : ℕ) (z : ℂ) : iteratedDeriv n (fun _ : ℂ => (0 : ℂ)) z = 0`
- **What**: All iterated derivatives of the zero function vanish.
- **How**: `iteratedDeriv_fun_const_zero`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 88–90, proof body ≈ 1 line
- **Notes**: `@[simp]`; comment "--generalize this away from ℂ". Exact duplicate of mathlib `iteratedDeriv_fun_const_zero` (`IteratedDeriv/Defs.lean:370`, already `@[simp]`, already general) — typechecked in scratch. Dead project-wide.

### `lemma iteratedDeriv_const_eq_zero`
- **Type**: `(m : ℕ) (hm : 0 < m) (c : ℂ) : iteratedDeriv m (fun _ : ℂ => c) = fun _ : ℂ => 0`
- **What**: Positive-order derivatives of a constant vanish.
- **How**: `funext` + mathlib `iteratedDeriv_const` (`IteratedDeriv/Defs.lean:357`: `= if n = 0 then c else 0`) + `hm.ne'`.
- **Hypotheses**: m > 0.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 92–95, proof body ≈ 2 lines
- **Notes**: Function-level restatement of `iteratedDeriv_const`. Dead project-wide.

### `lemma qExpansion_pow`
- **Type**: `(f : ModularForm Γ(1) k) (n : ℕ) : qExpansion 1 ((((DirectSum.of (ModularForm Γ(1)) k) f) ^ n) (n * k)) = (qExpansion 1 f) ^ n`
- **What**: q-expansion of the n-th power (in the graded ring ⊕_k M_k(Γ(1))) is the n-th power of the q-expansion.
- **How**: `exact_mod_cast qExpansion_of_pow` (`QExpansion.lean:638`) at h = 1.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 97–101, proof body ≈ 3 lines
- **Notes**: Wrapper. Dead project-wide.

### `lemma qExpansion_injective`
- **Type**: `[hn : NeZero n] (f : ModularForm Γ(n) k) : qExpansion n f = 0 ↔ f = 0`
- **What**: A level-Γ(n) modular form vanishes iff its q-expansion does.
- **How**: mathlib `ModularForm.qExpansion_eq_zero_iff` (`QExpansion.lean:589`).
- **Hypotheses**: n ≠ 0.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 103–106, proof body ≈ 2 lines
- **Notes**: Misnamed (it is `_eq_zero_iff`, not injectivity; actual injectivity would be `qExpansion n f = qExpansion n g ↔ f = g`). Dead project-wide.

### `abbrev SlashInvariantFormClass.cuspFunction`
- **Type**: `(h : ℝ) (f : UpperHalfPlane → ℂ) : ℂ → ℂ := UpperHalfPlane.cuspFunction h f`
- **What**: Namespaced alias of mathlib's `UpperHalfPlane.cuspFunction`.
- **How**: abbrev.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file (the `cuspFunction` at 23–24, 81–82 resolves to `UpperHalfPlane.cuspFunction`, this abbrev is declared later and is `protected`)
- **Visibility**: protected
- **Lines**: 110–111
- **Notes**: `noncomputable`. grep for `SlashInvariantFormClass.cuspFunction` over XYin: no hits. Dead project-wide; likely a leftover from a mathlib rename.

## File Summary
- Total declarations: 16 (0 defs, 1 abbrev, 14 lemmas/theorems, 1 instance)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): all 16 (nothing in the file uses anything else in the file); project-wide live: `qExpansion_mul_coeff` (Eisenstein.lean:395), `qExpansion_smul2` (Eisenstein.lean:424), `qExpansion_ext` (qExpansion_tactic/link.lean:250); the `FunLike` instance is potentially load-bearing for elaboration downstream
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `modform_tendto_ndhs_zero` (21) = `Function.Periodic.tendsto_nhds_zero` (`Mathlib/Analysis/Complex/Periodic.lean:139`) applied to `(ModularFormClass.analyticAt_cuspFunction_zero f _ _).continuousAt`.
- `derivWithin_mul2` (32) = `derivWithin_fun_mul` (`Deriv/Mul.lean:278`); `iteratedDerivWithin_mul'` (40) = `iteratedDerivWithin_mul` (`IteratedDeriv/Lemmas.lean:278`); `iteratedDeriv_eq_iteratedDerivWithin` (49) = `iteratedDerivWithin_of_isOpen` (`Defs.lean:318`).symm; `IteratedDeriv_smul` (63) = `iteratedDeriv_const_smul_field` (`Lemmas.lean:349`); `IteratedDeriv_zero_fun` (88) = `iteratedDeriv_fun_const_zero` (`Defs.lean:370`, verified); `iteratedDeriv_const_eq_zero` (92) = `iteratedDeriv_const` (`Defs.lean:357`).
- `qExpansion_mul_coeff` (53) = `ModularForm.qExpansion_mul` (`QExpansion.lean:584`); `qExpansion_smul2` (68) = `ModularForm.qExpansion_smul` (:556); `qExpansion_pow` (97) = `qExpansion_of_pow` (:638); `qExpansion_injective` (103) = `ModularForm.qExpansion_eq_zero_iff` (:589). All four only fix `h = n`, `Γ = Γ(n)` and discharge `0 < n` / `n ∈ Γ(n).strictPeriods` by `simp` — a single `Γ(n)`-specialisation lemma `strictPeriods_Gamma (n) [NeZero n] : (n : ℝ) ∈ Γ(n).strictPeriods` would let callers use mathlib directly.
- `qExpansion_ext`, `cuspFunction_congr_funLike`, `qExpansion_ext2` (75–86) = `congrArg`.
- `SlashInvariantFormClass.cuspFunction` (110) = `UpperHalfPlane.cuspFunction` (`QExpansion.lean:76`).
### Missing API / repeated patterns
- `(Nat.cast_pos.mpr (Nat.pos_of_neZero n)) (by simp)` discharging `hh`/`hΓ` appears at 26, 57–58, 70–71, 106 → the `strictPeriods_Gamma` lemma above, or a `Fact`/instance.
- Two `variable` blocks (17, 60–61) both bind `F`; the second (`{𝕜} [NontriviallyNormedField 𝕜] {F} [NormedAddCommGroup F] [NormedSpace 𝕜 F]`) is used by nothing.
### Junk candidates
- Dead project-wide: `modform_tendto_ndhs_zero`, `derivWithin_mul2`, `iteratedDerivWithin_mul'`, `iteratedDeriv_eq_iteratedDerivWithin`, `IteratedDeriv_smul`, `cuspFunction_congr_funLike`, `qExpansion_ext2`, `IteratedDeriv_zero_fun`, `iteratedDeriv_const_eq_zero`, `qExpansion_pow`, `qExpansion_injective`, `SlashInvariantFormClass.cuspFunction` — 12 of 16.
- The global `instance : FunLike (ℍ → ℂ) ℍ ℂ` (73): mathlib intentionally omits this; should be deleted or made `scoped`. Whether any downstream elaboration silently depends on it can only be settled by removing it and rebuilding (`IsCuspForm.lean`, `Eisenstein.lean`, `jLevelN.lean` `open SlashInvariantFormClass` and use FunLike-generic lemmas at 118–119 / 313–314).
- Spurious imports: `Mathlib.Analysis.CStarAlgebra.Classes` (3), `Mathlib.Data.Real.StarOrdered` (4), `Mathlib.Order.CompletePartialOrder` (6), `Mathlib.Tactic.Cases` (7). Unused opens: `MeasureTheory intervalIntegral` (11).
- Missing copyright header/docstring. CamelCase `IteratedDeriv_smul`, `IteratedDeriv_zero_fun`; misnamed `qExpansion_mul_coeff`, `qExpansion_injective`, `qExpansion_smul2`.
### Moral duplicates within this batch
- `qExpansion_ext` (75) vs `qExpansion_ext2` (84) vs `cuspFunction_congr_funLike` (79): three `congrArg`s.
- `IteratedDeriv_zero_fun` (88) vs `iteratedDeriv_const_eq_zero` (92): the former is the `c = 0` case of the latter (and of mathlib `iteratedDeriv_const`).
- `iteratedDeriv_eq_iteratedDerivWithin` (49) vs iteratedderivs.lean's inline `iteratedDerivWithin_of_isOpen` uses (30, 71) and tsumderivWithin.lean `der_iter_eq_der2` (85).
### Generalization notes
- `derivWithin_mul2`, `iteratedDerivWithin_mul'`, `iteratedDeriv_eq_iteratedDerivWithin`, `IteratedDeriv_smul`, `IteratedDeriv_zero_fun`, `iteratedDeriv_const_eq_zero`: all stated for `ℂ → ℂ` but the mathlib lemmas they wrap are for `𝕜 → F` over any `NontriviallyNormedField` — the file even declares those variables (60–61) and then doesn't use them.
- `qExpansion_mul_coeff`, `qExpansion_smul2`, `qExpansion_pow`, `qExpansion_injective`: hold for any `Γ` with `[Γ.HasDetPlusMinusOne]` and any `h ∈ Γ.strictPeriods`, as in mathlib; the `Γ(n)`, `h = n` specialisation is the only content.
