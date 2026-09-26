# Cleanup report — `XYin/PhD/Modularforms/` (worker "mf", 2026-09-26)

## 1. Final gate

`lake build` in SB (both default targets `XYin`, `XYinTest`):

```
✔ [3710/3711] Built XYin (4.4s)
Build completed successfully (3711 jobs).
```

Only warning in the owned set: `DimensionFormulas.lean:25` "declaration uses `sorry`" (the kept
`dim_gen_cong_levels`). All other warnings of the build are pre-existing (Tactic2 / XYinTest header
linters, replayed). Log: `SB/.scratch/build_final.log`.

## 2. Files (lines before → after)

| File | Before | After |
|---|---|---|
| `AtImInfty.lean` | 27 | 23 |
| `Delta.lean` | 408 | 108 |
| `DimensionFormulas.lean` | 200 | 27 (sorry only) |
| `E2.lean` | 109 | 49 |
| `Eisenstein.lean` | 692 | 210 |
| `ForMathlib_Cusps.lean` | 21 | 37 (header + docstrings) |
| `ResToImagAxis.lean` | 403 | 434 (docs, simp API, reality helpers) |
| `SlashActionAuxil.lean` | 287 | 251 |
| `clog_arg_lems.lean` | 94 | 61 |
| `multipliable_lems.lean` | 81 | 36 |
| deleted: `BigO` 61, `Eisensteinqexpansions` 155, `IsCuspForm` 152, `NormNumI` 205, `Summability/Basic` 206, `Summability/QExpansion` 296, `Summability/Reciprocal` 297, `csqrt` 57, `equivs` 46, `eta` 81, `exp_lems` 29, `iteratedderivs` 72, `qExpansion_lems` 113, `summable_lems` 16, `tsumderivWithin` 138, `upperhalfplane` 17 | 1941 | 0 |
| **Total** | **4263** | **1236** |

`XYin.lean`: removed the 13 import lines of the deleted modules (Summability/* were only reached via
`summable_lems`). Nothing outside the owned set was edited (checked with `diff -rq` against SB.base).

## 3. Done items

### Whole-file deletions (all verified: no use outside the folder; build is the judge)
- `BigO` (= `EisensteinSeries.linear_inv_isBigO_right/left`), `eta` (1:1 mathlib `Discriminant.lean`
  `logDeriv_eta_comp_eq_logDeriv_csqrt_eta` / `eta_comp_eq_csqrt_I_inv`), `csqrt` (= `Complex.sqrt`),
  `equivs` (= `Equiv.neg ℤ` …; carried a `Mathlib.Tactic` import), `upperhalfplane`
  (= `im_pnat_div_pos`), `exp_lems` (= `norm_exp_two_pi_I_lt_one`), `iteratedderivs`,
  `tsumderivWithin`, `Summability/{Basic,QExpansion,Reciprocal}` (mathlib `derivWithin_tsum`,
  `qExpansion_identity_pnat`, `E2/Transform` `δ`/`G2Term`, …), `summable_lems` (facade),
  `NormNumI` (vendored `norm_numI`, never invoked), `IsCuspForm` (= mathlib `CuspFormSubmodule`;
  its consumers `Delta_E4_E6_aux`, `modularForm_normalise`, DimensionFormulas were dead),
  `qExpansion_lems` (after relocating `qExpansion_ext` and the `FunLike` instance, see below),
  `Eisensteinqexpansions` (dead `gammaSetN`/`EQ*` block = `gammaSetDivGcdEquiv`…;
  `standardcongruencecondition` inlined as `0`; project `E`/`E_k_q_expansion` replaced by mathlib
  `ModularForm.E`/`q_expansion_bernoulli`).
- `DimensionFormulas`: every proved lemma was a Γ(1)-transport of mathlib
  `LevelOne/DimensionFormula.lean`; only the `sorry` `dim_gen_cong_levels` kept (statement unchanged:
  `hΓ : Γ.index ≠ 0` is equivalent to `[Γ.FiniteIndex]`, so no restatement), with a docstring/TODO.

### `Delta.lean` (408 → 108)
- `Delta` is now `CuspForm.discriminant.copy Δ Δ_eq_discriminant Gamma_one_coe_eq_SL`
  (mathlib's own device for `ModularForm.E`); `Delta z = Δ z` stays `rfl`, type unchanged.
  This removed `Discriminant_SIF`, `Discriminant_T/S_invariant`, `Discriminant_zeroAtImInfty`,
  the hand `holo'` proof and the use of `slashaction_generators_GL2R`.
- `Δ_ne_zero` from `discriminant_ne_zero`; `delta_eq_discriminant` (private) → public
  `Δ_eq_discriminant`; new `coe_Delta`.
- Deleted dead block :64–149 (incl. global `instance natPosSMul : SMul ℕ+ ℍ`,
  `atImInfy_pnat_mono`, …), `Δ_periodic`, `Δ_S_transform`, `DiscriminantProductFormula`,
  `Delta_isTheta_rexp`, `CuspForm_apply`, `div_Delta_is_SIF`, `CuspForm_div_Discriminant(+_apply,
  _Add)` (= `CuspForm.divDiscriminant`/`discriminantEquiv`), `cexp_aux1..5`,
  `Complex.im_finset_prod/pow_eq_zero_of_im_eq_zero`.
- Imaginary-axis block re-proved via one new lemma `Δ_resToImagAxis` (Δ(it) = ↑(real product));
  `Delta_imag_axis_real`, `re_ResToImagAxis_Delta_eq_real_prod` are now 1-liners;
  `tprod_pos_nat_im` generalised from `z : ℍ` to `{t} (ht : 0 < t)` (its only use).
- Imports: dropped `SlashActionAuxil`, `clog_arg_lems`, `eta`, `multipliable_lems`, `NormNumI`,
  `ForMathlib_Cusps`, `QExpansion`; now `Discriminant` + `ResToImagAxis`.

### `Eisenstein.lean` (692 → 210)
- Deleted: rank-one helpers, `E4_eq/E6_eq/E4_apply/E6_apply`, `E₄/E₆_periodic`, `E₄/E₆_S_transform`,
  dead `variable`s, φ block (9 decls), cusp-function utilities (`cuspfunc_lim_coef`,
  `summable_zero_pow`, `tsum_zero_pow`, `cuspfunc_Zero`, `modfom_q_exp_cuspfunc`,
  `qParam_surj_onto_ball`, `q_exp_unique`, `deriv_mul_eq`), `auxasdf`, `sigma_bound`, `Ek_q`,
  `qexpsummable`, `Ek_q_exp(_zero)`, `E4/E6_q_exp_zero/_one`, `E4_pow_q_exp_one`,
  `antidiagonal_one`, `Complex.I_pow_six`, `bernoulli'_five` (= `bernoulli'_eq_zero_of_odd`),
  `E4E6_coeff_zero_eq_zero`, `Delta_E4_E6_aux`, `Delta_cuspFuntion_eq`, `Delta_ne_zero`, `asdf`,
  `diffwithinat_prod_1`, `Ek_ne_zero`, `E4/E6_ne_zero`, `modularForm_normalise`,
  `PowerSeries.coeff_add`, `neg_two_pi_I_pow_even_real`, `exp_imag_axis_arg`,
  `E₄_isBoundedAtImInfty`, `E₂_mul_E₄_isBoundedAtImInfty`, stale comments.
- `E₄`, `E₆`: same type; body `(1/2 : ℂ) • eisensteinSeriesMF _ 0` (inlined
  `standardcongruencecondition := 0`; all downstream `rfl` bridges still hold).
- `Delta_q_one_term` via `coe_Delta` + `discriminant_qExpansion_coeff_one`.
- `E_even_imag_axis_real` restated for mathlib `ModularForm.E hk` (`hk : 3 ≤ k` in ℕ) and re-proved
  from `EisensteinSeries.q_expansion_bernoulli` (the old proof needed `E_k_q_expansion`, `a33`,
  `sigma_bound`, ζ(k)/(-2πi)^k realness; now the constant is rational): 55 → 12 lines.
  `E₄/E₆_imag_axis_real` unchanged statements (defeq transport).
- `E₂_imag_axis_real` re-proved from mathlib `E2_eq_tsum_cexp` (45 → 8 lines).
- `norm_tsum_logDeriv_expo_le`: inlined the deleted `tsum_pnat_coe_mul_geometric` via
  `tsum_zero_pnat_eq_tsum_nat` + `tsum_coe_mul_geometric_of_norm_lt_one`, `tsum_div_const`.
- `bernoulli'_six`: proof no longer needs `bernoulli'_five` (uses `bernoulli'_eq_zero_of_odd`).
- Relocated here from `qExpansion_lems`: `qExpansion_ext` (used at `link.lean:250`) and the global
  `instance : FunLike (ℍ → ℂ) ℍ ℂ` (load-bearing, see §6).
- Re-exports `Mathlib.Tactic.NormNum.BigOperators` (load-bearing for `Cox/LevelThree.lean:67`,
  previously reached through `equivs.lean`'s `import Mathlib.Tactic`).

### `E2.lean` (109 → 49)
- Deleted the renames `G₂`, `E₂`, `D₂`, `D₂_apply`, `D2_one/mul/inv/T/S`, `G2_q_exp`,
  `G2_periodic`, `G₂_transform`, `E₂_slash_transform`, `tsum_eq_tsum_sigma`; `E₂_transform` folded
  into `E₂_S_transform`.
- Kept (now about mathlib `EisensteinSeries.E2`): `E₂_S_transform`, `E₂_eq`, `E₂_periodic`
  (new 3-line proof, no longer needs `SlashActionAuxil`).

### `SlashActionAuxil.lean` (287 → 251)
- Deleted `modular_slash_S_apply` (→ `SlashInvariantForm.slash_S_apply`, used in ResToImagAxis),
  `SL2Z_generate` (= `SL2Z_generators.symm`), `slashaction_generators`
  (= `slash_action_generators`), `slashaction_generators_SL2Z` (= `slash_action_generators_SL2Z`),
  `slashaction_generators_GL2R` (only user was Delta), private unused `α_zpow_one_zero`, unused
  local notation `GL(n,R)⁺`, `CStarAlgebra.Classes` import, stale theta-function docstring.
- Kept the Γ(2) chain (`α`, `β`, `negI`, `Γ2_c_eq_zero`, `Γ2_reduce_row/col`, `Γ2_descent`,
  `Γ2_generate`, `slashaction_generators'`, `slashaction_generators_Γ2`, `modular_slash_negI_of_even`,
  …) and `modular_slash_T_apply`; added header/module doc/docstrings; replaced 3 flexible
  `simp; decide` by `simp only [...]; decide`.
- The file is no longer imported by anything except `XYin.lean` (so root-level `α`/`β` no longer
  leak into the jFunction/Cox import closure).

### `ResToImagAxis.lean` (403 → 434)
- Unified the duplicate definitions: `Function.resToImagAxis` is now the definition; deleted
  `ResToImagAxis` (capital def) and the rfl simp lemmas `resToImagAxis_eq_resToImagAxis`,
  `resToImagAxis_apply`.
- New `@[simp]` `Function.resToImagAxis_of_pos`, `_of_nonpos`; private `_add/_mul/_smul_apply` made
  public `@[simp]` (namespace `Function`).
- `@[fun_prop]` added on `ResToImagAxis.Pos.const`; `tendsto_ofComplex_I_mul_atTop` made public.
- `modular_slash_S_apply` → `SlashInvariantForm.slash_S_apply`; dropped dead hypotheses
  (`_hc` of `isBigO_resToImagAxis_of_isBigO_atImInfty`, `_hn₀ _hc` of
  `isBigO_atImInfty_of_fourier_shift`, `hc` of `tendsto_rpow_mul_resToImagAxis_of_fourier_shift`).
- New reality helpers (used by Delta/Eisenstein): `Complex.ofReal_tprod`,
  `Complex.im_tsum_eq_zero_of_im_eq_zero`, `cexp_two_pi_I_mul_I_mul`; moved and generalised
  `Complex.im_tprod_eq_zero_of_im_eq_zero` (any index type, no `Multipliable` hypothesis).
- Import `SlashActionAuxil` → `Mathlib.NumberTheory.ModularForms.Identities`.

### `multipliable_lems.lean` (81 → 36)
- Deleted `Complex.summable_nat_multipliable_one_add` (= `multipliable_one_add_of_summable`),
  `term_ne_zero`, `ball_pow_ne_1`, `multipliable_lt_one` (= `multipliable_one_sub_pow`),
  `MultipliableEtaProductExpansion(_pnat)`, `tprod_ne_zero`
  (≈ `tprod_one_add_ne_zero_of_summable`), `Multipliable_pow` (= `Multipliable.pow`),
  `MultipliableDeltaProductExpansion_pnat`, `tprod_pow` (= `Multipliable.tprod_pow`).
- Kept `hasProd_le_nonneg`, `HasProd.le_one_nonneg` (generalised ℕ → any `ι`); renamed the
  misnamed `one_le_tprod_nonneg` → `tprod_le_one_of_nonneg` (no users anywhere).
- Import `Summability.Basic` → `Mathlib.Topology.Algebra.InfiniteSum.Real`.

### `clog_arg_lems.lean` (94 → 61)
- `arg_pow_aux` re-proved from mathlib `arg_pow_coe_angle` (33 → 8 lines); its hypothesis
  `x ≠ 0` turned out unnecessary and was dropped.
- `eventually_arg_pow` made public (and simplified); `arg_pow`, `arg_pow2` deleted;
  `clog_pow`/`clog_pow2` unified into filter-generic `eventually_clog_pow`; `log_summable_pow`
  generalised ℕ → any index type; `one_add_abs_half_ne_zero` no longer needed (deleted).
- Boilerplate imports (`Algebra.Order.Ring.Star`, `CStarAlgebra.Classes`, `Tactic.Cases`, …) removed.

### `AtImInfty.lean`, `ForMathlib_Cusps.lean`
- AtImInfty: kept `Filter.eventually_atImInfty`; deleted `Filter.tendsto_im_atImInfty`
  (= `tendsto_comap`) and `ne_zero_of_tendsto_ne_zero` (unused); dropped `Tannery` import.
- ForMathlib_Cusps: unchanged statements; header, module doc, docstrings.
- All surviving files now carry the copyright header + module docstring; `fun x =>` → `fun x ↦`.

## 4. New public API

- `Δ_eq_discriminant : Δ = ModularForm.discriminant` (was private `delta_eq_discriminant`)
- `coe_Delta : ⇑Delta = ModularForm.discriminant`
- `Δ_resToImagAxis (ht : 0 < t) : Δ.resToImagAxis t = ↑(rexp (-2πt) * ∏' n, (1 - rexp (-(2π(n+1)t)))^24)`
- `Function.resToImagAxis_of_pos / _of_nonpos` (@[simp]); `_add_apply / _mul_apply / _smul_apply`
  (@[simp], previously private)
- `Complex.ofReal_tprod (f : ι → ℝ) : ↑(∏' i, f i) = ∏' i, (f i : ℂ)` (unconditional)
- `Complex.im_tsum_eq_zero_of_im_eq_zero (f : ι → ℂ) (h : ∀ i, (f i).im = 0) : (∑' i, f i).im = 0`
- `cexp_two_pi_I_mul_I_mul (t : ℝ) : cexp (2π I (I t)) = rexp (-2πt)`
- `tendsto_ofComplex_I_mul_atTop : Tendsto (fun t ↦ ofComplex (I t)) atTop atImInfty` (was private)
- `eventually_arg_pow` (was private), `eventually_clog_pow` (filter-generic)
- `tprod_le_one_of_nonneg` (renamed from `one_le_tprod_nonneg`)

External API preserved with unchanged names/types: `Δ`, `Delta`, `Delta_apply`, `Delta_eq_eta_pow`,
`Δ_ne_zero`, `Delta_boundedfactor`, `E₄`, `E₆`, `bernoulli'_six`, `Delta_q_one_term`,
`zero_at_cusps_of_zero_at_infty`, `qExpansion_ext` (moved to Eisenstein.lean, on link's import path),
plus the global `FunLike (ℍ → ℂ) ℍ ℂ` instance.

## 5. Kept on purpose (genuine, currently unused)

`E₂_S_transform`, `E₂_eq`, `E₂_periodic`, `E₂_isBoundedAtImInfty`, `norm_tsum_logDeriv_expo_le(_of_norm_le)`,
`norm_exp_two_pi_I_le_exp_neg_two_pi`, `E_even_imag_axis_real`, `E₄/E₆/E₂_imag_axis_real`,
`E4_q_exp`, `E6_q_exp` (explicit 240σ₃ / −504σ₅; public twins of private lemmas in Deltaqexpansions),
`Delta_imag_axis_real/_pos`, `re_ResToImagAxis_Delta_eq_real_prod`, `tprod_pos_nat_im`,
`Complex.im_tprod_eq_zero_of_im_eq_zero`, all of `ResToImagAxis.lean`, the Γ(2) chain
(`Γ2_generate`, `slashaction_generators_Γ2`, …), `modular_slash_T_apply`, `arg_pow_aux`,
`eventually_arg_pow`, `eventually_clog_pow`, `log_summable_pow`, `hasProd_le_nonneg` family,
`Filter.eventually_atImInfty`, `bounded_at_cusps_of_bounded_at_infty`, `dim_gen_cong_levels` (sorry).

## 6. Deferred / follow-ups (need edits outside the owned set)

1. Global `instance : FunLike (ℍ → ℂ) ℍ ℂ` (now in `Eisenstein.lean`) is load-bearing: removing it
   makes `jFunction/jfunction.lean:197-201` time out (`UpperHalfPlane.qExpansion_coeff_unique
   (f := deltaShiftedQSeries)` — the lemma is generic over `[FunLike F ℍ ℂ]`); also used at
   `Cox/CoxMatrices/LaurentExpansion.lean:241` (`qExpansion_coeff_unique g …`). To delete it,
   those call sites need a local instance or a plain-function uniqueness lemma.
2. `Cox/LevelThree.lean:67` (`ring_nf` closing `∑ x : Fin 0, 0`) relies on
   `Mathlib.Tactic.NormNum.BigOperators`, re-exported from `Eisenstein.lean`; LevelThree should import
   it directly, then drop the re-export.
3. `qExpansion_tactic/link.lean:250`: inline `qExpansion_ext` as `congrArg (qExpansion 1) h`; then
   delete `qExpansion_ext`.
4. `jFunction/Deltaqexpansions.lean:41-52`: private `E4/E6_qExpansion_coeff_aux` duplicate
   `E4_q_exp`/`E6_q_exp` → `congr_fun E4_q_exp n`.
5. `Deltaqexpansions.lean:272-275`, `Cox/LatticeJ.lean:216-218, 266`: re-derive `⇑Delta =
   discriminant` by hand → use `coe_Delta`/`Δ_eq_discriminant`; LatticeJ's root-level
   `Delta_eq_E4_E6` (:215) belongs in `Eisenstein.lean` (cannot be added there now: name clash).
6. Γ(1) → 𝒮ℒ migration of `Delta`/`E₄`/`E₆` (retarget jfunction/Qj/link/LatticeJ to
   `CuspForm.discriminant`, `ModularForm.E₄/E₆`) — out of scope per task.
7. Naming hygiene (style renames, deferred): root-level `α`, `β`, `negI` and
   `ModularGroup.modular_negI_*` in SlashActionAuxil; `Filter.eventually_atImInfty` →
   `UpperHalfPlane.eventually_atImInfty`; `E₂_*` lemmas now about `EisensteinSeries.E2`
   (mathlib-style `EisensteinSeries.E2_S_smul`, …); `bernoulli'_six` → next to mathlib's
   `bernoulli'_four`; lowercase file names `clog_arg_lems`, `multipliable_lems`.
8. Upstream candidates: `bernoulli'_six`, `E₂_S_transform`, `E₂_eq`, `E₂_isBoundedAtImInfty`,
   `norm_tsum_logDeriv_expo_le`, `Complex.ofReal_tprod`, `Complex.im_tsum/tprod_eq_zero_of_im_eq_zero`,
   `arg_pow_aux`, `hasProd_le_nonneg`, `Filter.eventually_atImInfty`, `modular_slash_T_apply`,
   `Γ2_generate`.
9. Not done (optional polish): `α_zpow_val`/`β_zpow_val` share one induction (step5 H7);
   `ResToImagAxis.EventuallyPos` could be an `∀ᶠ … atTop` predicate (changes the definition).

## 7. Perf (kernel-computation files downstream; `lake env lean F`, wall clock, 2 runs)

| File | Before | After |
|---|---|---|
| `qExpansion_tactic/link.lean` | 5.67 s | 5.48 / 5.70 s |
| `jFunction/qexp_coeffs.lean` | 5.32 s | 5.31 / 5.30 s |
| `Cox/LevelThree.lean` | 12.22 s | 12.29 / 12.31 s |

`qExpansion_tactic/Qj.lean` does not import the folder (unaffected). No file got slower.
