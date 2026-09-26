# Worker report: `sorry` (fill `dim_gen_cong_levels`), 2026-09-26

## 1. Final build
`lake build` (targets `XYin`, `XYinTest`) in SB:
```
info: XYinTest/qExpansion_tactic/Examples.lean:53:19: [qexp time: 19ms]
Build completed successfully (3714 jobs).
```
`grep -rnw sorry SB/XYin SB/XYinTest SB/XYin.lean SB/XYinTest.lean` -> 0 hits.
`#print axioms` for every new declaration and for `dim_gen_cong_levels`:
`[propext, Classical.choice, Quot.sound]` only. No new warnings in owned files.

## 2. Files
| file | before | after |
|---|---|---|
| `XYin/PhD/Modularforms/DimensionFormulas.lean` | 27 lines (1 `sorry`) | 29 lines (0 `sorry`) |
| `XYin/PhD/Modularforms/SturmBound.lean` | new | 260 lines |
| `XYin.lean` | 25 imports | 26 imports (`+ import XYin.PhD.Modularforms.SturmBound`) |

Both Modularforms files keep the module-system layout (`module`, `public import`,
`@[expose] public section`). `SturmBound.lean` imports only Mathlib
(`...ModularForms.LevelOne.DimensionFormula`, `...ModularForms.NormTrace`); no project imports, so
no import-cycle risk. `DimensionFormulas.lean` now imports `SturmBound` (nothing else in the project
imports `DimensionFormulas`).

## 3. Done
* **`dim_gen_cong_levels` filled** with name and statement unchanged:
  `lemma dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
     FiniteDimensional ℂ (ModularForm Γ k)` — proof: `have : Γ.FiniteIndex := ⟨hΓ⟩; inferInstance`
  (via the new general instance, using mathlib's `IsArithmetic` instance for finite-index subgroups
  and `HasDetOne (Γ.map (mapGL ℝ))`). Module docstring updated (no longer "still open").
* Route (as suggested): Sturm bound for arithmetic `Γ` by norming down to level one.
  1. vanishing of the first `n` coefficients of `qExpansion h f` => `f = O(exp(-2πn·im τ/h))`
     (`HasFPowerSeriesAt.isBigO_sub_partialSum_pow` on the cusp function, composed with
     `qParam_tendsto_atImInfty`);
  2. `ModularForm.norm 𝒮ℒ f = O(f)` at `∞` (split off the `⟦1⟧` factor of `coe_norm` with
     `Finset.mul_prod_erase`; other factors are `ModularForm.translate f r⁻¹`, bounded at `∞` via
     `IsCusp.of_isFiniteRelIndex_conj`; `IsBigO.finsetProd`);
  3. `F = O(exp(-2πr·im τ/h))` => coefficients `j < r` vanish (interval-integral formula
     `qExpansion_coeff_eq_intervalIntegral` + `norm_integral_le_of_norm_le_const`, let `im τ → ∞`);
  4. combine with `ModularForm.sturm_bound_levelOne` and `ModularForm.norm_eq_zero_iff`;
  5. `q`-expansion coefficient map `ModularForm Γ k →ₗ[ℂ] Fin n → ℂ` is injective for
     `n > h ⌊k d / 12⌋` => `FiniteDimensional.of_injective`.

## 4. New public API (`XYin/PhD/Modularforms/SturmBound.lean`)
* `UpperHalfPlane.exp_decay_atImInfty_of_coeff_eq_zero (hh : 0 < h) (hfper) (hfhol) (hfbdd)
  (hn : ∀ j < n, (qExpansion h f).coeff j = 0) : f =O[atImInfty] fun τ ↦ exp (-2π n τ.im / h)`
* `UpperHalfPlane.qExpansion_coeff_eq_zero_of_exp_decay (hh) (hfper) (hfhol) (hfbdd)
  (hf : f =O[atImInfty] fun τ ↦ exp (-2π r τ.im / h)) (hj : j < r) : (qExpansion h f).coeff j = 0`
* `ModularFormClass.exp_decay_atImInfty_of_coeff_eq_zero`,
  `ModularFormClass.qExpansion_coeff_eq_zero_of_exp_decay` (protected; same, for
  `[ModularFormClass F Γ k]` and a positive strict period `h ∈ Γ.strictPeriods`)
* `SlashInvariantForm.isBoundedAtImInfty_quotientFunc [ModularFormClass F 𝒢 k]
  [𝒢.IsFiniteRelIndex ℋ] [Fact (IsCusp ∞ ℋ)] (q) : IsBoundedAtImInfty (quotientFunc f q)`
* `ModularForm.coe_norm_isBigO [ModularFormClass F 𝒢 k] [𝒢.IsFiniteRelIndex ℋ]
  [ℋ.HasDetPlusMinusOne] [Fact (IsCusp ∞ ℋ)] : ⇑(ModularForm.norm ℋ f) =O[atImInfty] f`
* `ModularFormClass.sturm_bound [ModularFormClass F Γ k] [Γ.IsArithmetic] (hh : 0 < h)
  (hΓ : h ∈ Γ.strictPeriods) (f : F) (hn : ↑((k * Γ.relIndex 𝒮ℒ).toNat / 12) * h < n)
  (hf : ↑n ≤ (qExpansion h f).order) : ⇑f = 0`
* `ModularForm.sturm_bound [Γ.IsArithmetic] (hh) (hΓ) (f : ModularForm Γ k) (hn) (hf) : f = 0`
* `Subgroup.relIndex_map_mapGL_range (Γ : Subgroup SL(2, ℤ)) :
  (Γ : Subgroup (GL (Fin 2) ℝ)).relIndex 𝒮ℒ = Γ.index`
* `ModularForm.sturm_bound_of_finiteIndex {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hh)
  (hΓ : h ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods) (f : ModularForm Γ k)
  (hn : ↑((k * Γ.index).toNat / 12) * h < n) (hf : ↑n ≤ (qExpansion h f).order) : f = 0`
* `instance ModularForm.instFiniteDimensional [Γ.IsArithmetic] [Γ.HasDetOne] :
  FiniteDimensional ℂ (ModularForm Γ k)` (fires e.g. for `Γ.FiniteIndex` images and `Gamma N`)

## 5. Kept on purpose
Nothing deleted.

## 6. Deferred / follow-ups
* None required outside the owned set. Possible future additions (not done, to avoid
  gold-plating): `FiniteDimensional ℂ (CuspForm Γ k)`; an `ℝ`-linear version for arithmetic `Γ`
  without `HasDetOne`; upstreaming the new API to mathlib (it only depends on mathlib).
* Memory notes / `PROJECT_OVERVIEW.md` still describe `dim_gen_cong_levels` as the open `sorry`;
  the orchestrator may want to update them after merging.

## 7. Perf
No kernel-computation file touched. `lake env lean XYin/PhD/Modularforms/SturmBound.lean`: ~7 s
wall (≈4.5 s elaboration); `DimensionFormulas.lean`: ~6 s wall (≈3 s build). No heartbeat options.
