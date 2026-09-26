# Inventory: XYin/PhD/ModularFunctions/Congruence.lean  (150 lines)

Modular functions on `Γ₀(N)`: restriction of a `ModularFunction` to a subgroup, the fact that every SL₂(ℤ)-transform of a `Γ₀(N)`-invariant weight-0 function has period `N` (via conjugating `T^N` into `Γ₀(N)`), the resulting meromorphy of the period-`N` cusp functions, and a constructor `ofGamma0CuspData` from raw data (normal form + invariance + period-`N` cusp meromorphy). Bridges the period-free bundled definition to the period-`N` q-expansion data used in Cox/ModularFunction/CuspData.lean.

## Declarations

### `def ModularFunction.restrict`
- **Type**: `{Γ Γ'} (f : ModularFunction Γ) (h : Γ' ≤ Γ) : ModularFunction Γ'`
- **What**: a modular function for Γ is one for any subgroup Γ'.
- **How**: same `toFun`; invariance restricted; `meromorphic'` unchanged; growth via `IsCusp.mono` (mathlib) + `bdd_at_cusps`.
- **Hypotheses**: `Γ' ≤ Γ`.
- **Uses from project**: `ModularFunction`, `ModularFunction.bdd_at_cusps`
- **Used by**: `coe_restrict`
- **Visibility**: public
- **Lines**: 23–30
- **Notes**: used by Cox/ModularFunction/CuspData.lean:75,80. Mathlib has no `ModularForm.restrict` (searched `restrict` in the decl index for ModularForms; none).

### `theorem ModularFunction.coe_restrict`
- **Type**: `(f : ModularFunction Γ) (h : Γ' ≤ Γ) : (f.restrict h : ℍ → ℂ) = f`
- **What**: restriction does not change the function.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `restrict`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 32–34
- **Notes**: `@[simp]`; unused project-wide.

### `lemma ModularFunction.periodic_comp_ofComplex_of_vadd` (private)
- **Type**: `{f : ℍ → ℂ} {h : ℝ} (hf : ∀ τ, f (h +ᵥ τ) = f τ) : Periodic (f ∘ ofComplex) (h : ℂ)`
- **What**: translation invariance on ℍ gives periodicity of the `ofComplex`-extension on all of ℂ.
- **How**: case split on `0 < z.im`; positive case via `ofComplex_apply_of_im_pos` and `coe_vadd`; nonpositive case both sides are the junk value (`ofComplex_apply_of_im_nonpos`).
- **Hypotheses**: `f (h +ᵥ τ) = f τ` for all `τ`.
- **Uses from project**: []
- **Used by**: `periodic_comp_sl2_of_gamma0_invariant`
- **Visibility**: private
- **Lines**: 36–48, proof body ≈ 11 lines
- **Notes**: near-verbatim copy of the proof of mathlib's `SlashInvariantFormClass.periodic_comp_ofComplex` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:120–130`) with the `vAdd_apply_of_mem_strictPeriods` step abstracted — the general lemma should be upstreamed and the mathlib one derived from it.

### `lemma ModularFunction.conjugate_T_pow_mem_Gamma0` (private)
- **Type**: `(N : ℕ+) (γ : SL(2, ℤ)) : γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 (N : ℕ)`
- **What**: conjugates of `T^N` lie in `Γ₀(N)`.
- **How**: explicit `(1,0)`-entry computation: `SL2_inv_expl`, `ModularGroup.coe_T_zpow`, `Matrix.mul_apply`, `Fin.sum_univ_two`, `ring` gives `-N·(γ 1 0)²`, then `Gamma0_mem` and `simp` (mod `N`).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `periodic_comp_sl2_of_gamma0_invariant`
- **Visibility**: private
- **Lines**: 50–65, proof body ≈ 14 lines
- **Notes**: alternative route: `T^N ∈ Γ(N)`, `Gamma_normal` (`Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean:62`) and `Γ(N) ≤ Γ₀(N)` avoid the matrix computation.

### `theorem ModularFunction.periodic_comp_sl2_of_gamma0_invariant`
- **Type**: `(N : ℕ+) {f : ℍ → ℂ} (hinv : ∀ γ : Gamma0 N, f ∣[(0:ℤ)] (γ : SL(2,ℤ)) = f) (γ : SL(2,ℤ)) : Periodic (fun z : ℂ ↦ f (γ • ofComplex z)) (N : ℂ)`
- **What**: every SL₂(ℤ)-transform of a `Γ₀(N)`-invariant weight-0 function has period `N`; no analytic hypotheses.
- **How**: `δ := γ T^N γ⁻¹ ∈ Γ₀(N)` (`conjugate_T_pow_mem_Gamma0`), invariance under `δ` (`SL_slash_apply`), `modular_T_zpow_smul` turns `T^N • τ` into `N +ᵥ τ`, then `periodic_comp_ofComplex_of_vadd`.
- **Hypotheses**: `Γ₀(N)`-invariance of `f` (weight 0).
- **Uses from project**: `conjugate_T_pow_mem_Gamma0`, `periodic_comp_ofComplex_of_vadd`
- **Used by**: `periodic_comp_sl2_gamma0`, `ofGamma0CuspData`
- **Visibility**: public
- **Lines**: 67–84, proof body ≈ 13 lines
- **Notes**: used by Cox/ModularFunction/CuspData.lean:64.

### `theorem ModularFunction.periodic_comp_sl2_gamma0`
- **Type**: `(N : ℕ+) (f : ModularFunction (Gamma0 N)) (γ : SL(2,ℤ)) : Periodic (fun z : ℂ ↦ f (γ • ofComplex z)) (N : ℂ)`
- **What**: bundled version of the previous lemma.
- **How**: apply it with invariance from `f.slash_action_eq'`.
- **Hypotheses**: none.
- **Uses from project**: `periodic_comp_sl2_of_gamma0_invariant`, `ModularFunction`
- **Used by**: `cuspFunction_gamma0`
- **Visibility**: public
- **Lines**: 86–92
- **Notes**: —

### `theorem ModularFunction.cuspFunction_gamma0`
- **Type**: `(N : ℕ+) (f : ModularFunction (Gamma0 N)) (γ : SL(2,ℤ)) : MeromorphicAt (cuspFunction (N : ℝ) (fun τ ↦ f (γ • τ))) 0`
- **What**: the period-`N` cusp function of every SL₂(ℤ)-transform of a `Γ₀(N)` modular function is meromorphic at 0.
- **How**: `mapGL ℝ γ • ∞` is a cusp of `Γ₀(N)` (`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`, `isCusp_SL2Z_iff'`), rewrite `f ∣[0] γ` as `f (γ • ·)` (`SL_slash_apply`), feed the period from `periodic_comp_sl2_gamma0` to `ModularFunction.meromorphicAt_cuspFunction`.
- **Hypotheses**: none (`NeZero N` built locally).
- **Uses from project**: `periodic_comp_sl2_gamma0`, `ModularFunction.meromorphicAt_cuspFunction`, `ModularFunction`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 94–111, proof body ≈ 15 lines
- **Notes**: used by Cox/ModularFunction/CuspData.lean:70. Contains the `hslash` fragment (103–105).

### `def ModularFunction.ofGamma0CuspData`
- **Type**: `(N : ℕ+) (f : ℍ → ℂ) (hf : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet) (hinv : ∀ γ : Gamma0 N, f ∣[0] γ = f) (hcusp : ∀ γ : SL(2,ℤ), MeromorphicAt (cuspFunction N (fun τ ↦ f (γ • τ))) 0) : ModularFunction (Gamma0 N)`
- **What**: constructor of a `Γ₀(N)` modular function from normal form, invariance and period-`N` cusp meromorphy at every integral cusp.
- **How**: `meromorphic'` via `MeromorphicField.meromorphicNFOn_iff_exists`; growth: cusp of `Γ₀(N)` ⇒ cusp of SL₂(ℤ) (`IsCusp.mono`, `Subgroup.map_le_range`) ⇒ `γ • ∞`; `OnePoint.isOfExponentialGrowthAt_iff` + `isOfExponentialGrowth_of_meromorphicAt_cuspFunction` with the period from `periodic_comp_sl2_of_gamma0_invariant`.
- **Hypotheses**: as in the type.
- **Uses from project**: `ModularFunction`, `MeromorphicField.meromorphicNFOn_iff_exists`, `OnePoint.isOfExponentialGrowthAt_iff`, `IsOfExponentialGrowth`, `isOfExponentialGrowth_of_meromorphicAt_cuspFunction`, `periodic_comp_sl2_of_gamma0_invariant`
- **Used by**: `coe_ofGamma0CuspData`
- **Visibility**: public
- **Lines**: 113–140, body ≈ 20 lines
- **Notes**: used by Cox/ModularFunction/LevelJ.lean. `bdd_at_cusps'` (126–140) repeats the JInvariant.lean:48–54 skeleton and the `hslash` fragment (132–134).

### `theorem ModularFunction.coe_ofGamma0CuspData`
- **Type**: `… : (ofGamma0CuspData N f hf hinv hcusp : ℍ → ℂ) = f`
- **What**: the constructed function is `f`.
- **How**: `rfl`.
- **Hypotheses**: as above.
- **Uses from project**: `ofGamma0CuspData`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 142–148
- **Notes**: `@[simp]`; unused project-wide.

## File Summary
- Total declarations: 9 (2 defs, 7 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none (`periodic_comp_sl2_of_gamma0_invariant` used by 2)
- Unused declarations (not used by anything in this file): `coe_restrict`, `cuspFunction_gamma0` (used by Cox), `coe_ofGamma0CuspData`
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations
### Mathlib API candidates
- `periodic_comp_ofComplex_of_vadd` (36–48) generalises mathlib's `SlashInvariantFormClass.periodic_comp_ofComplex` (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:120`) — identical proof; upstream as `UpperHalfPlane.periodic_comp_ofComplex_of_forall_vadd`.
- `conjugate_T_pow_mem_Gamma0` (50–65): 14-line matrix computation replaceable by `CongruenceSubgroup.Gamma_normal` (`CongruenceSubgroups.lean:62`) + `T^N ∈ Γ(N)` + `Γ(N) ≤ Γ₀(N)`.
- `cuspFunction_gamma0` uses `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` (`Cusps.lean:147`) and `isCusp_SL2Z_iff'` (`:133`) correctly.
### Missing API / repeated patterns
- `hslash : (f ∣[(0:ℤ)] γ) = fun τ ↦ f (γ • τ) := by ext τ; simp [SL_slash_apply]` appears at 103–105 and 132–134 (and implicitly JInvariant.lean:52–53, Cox/ModularPolynomial/Construction.lean:273): add `ModularForm.SL_slash_zero : f ∣[(0:ℤ)] γ = fun τ ↦ f (γ • τ)` (funext form of mathlib `SL_slash_apply`, `SlashActions.lean:162`).
- `simpa only [Function.comp_def, ofReal_natCast] using periodic_comp_sl2_of_gamma0_invariant N _ γ` at 106–107 and 138–139: state the lemma directly as `Periodic ((f ∣[0] γ) ∘ ofComplex) (N : ℝ)` to match the consumers.
- `bdd_at_cusps'` skeleton duplicated with JInvariant.lean — see the proposed `isOfExponentialGrowthAt_of_forall_SL2Z` lemma (GrowthAtCusp.md).
### Junk candidates
- `coe_restrict` (32), `coe_ofGamma0CuspData` (142): unused project-wide `rfl` simp lemmas.
- `periodic_comp_sl2_gamma0` (86): only used once in-file; Cox uses the `_of_gamma0_invariant` form.
### Moral duplicates within this batch
- `periodic_comp_sl2_gamma0` at `N = 1` is `JInvariant.j_periodic` for `f = j`.
- `ofGamma0CuspData.bdd_at_cusps'` ≈ `jModularFunction.bdd_at_cusps'` (JInvariant.lean:48–54).
### Generalization notes
- `periodic_comp_sl2_of_gamma0_invariant` only needs `T^N`-conjugate-invariance; it holds for any subgroup containing `Γ(N)` (or any subgroup for which `γ T^N γ⁻¹ ∈ Γ` for all `γ ∈ SL₂(ℤ)`), i.e. for every congruence subgroup of level `N`, not just `Γ₀(N)`.
- `ofGamma0CuspData` needs the cusp data only at the cusps of `Γ₀(N)` (finitely many `γ` up to `Γ₀(N)`), not at every `γ ∈ SL(2,ℤ)`; the stronger hypothesis is harmless because the conclusion is invariant.
