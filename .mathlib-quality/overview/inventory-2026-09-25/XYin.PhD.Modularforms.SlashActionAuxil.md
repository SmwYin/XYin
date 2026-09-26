# Inventory: XYin/PhD/Modularforms/SlashActionAuxil.lean  (287 lines)

Generators of `SL(2,ℤ)` (`S`, `T`) and of `Γ(2)` (`α = T²`, `β`, `−I`), a proof that `{α, β, −I}` generates `Γ(2)` (Euclidean descent on the `(1,0)` entry), pointwise formulas for the slash action by `S`, `T`, `−I`, and the "check invariance on generators" principle for slash actions. The file header says these were meant for showing `Θ₂⁴, Θ₃⁴, Θ₄⁴` are weight-2 forms for `Γ(2)`, but no Jacobi-theta development exists in the project; the only external consumers are `modular_slash_S_apply` (ResToImagAxis.lean:97), `modular_slash_T_apply` (E2.lean:60) and `slashaction_generators_GL2R` (Delta.lean:62).

## Declarations

### `local notation "GL(" n ", " R ")" "⁺"` (L25)
- **Type**: notation for `Matrix.GLPos (Fin n) R`
- **What**: `GL(n, R)⁺` abbreviation.
- **How**: `local notation`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: local
- **Lines**: 25
- **Notes**: dead notation (never used below).

### `local notation "Γ " n:100` (L26)
- **Type**: notation for `CongruenceSubgroup.Gamma n`
- **What**: `Γ 2` abbreviation (distinct from mathlib's scoped `Γ(2)`).
- **How**: `local notation`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: α, β, negI, Γ2_c_eq_zero, Γ2_odd_00, Γ2_even_10, Γ2_descent, Γ2_generate, slashaction_generators_Γ2
- **Visibility**: local
- **Lines**: 26
- **Notes**: mathlib provides `Γ(n)` (`open scoped CongruenceSubgroup`); a second spelling is confusing.

### `def α`
- **Type**: `Γ 2` (i.e. `↥(CongruenceSubgroup.Gamma 2)`)
- **What**: The matrix `[[1,2],[0,1]] = T²` as an element of `Γ(2)`.
- **How**: subtype constructor with `det = 1` by `simp` and membership by `simp; decide`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: α_eq_T_sq, β_eq_negI_mul_S_mul_α_inv_mul_S, α_zpow_val, α_zpow_one_zero, Γ2_c_eq_zero, Γ2_descent, Γ2_generate, slashaction_generators_Γ2
- **Visibility**: public
- **Lines**: 28
- **Notes**: root-namespace single-letter Greek name `α` — collides visually with the universal convention `{α : Type*}` in every importing file (ResToImagAxis, E2, Delta); should live in a namespace (`Gamma2.α`).

### `def β`
- **Type**: `Γ 2`
- **What**: `[[1,0],[2,1]]` as an element of `Γ(2)`.
- **How**: as for `α`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: β_eq_negI_mul_S_mul_α_inv_mul_S, β_zpow_val, Γ2_c_eq_zero, Γ2_descent, Γ2_generate, slashaction_generators_Γ2
- **Visibility**: public
- **Lines**: 30
- **Notes**: same naming hazard.

### `def negI`
- **Type**: `Γ 2`
- **What**: `−I = [[−1,0],[0,−1]]` as an element of `Γ(2)`.
- **How**: subtype constructor, `simp`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: β_eq_negI_mul_S_mul_α_inv_mul_S, modular_negI_sq, modular_negI_inv, modular_negI_smul, modular_slash_negI_of_even, Γ2_c_eq_zero, Γ2_descent, Γ2_generate, slashaction_generators_Γ2
- **Visibility**: public
- **Lines**: 32
- **Notes**: this is just `(-1 : Γ 2)` (mathlib uses `-1 ∈ Γ`, e.g. `ModularForm.eq_zero_of_neg_one_mem`, `Basic.lean:231`).

### `theorem α_eq_T_sq`
- **Type**: `α = ⟨T ^ 2, by simp [sq, T]; decide⟩`
- **What**: `α = T²`.
- **How**: `ext; simp [α, T, sq]`.
- **Hypotheses**: none.
- **Uses from project**: α
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 34
- **Notes**: unused anywhere; the RHS bakes a proof term into the statement.

### `theorem β_eq_negI_mul_S_mul_α_inv_mul_S`
- **Type**: `β = negI * S * α⁻¹ * S`
- **What**: `β = −S α⁻¹ S`.
- **How**: `ext; simp [β, S, α, negI]`.
- **Hypotheses**: none.
- **Uses from project**: β, negI, α
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 36
- **Notes**: unused anywhere. Note `S : SL(2,ℤ)` multiplied with elements of `Γ 2` — the statement only typechecks via coercions (elaborates in `SL(2,ℤ)`).

### `theorem ModularGroup.modular_negI_sq`
- **Type**: `negI ^ 2 = 1`
- **What**: `(−I)² = 1` in `Γ(2)`.
- **How**: `ext i j; fin_cases i <;> fin_cases j <;> rfl`.
- **Hypotheses**: none.
- **Uses from project**: negI
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 38–39
- **Notes**: unused anywhere; declared into mathlib's `ModularGroup` namespace.

### `theorem ModularGroup.modular_negI_inv`
- **Type**: `negI⁻¹ = negI`
- **What**: `−I` is its own inverse.
- **How**: `ext i j; simp [negI]`.
- **Hypotheses**: none.
- **Uses from project**: negI
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 41
- **Notes**: unused anywhere.

### `theorem modular_negI_smul`
- **Type**: `(z : ℍ) : negI.1 • z = z`
- **What**: `−I` acts trivially on ℍ.
- **How**: `specialLinearGroup_apply` (`MoebiusAction.lean:299`) + `simp [negI]`.
- **Hypotheses**: none.
- **Uses from project**: negI
- **Used by**: modular_slash_negI_of_even
- **Visibility**: public
- **Lines**: 49
- **Notes**: variables `f k z` from `variable` L45; mathlib proves `-1 • z = z` inline via `neg_smul, one_smul` (`Basic.lean:236`).

### `theorem modular_slash_negI_of_even`
- **Type**: `(f : ℍ → ℂ) (k : ℤ) (hk : Even k) : f ∣[k] negI.1 = f`
- **What**: For even weight, slashing by `−I` is the identity.
- **How**: `slash_action_eq'_iff` (`SlashActions.lean:190`), `modular_negI_smul`, `Even.neg_one_zpow`.
- **Hypotheses**: `k` even.
- **Uses from project**: negI, modular_negI_smul
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 51–52
- **Notes**: unused anywhere. No named mathlib lemma for `f ∣[k] (-1)`; mathlib computes it inline in `ModularForm.eq_zero_of_neg_one_mem` (`Basic.lean:231–236` via `slash_action_eqn''`, `denom_neg`, `denom_one`, `Odd.neg_one_zpow`).

### `theorem modular_slash_S_apply`
- **Type**: `(f : ℍ → ℂ) (k : ℤ) (z : ℍ) : (f ∣[k] S) z = f (UpperHalfPlane.mk (-z)⁻¹ z.im_inv_neg_coe_pos) * z ^ (-k)`
- **What**: `(f|_k S)(z) = f(−1/z)·z^{−k}`.
- **How**: `SL_slash_apply` (`SlashActions.lean:162`), `denom`, `modular_S_smul` (`MoebiusAction.lean:308`), `simp [S]`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file; externally ResToImagAxis.lean:97
- **Visibility**: public
- **Lines**: 54–56
- **Notes**: **exact duplicate of mathlib `SlashInvariantForm.slash_S_apply`** (`Mathlib/NumberTheory/ModularForms/Identities.lean:47`) — verified by scratch typecheck this session (`SlashInvariantForm.slash_S_apply f k z` closes this statement).

### `theorem modular_slash_T_apply`
- **Type**: `(f : ℍ → ℂ) (k : ℤ) (z : ℍ) : (f ∣[k] T) z = f ((1 : ℝ) +ᵥ z)`
- **What**: `(f|_k T)(z) = f(z+1)`.
- **How**: `SL_slash_apply`, `denom`, `modular_T_smul` (`MoebiusAction.lean:319`), `simp [T]`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file; externally E2.lean:60
- **Visibility**: public
- **Lines**: 58–59
- **Notes**: no named mathlib lemma (searched `slash_T_apply`, `T_slash`); composable in one line from `SL_slash_apply` + `modular_T_smul` + `denom` (as here). Reasonable ForMathlib candidate next to `slash_S_apply`.

### `theorem SL2Z_generate`
- **Type**: `(⊤ : Subgroup SL(2, ℤ)) = Subgroup.closure {S, T}`
- **What**: `SL(2,ℤ)` is generated by `S` and `T`.
- **How**: `SpecialLinearGroup.SL2Z_generators.symm` (`Mathlib/LinearAlgebra/Matrix/FixedDetMatrices.lean:271`).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: slashaction_generators_SL2Z
- **Visibility**: public
- **Lines**: 68–69
- **Notes**: pure `.symm` alias of a mathlib lemma.

### `private theorem α_zpow_val`
- **Type**: `(k : ℤ) : (α ^ k : SL(2, ℤ)).val = !![1, 2 * k; 0, 1]`
- **What**: Explicit matrix of `α^k`.
- **How**: `Int.induction_on`; `zpow_add`/`zpow_sub`, `SpecialLinearGroup.coe_mul`/`coe_inv`, `Matrix.adjugate_fin_two`, entrywise `fin_cases` + `ring`.
- **Hypotheses**: none.
- **Uses from project**: α
- **Used by**: α_zpow_one_zero, Γ2_c_eq_zero, Γ2_descent
- **Visibility**: private
- **Lines**: 72–81, body ≈ 9 lines
- **Notes**: docstring. Mathlib has `ModularGroup.coe_T_zpow : ↑(T ^ n) = !![1, n; 0, 1]` (in `Mathlib/NumberTheory/Modular.lean`); since `α = T²`, this is `coe_T_zpow (2*k)` — but `α_eq_T_sq` is never used to exploit that.

### `private theorem α_zpow_one_zero`
- **Type**: `(k : ℤ) : (α ^ k : SL(2, ℤ)).val 1 0 = 0`
- **What**: The `(1,0)` entry of `α^k` is 0.
- **How**: `simp [α_zpow_val]`.
- **Hypotheses**: none.
- **Uses from project**: α, α_zpow_val
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 84–85
- **Notes**: private AND unused — dead code.

### `private theorem β_zpow_val`
- **Type**: `(k : ℤ) : (β ^ k : SL(2, ℤ)).val = !![1, 0; 2 * k, 1]`
- **What**: Explicit matrix of `β^k`.
- **How**: same induction as `α_zpow_val` with `Matrix.mul_apply`.
- **Hypotheses**: none.
- **Uses from project**: β
- **Used by**: Γ2_descent
- **Visibility**: private
- **Lines**: 88–97, body ≈ 9 lines
- **Notes**: docstring; verbatim copy of `α_zpow_val`'s proof (transposed).

### `lemma Γ2_c_eq_zero`
- **Type**: `(A : Γ 2) (h : A.1 1 0 = 0) : A ∈ Subgroup.closure {α, β, negI}`
- **What**: An element of `Γ(2)` with lower-left entry 0 lies in the subgroup generated by `α, β, −I`.
- **How**: `Gamma_mem` (`CongruenceSubgroups.lean:50`) + `ZMod.intCast_zmod_eq_zero_iff_dvd` give `A₀₁ = 2k`; `det_fin_two` gives `A₀₀A₁₁ = 1`, so (`Int.mul_eq_one_iff_eq_one_or_neg_one`) `A = α^k` or `A = negI·α^{−k}` (checked entrywise via `α_zpow_val`); conclude by `Subgroup.zpow_mem`/`mul_mem`.
- **Hypotheses**: `A ∈ Γ(2)`, `A₁₀ = 0`.
- **Uses from project**: α, β, negI, α_zpow_val
- **Used by**: Γ2_generate
- **Visibility**: public
- **Lines**: 99–127, body ≈ 28 lines
- **Notes**: `erw` at L104; `simp_all` inside `fin_cases` at L116.

### `lemma Γ2_reduce_row`
- **Type**: `(a c : ℤ) (ha : Odd a) (hc : Even c) (hc0 : c ≠ 0) : ∃ n, |a + 2 * n * c| < |c|`
- **What**: Euclidean step: an odd `a` can be reduced modulo `2c` to something strictly smaller than `|c|` in absolute value.
- **How**: division with remainder `a = 2c·q + r`, `0 ≤ r < 2|c|` (`Int.mul_ediv_add_emod`, `Int.emod_nonneg`, `Int.emod_lt_abs`); case `r ≤ |c|` (strictness from `a` odd, `c` even via `grind`) or shift by one more multiple; `grind`/`abs_cases`.
- **Hypotheses**: `a` odd, `c` even, `c ≠ 0`.
- **Uses from project**: []
- **Used by**: Γ2_descent
- **Visibility**: public
- **Lines**: 129–140, body ≈ 11 lines
- **Notes**: pure integer arithmetic, `grind`-heavy. Core has balanced mod `Int.bmod` with `Int.le_bmod`/`Int.bmod_lt` (`Init/Data/Int/DivModLemmas.lean`) which packages "remainder in `(−m/2, m/2]`".

### `lemma Γ2_reduce_col`
- **Type**: `(a c : ℤ) (ha : Odd a) (hc : Even c) (ha0 : a ≠ 0) : ∃ m, |c + 2 * m * a| < |a|`
- **What**: Column analogue: even `c` reduced modulo `2a` below `|a|`.
- **How**: divide `c/2` by `a` (`Int.ediv_mul_add_emod`), get `|c/2 + m a| ≤ (|a|−1)/2`, double back using `Int.ediv_mul_cancel` for `2 ∣ c` and `2 ∣ |a|−1`; `nlinarith` with `abs_cases`.
- **Hypotheses**: `a` odd, `c` even, `a ≠ 0`.
- **Uses from project**: []
- **Used by**: Γ2_descent
- **Visibility**: public
- **Lines**: 142–158, body ≈ 16 lines
- **Notes**: `norm_num [abs_le] at *` + `nlinarith` — fragile.

### `private lemma Γ2_odd_00`
- **Type**: `(A : Γ 2) : Odd (A.val.val 0 0)`
- **What**: The top-left entry of a `Γ(2)` element is odd.
- **How**: `Gamma_mem`, `ZMod.intCast_eq_one_iff_odd`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: Γ2_descent
- **Visibility**: private
- **Lines**: 161–163
- **Notes**: docstring.

### `private lemma Γ2_even_10`
- **Type**: `(A : Γ 2) : Even (A.val.val 1 0)`
- **What**: The lower-left entry is even.
- **How**: `Gamma_mem`, `ZMod.intCast_zmod_eq_zero_iff_dvd` (via `erw`).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: Γ2_descent
- **Visibility**: private
- **Lines**: 166–168
- **Notes**: `erw`.

### `lemma Γ2_descent`
- **Type**: `(A : Γ 2) (h : A.1 1 0 ≠ 0) : ∃ (M : Γ 2), M ∈ Subgroup.closure {α, β, negI} ∧ |(M * A).1 1 0| < |A.1 1 0|`
- **What**: Left-multiplying by a word `β^m α^n` strictly decreases `|A₁₀|` when it is nonzero.
- **How**: `Γ2_reduce_row` (with `Γ2_odd_00`, `Γ2_even_10`) picks `n`, then `Γ2_reduce_col` picks `m`; `M = β^m * α^n`; the entry is computed with `α_zpow_val`, `β_zpow_val`, `Matrix.mul_apply`, `Fin.sum_univ_two`, and `ring_nf`.
- **Hypotheses**: `A₁₀ ≠ 0`.
- **Uses from project**: α, β, negI, Γ2_reduce_row, Γ2_reduce_col, Γ2_odd_00, Γ2_even_10, α_zpow_val, β_zpow_val
- **Used by**: Γ2_generate
- **Visibility**: public
- **Lines**: 170–187, body ≈ 17 lines
- **Notes**: none.

### `theorem Γ2_generate`
- **Type**: `(⊤ : Subgroup (Γ 2)) = Subgroup.closure {α, β, negI}`
- **What**: `Γ(2)` is generated by `α, β, −I`.
- **How**: Well-ordering: take `M` in the closure minimising `natAbs ((M*A)₁₀)` (`Nat.sInf_mem`); if positive, `Γ2_descent` contradicts minimality (`Nat.sInf_le`); if zero, `Γ2_c_eq_zero` puts `M*A` in the closure, hence `A`.
- **Hypotheses**: none.
- **Uses from project**: α, β, negI, Γ2_c_eq_zero, Γ2_descent
- **Used by**: slashaction_generators_Γ2
- **Visibility**: public
- **Lines**: 189–215, body ≈ 26 lines
- **Notes**: no mathlib analogue (searched `Gamma 2`, `Γ(2)`, `generators` in `Mathlib/NumberTheory/ModularForms/`, `Modular.lean`, `SpecialLinearGroup.lean`); this is a genuine, upstreamable result, but its only consumer (`slashaction_generators_Γ2`) is unused. `Nat.find`/`Nat.strong_induction_on` on `natAbs` would be simpler than `sInf`.

### `theorem slashaction_generators`
- **Type**: `(f : ℍ → ℂ) (G : Subgroup SL(2, ℤ)) (s : Set SL(2, ℤ)) (hG : G = Subgroup.closure s) (k : ℤ) : (∀ γ : G, f ∣[k] γ.1 = f) ↔ (∀ γ ∈ s, f ∣[k] γ = f)`
- **What**: Slash-invariance under a subgroup follows from invariance under a generating set.
- **How**: `Subgroup.closure_induction` with `SlashAction.slash_one`, `SlashAction.slash_mul` (and inverse step via `mul_inv_cancel`).
- **Hypotheses**: `G = closure s`.
- **Uses from project**: []
- **Used by**: slashaction_generators_SL2Z
- **Visibility**: public
- **Lines**: 220–235, body ≈ 13 lines
- **Notes**: docstring. **Mathlib now has `SlashInvariantForm.slash_action_generators`** (`Mathlib/NumberTheory/ModularForms/Identities.lean:54`) with the same proof, stated for `Γ : Subgroup (GL (Fin 2) ℝ)`, `s : Set (GL (Fin 2) ℝ)`; the `SL(2,ℤ)` version here transports through `SL_slash` + `MonoidHom.map_closure` as mathlib does in `slash_action_generators_SL2Z`.

### `theorem slashaction_generators'`
- **Type**: `(f : ℍ → ℂ) {G : Subgroup SL(2, ℤ)} (s : Set G) (hG : ⊤ = Subgroup.closure s) (k : ℤ) : (∀ γ : G, f ∣[k] γ.1 = f) ↔ (∀ γ ∈ s, f ∣[k] γ.1 = f)`
- **What**: Same principle with the generating set inside `G`.
- **How**: `Subgroup.closure_induction` inside `G`, `Subgroup.coe_mul`, `slash_mul`, `slash_one`.
- **Hypotheses**: `⊤ = closure s` in `G`.
- **Uses from project**: []
- **Used by**: slashaction_generators_Γ2
- **Visibility**: public
- **Lines**: 240–258, body ≈ 16 lines
- **Notes**: docstring; the goal order after `apply … ?_ ?_` is confusing (bullets L249–258 are not in source order).

### `theorem slashaction_generators_SL2Z`
- **Type**: `(f : ℍ → ℂ) (k : ℤ) (hS : f ∣[k] S = f) (hT : f ∣[k] T = f) : ∀ γ : SL(2, ℤ), f ∣[k] γ = f`
- **What**: `S`- and `T`-invariance imply full `SL(2,ℤ)`-invariance.
- **How**: `slashaction_generators` with `SL2Z_generate`, `rcases` on the two generators.
- **Hypotheses**: `S`, `T` invariance.
- **Uses from project**: slashaction_generators, SL2Z_generate
- **Used by**: slashaction_generators_GL2R
- **Visibility**: public
- **Lines**: 260–266, body ≈ 4 lines
- **Notes**: **= mathlib `SlashInvariantForm.slash_action_generators_SL2Z`** (`Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean:56`, same statement with `f k` implicit).

### `theorem slashaction_generators_GL2R`
- **Type**: `(f : ℍ → ℂ) (k : ℤ) (hS) (hT) : ∀ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1), f ∣[k] γ = f`
- **What**: `S`/`T`-invariance gives invariance under the image of `Γ(1)` in `GL(2,ℝ)`.
- **How**: `rintro γ ⟨A, hA, rfl⟩` + `slashaction_generators_SL2Z`.
- **Hypotheses**: as above.
- **Uses from project**: slashaction_generators_SL2Z
- **Used by**: unused in file; externally Delta.lean:62 (`slashaction_generators_GL2R Δ 12 Discriminant_S_invariant Discriminant_T_invariant`)
- **Visibility**: public
- **Lines**: 268–273, body 2 lines
- **Notes**: composable from mathlib's `slash_action_generators_SL2Z` + `Subgroup.mem_map`; Delta.lean's use mirrors mathlib `Discriminant.lean:239` exactly.

### `theorem slashaction_generators_Γ2`
- **Type**: `(f : ℍ → ℂ) (k : ℤ) (hα : f ∣[k] α.1 = f) (hβ : f ∣[k] β.1 = f) (hnegI : f ∣[k] negI.1 = f) : ∀ γ ∈ Subgroup.map (SpecialLinearGroup.mapGL ℝ) (Γ 2), f ∣[k] γ = f`
- **What**: Invariance under `α, β, −I` gives invariance under the image of `Γ(2)`.
- **How**: `Subgroup.mem_map`, `slashaction_generators'` with `Γ2_generate`.
- **Hypotheses**: as stated.
- **Uses from project**: α, β, negI, slashaction_generators', Γ2_generate
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 275–285, body ≈ 8 lines
- **Notes**: unused anywhere — the whole `Γ(2)` development (L28–36, 72–215, 240–258, 275–285) has no consumer.

## File Summary
- Total declarations: 27 (3 defs: α, β, negI; 24 lemmas/theorems; 0 instances) + 2 local notations
- Key API (used by 3+ others in the file): α (8), β (6), negI (9), α_zpow_val (3)
- Unused declarations (not used by anything in this file): α_eq_T_sq, β_eq_negI_mul_S_mul_α_inv_mul_S, ModularGroup.modular_negI_sq, ModularGroup.modular_negI_inv, modular_slash_negI_of_even, modular_slash_S_apply (ext. ResToImagAxis), modular_slash_T_apply (ext. E2), α_zpow_one_zero (private!), slashaction_generators_GL2R (ext. Delta), slashaction_generators_Γ2, local notation `GL(n,R)⁺`
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: Γ2_c_eq_zero 28, Γ2_generate 26)

## Observations

### Mathlib API candidates
- `modular_slash_S_apply` (L54) **is** `SlashInvariantForm.slash_S_apply` (`Mathlib/NumberTheory/ModularForms/Identities.lean:47`) — verified by scratch typecheck; replace the one use in ResToImagAxis.lean:97.
- `slashaction_generators` (L220) **is** `SlashInvariantForm.slash_action_generators` (`Identities.lean:54`) modulo `SL(2,ℤ)` vs `GL(2,ℝ)`; `slashaction_generators_SL2Z` (L260) **is** `SlashInvariantForm.slash_action_generators_SL2Z` (`LevelOne/Basic.lean:56`); `slashaction_generators_GL2R` (L268) is that plus `Subgroup.mem_map` (mathlib's own `Discriminant.lean:239` does exactly this for Δ). `SL2Z_generate` (L68) is `SpecialLinearGroup.SL2Z_generators.symm` (`Mathlib/LinearAlgebra/Matrix/FixedDetMatrices.lean:271`).
- `modular_slash_T_apply` (L58): no named mathlib lemma (searched `slash_T_apply`, `T_slash` in `ModularForms/` and `UpperHalfPlane/`); one-liner from `SL_slash_apply` (`SlashActions.lean:162`) + `modular_T_smul` (`MoebiusAction.lean:319`). ForMathlib candidate next to `slash_S_apply`.
- `modular_slash_negI_of_even` (L51): no named mathlib lemma; mathlib computes `f ∣[k] (-1)` inline in `ModularForm.eq_zero_of_neg_one_mem` (`Basic.lean:231`). A general `slash_neg_one : f ∣[k] (-1 : GL) = (-1)^k • f` would serve both.
- `α_zpow_val` (L72): `α = T²`, so it is `ModularGroup.coe_T_zpow (2*k)` (mathlib `Modular.lean`) after `α_eq_T_sq`; `β_zpow_val` similarly via conjugation by `S` (`β_eq_negI_mul_S_mul_α_inv_mul_S`) — both stated relations are proved but never exploited.
- `Γ2_reduce_row`/`Γ2_reduce_col` (L129–158): hand-rolled balanced Euclidean division; core `Int.bmod` with `Int.le_bmod`/`Int.bmod_lt` (`Init/Data/Int/DivModLemmas.lean`) gives a remainder in `(−m/2, m/2]` directly.
- `Γ2_generate` (L189): no mathlib analogue found (searched `Gamma 2`, `Γ(2)`, `closure {`, `generators` in `Mathlib/NumberTheory/ModularForms/`, `Mathlib/NumberTheory/Modular.lean`, `SpecialLinearGroup.lean`, `FixedDetMatrices.lean`) — genuinely new, upstreamable content, though currently unused.
- `negI` (L32) is `(-1 : Γ 2)`; mathlib phrases everything with `-1 ∈ Γ` (`HasDetOne`/`adjoinNegOne`, `ArithmeticSubgroups.lean:229–240`).

### Missing API / repeated patterns
- `α_zpow_val` (L72–81) and `β_zpow_val` (L88–97) are the same 9-line induction; one lemma `coe_zpow_of_unipotent` (or reuse `coe_T_zpow` + conjugation) collapses both.
- `slashaction_generators` and `slashaction_generators'` (L220–258) are the same closure-induction twice (set in `SL(2,ℤ)` vs set in `G`); mathlib's single `GL`-level lemma covers both after `Subgroup.map`.
- The closure `{α, β, negI}` membership facts `Subgroup.subset_closure (Set.mem_insert …)` are re-derived at L110–111, L124–125, L178–180 — three times.

### Junk candidates
- Unused anywhere: `α_eq_T_sq` (L34), `β_eq_negI_mul_S_mul_α_inv_mul_S` (L36), `ModularGroup.modular_negI_sq` (L38), `ModularGroup.modular_negI_inv` (L41), `modular_slash_negI_of_even` (L51), private `α_zpow_one_zero` (L84 — private and unused), `slashaction_generators_Γ2` (L275) and hence the entire Γ(2)-generation chain (`Γ2_c_eq_zero`, `Γ2_reduce_row/col`, `Γ2_odd_00`, `Γ2_even_10`, `Γ2_descent`, `Γ2_generate`, `slashaction_generators'`, `α`, `β`, `negI`) — ~190 of 287 lines have no consumer.
- Local notation `GL(n, R)⁺` (L25) is never used.
- The header docstring (L18–19) promises Jacobi theta applications that do not exist in the project (`grep -i theta` finds only this file and a comment in Delta.lean).
- Naming hazards: root-level `α`, `β`; theorems declared into mathlib's `ModularGroup` namespace (L38, L41).

### Moral duplicates within this batch
- `α_zpow_val` / `β_zpow_val`; `slashaction_generators` / `slashaction_generators'`; `modular_negI_sq` vs `modular_negI_inv` (both say `negI` is an involution).
- Across files: `modular_slash_S_apply` vs ResToImagAxis's `SlashActionS` (restates it on the axis); Delta.lean's `Discriminant_S_invariant`/`Discriminant_T_invariant` + `slashaction_generators_GL2R` (Delta.lean:49–62) reproduce mathlib `discriminant_S_invariant`/`discriminant_T_invariant` + `Discriminant.lean:239` verbatim.

### Generalization notes
- `slashaction_generators`/`'`: nothing uses `SL(2,ℤ)` beyond the `SlashAction` instance; mathlib's version is for arbitrary subgroups of `GL(2,ℝ)` — strictly more general.
- `modular_slash_negI_of_even`: holds for any `f`, any `k` even, for `-1 : GL(2,ℝ)`; the `Γ 2`-membership of `negI` is irrelevant.
- `Γ2_reduce_row/col`: pure ℤ facts; the parity hypotheses are only used for strictness (`r ≠ |c|`), i.e. they are the general "balanced remainder" statement specialised to modulus `2c`.
