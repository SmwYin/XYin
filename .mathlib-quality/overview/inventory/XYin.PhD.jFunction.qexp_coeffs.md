# XYin/PhD/jFunction/qexp_coeffs.lean
Project-internal imports: `XYin.PhD.qExpansion_tactic.link`

All declarations live at top level (no namespace). Throughout, `ramanujanTau`, `qjCoeffs`, `qj`, `j`, `Delta` are project definitions; `Delta_qexpansion`/`qj_qexpansion` are the certified integer power series computed by the project's q-expansion tactic infrastructure (`XYin.PhD.qExpansion_tactic.Qj`); `qExpansion`/`laurentqExpansion` are Mathlib's/the project's analytic q-expansions.

### `lemma ramanujanTau_one`
- **Type**: `ramanujanTau 1 = 1`
- **What**: The first Ramanujan tau value: τ(1) = 1 (coefficient of q in the q-expansion of Δ/(2π)¹²).
- **How**: Rewrites `ramanujanTau n` into the tactic-computed integer series via `ramanujanTau_link` and `Delta_qexpansion_coeff_eq`, then evaluates the resulting integer arithmetic by kernel reduction (`rfl`).
- **Hypotheses**: none.
- **Uses from project**: [`ramanujanTau`, `ramanujanTau_link`, `Delta_qexpansion_coeff_eq`, `Delta_qexpansion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 29–31, proof 2 lines
- **Notes**: none

### `lemma ramanujanTau_two`
- **Type**: `ramanujanTau 2 = -24`
- **What**: The second Ramanujan tau value: τ(2) = −24.
- **How**: Identical to `ramanujanTau_one`: rewrite with `ramanujanTau_link` and `Delta_qexpansion_coeff_eq`, then `rfl` kernel evaluation.
- **Hypotheses**: none.
- **Uses from project**: [`ramanujanTau`, `ramanujanTau_link`, `Delta_qexpansion_coeff_eq`, `Delta_qexpansion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 33–35, proof 2 lines
- **Notes**: none

### `lemma ramanujanTau_three`
- **Type**: `ramanujanTau 3 = 252`
- **What**: The third Ramanujan tau value: τ(3) = 252.
- **How**: Same route: `ramanujanTau_link`, `Delta_qexpansion_coeff_eq`, `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`ramanujanTau`, `ramanujanTau_link`, `Delta_qexpansion_coeff_eq`, `Delta_qexpansion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 37–39, proof 2 lines
- **Notes**: none

### `lemma qjCoeffs_eq_qjQExpansion_coeff_aux`
- **Type**: `(n : ℕ) : qjCoeffs n = qj_qexpansion.coeff n`
- **What**: The integer coefficients `qjCoeffs` of the regularized `j`-function `qj = e^{2πiτ}·j` (defined via the integrality certificate) agree with the tactic-computed integer power series `qj_qexpansion`, coefficientwise.
- **How**: Two-step comparison in ℂ: the complexification of `qjCoeffs n` equals the analytic `(qExpansion 1 qj).coeff n` by `coeTo_of_toIntegralPowerSeries` applied to `qj_isIntegralPowerSeries`, and the latter equals `(qj_qexpansion.coeff n : ℂ)` by the linking theorem `qj_qxp_coeff_link`; injectivity of ℤ → ℂ (`exact_mod_cast`) concludes.
- **Hypotheses**: none.
- **Uses from project**: [`qjCoeffs`, `qj_qexpansion`, `coeTo_of_toIntegralPowerSeries`, `qj_isIntegralPowerSeries`, `qj_qxp_coeff_link`, `qj`]
- **Used by**: `qjCoeffs_zero`, `qjCoeffs_one`, `qjCoeffs_two`, `qjCoeffs_three`, `qjCoeffs_four`
- **Visibility**: private
- **Lines**: 41–48, proof 6 lines
- **Notes**: none

### `lemma qjCoeffs_zero`
- **Type**: `qjCoeffs 0 = 1`
- **What**: The constant coefficient of `qj = e^{2πiτ}·j` is 1, i.e. `j` has a simple pole at ∞ with residue-normalization 1 (leading coefficient 1/q).
- **How**: Reduces to the certified series via `qjCoeffs_eq_qjQExpansion_coeff_aux` and `qj_qexpansion_coeff_eq`, then evaluates by `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`qjCoeffs`, `qjCoeffs_eq_qjQExpansion_coeff_aux`, `qj_qexpansion_coeff_eq`, `qj_qexpansion`]
- **Used by**: `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial`
- **Visibility**: public
- **Lines**: 50–52, proof 2 lines
- **Notes**: none

### `lemma Delta_qExpansion_coeff_two`
- **Type**: `(qExpansion 1 Delta).coeff 2 = -24`
- **What**: The q²-coefficient of the analytic q-expansion of the discriminant form Δ is −24 (= τ(2)).
- **How**: Rewrites the analytic coefficient into the integer series via the linking theorem `Delta_qxp_coeff_link`, evaluates `Delta_qexpansion.coeff 2 = −24` by `Delta_qexpansion_coeff_eq` plus `rfl`, and casts ℤ → ℂ.
- **Hypotheses**: none.
- **Uses from project**: [`Delta` (the project cusp form), `Delta_qxp_coeff_link`, `Delta_qexpansion`, `Delta_qexpansion_coeff_eq`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 54–58, proof 4 lines
- **Notes**: none

### `lemma Delta_qExpansion_coeff_three`
- **Type**: `(qExpansion 1 Delta).coeff 3 = 252`
- **What**: The q³-coefficient of the analytic q-expansion of Δ is 252 (= τ(3)).
- **How**: Same route as `Delta_qExpansion_coeff_two`: `Delta_qxp_coeff_link`, `Delta_qexpansion_coeff_eq`, `rfl`, cast.
- **Hypotheses**: none.
- **Uses from project**: [`Delta`, `Delta_qxp_coeff_link`, `Delta_qexpansion`, `Delta_qexpansion_coeff_eq`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 60–64, proof 4 lines
- **Notes**: none

### `lemma Delta_qExpansion_coeff_four`
- **Type**: `(qExpansion 1 Delta).coeff 4 = -1472`
- **What**: The q⁴-coefficient of the analytic q-expansion of Δ is −1472 (= τ(4)).
- **How**: Same route: `Delta_qxp_coeff_link`, `Delta_qexpansion_coeff_eq`, `rfl`, cast.
- **Hypotheses**: none.
- **Uses from project**: [`Delta`, `Delta_qxp_coeff_link`, `Delta_qexpansion`, `Delta_qexpansion_coeff_eq`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 66–70, proof 4 lines
- **Notes**: none

### `lemma Delta_qExpansion_coeff_five`
- **Type**: `(qExpansion 1 Delta).coeff 5 = 4830`
- **What**: The q⁵-coefficient of the analytic q-expansion of Δ is 4830 (= τ(5)).
- **How**: Same route: `Delta_qxp_coeff_link`, `Delta_qexpansion_coeff_eq`, `rfl`, cast.
- **Hypotheses**: none.
- **Uses from project**: [`Delta`, `Delta_qxp_coeff_link`, `Delta_qexpansion`, `Delta_qexpansion_coeff_eq`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 72–76, proof 4 lines
- **Notes**: none

### `lemma qj_qExpansion_coeff_one_aux`
- **Type**: `(qExpansion 1 qj).coeff 1 = 744`
- **What**: The q¹-coefficient of the analytic q-expansion of `qj` is 744, the celebrated constant term of `j`.
- **How**: Rewrites with `qj_qxp_coeff_link` into the certified integer series, evaluates `qj_qexpansion.coeff 1 = 744` via `qj_qexpansion_coeff_eq` and `rfl`, then casts.
- **Hypotheses**: none.
- **Uses from project**: [`qj`, `qj_qxp_coeff_link`, `qj_qexpansion`, `qj_qexpansion_coeff_eq`]
- **Used by**: `j_laurentQExpansion_coeff_zero`
- **Visibility**: private
- **Lines**: 78–82, proof 4 lines
- **Notes**: none

### `lemma qjCoeffs_one`
- **Type**: `qjCoeffs 1 = 744`
- **What**: The first integer coefficient of the regularized `j` is 744 (constant term of `j`'s Fourier expansion).
- **How**: Via `qjCoeffs_eq_qjQExpansion_coeff_aux` and `qj_qexpansion_coeff_eq`, then kernel evaluation `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`qjCoeffs`, `qjCoeffs_eq_qjQExpansion_coeff_aux`, `qj_qexpansion_coeff_eq`, `qj_qexpansion`]
- **Used by**: `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial`
- **Visibility**: public
- **Lines**: 84–86, proof 2 lines
- **Notes**: none

### `lemma qj_qExpansion_coeff_two_aux`
- **Type**: `(qExpansion 1 qj).coeff 2 = 196884`
- **What**: The q²-coefficient of the analytic expansion of `qj` is 196884 (the first Monstrous-Moonshine coefficient c(1) of `j`).
- **How**: Same route as `qj_qExpansion_coeff_one_aux`: `qj_qxp_coeff_link`, `qj_qexpansion_coeff_eq`, `rfl`, cast.
- **Hypotheses**: none.
- **Uses from project**: [`qj`, `qj_qxp_coeff_link`, `qj_qexpansion`, `qj_qexpansion_coeff_eq`]
- **Used by**: `j_laurentQExpansion_coeff_one`
- **Visibility**: private
- **Lines**: 88–92, proof 4 lines
- **Notes**: none

### `lemma qjCoeffs_two`
- **Type**: `qjCoeffs 2 = 196884`
- **What**: The second integer coefficient of the regularized `j` is 196884.
- **How**: Via `qjCoeffs_eq_qjQExpansion_coeff_aux`, `qj_qexpansion_coeff_eq`, `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`qjCoeffs`, `qjCoeffs_eq_qjQExpansion_coeff_aux`, `qj_qexpansion_coeff_eq`, `qj_qexpansion`]
- **Used by**: `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial`
- **Visibility**: public
- **Lines**: 94–96, proof 2 lines
- **Notes**: none

### `lemma qj_qExpansion_coeff_three_aux`
- **Type**: `(qExpansion 1 qj).coeff 3 = 21493760`
- **What**: The q³-coefficient of the analytic expansion of `qj` is 21493760 (the coefficient c(2) of `j`).
- **How**: Same route: `qj_qxp_coeff_link`, `qj_qexpansion_coeff_eq`, `rfl`, cast.
- **Hypotheses**: none.
- **Uses from project**: [`qj`, `qj_qxp_coeff_link`, `qj_qexpansion`, `qj_qexpansion_coeff_eq`]
- **Used by**: `j_laurentQExpansion_coeff_two`
- **Visibility**: private
- **Lines**: 98–102, proof 4 lines
- **Notes**: none

### `lemma qjCoeffs_three`
- **Type**: `qjCoeffs 3 = 21493760`
- **What**: The third integer coefficient of the regularized `j` is 21493760.
- **How**: Via `qjCoeffs_eq_qjQExpansion_coeff_aux`, `qj_qexpansion_coeff_eq`, `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`qjCoeffs`, `qjCoeffs_eq_qjQExpansion_coeff_aux`, `qj_qexpansion_coeff_eq`, `qj_qexpansion`]
- **Used by**: `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial`
- **Visibility**: public
- **Lines**: 104–106, proof 2 lines
- **Notes**: none

### `lemma qj_qExpansion_coeff_four_aux`
- **Type**: `(qExpansion 1 qj).coeff 4 = 864299970`
- **What**: The q⁴-coefficient of the analytic expansion of `qj` is 864299970 (the coefficient c(3) of `j`).
- **How**: Same route: `qj_qxp_coeff_link`, `qj_qexpansion_coeff_eq`, `rfl`, cast.
- **Hypotheses**: none.
- **Uses from project**: [`qj`, `qj_qxp_coeff_link`, `qj_qexpansion`, `qj_qexpansion_coeff_eq`]
- **Used by**: `j_laurentQExpansion_coeff_three`
- **Visibility**: private
- **Lines**: 108–112, proof 4 lines
- **Notes**: none

### `lemma qjCoeffs_four`
- **Type**: `qjCoeffs 4 = 864299970`
- **What**: The fourth integer coefficient of the regularized `j` is 864299970.
- **How**: Via `qjCoeffs_eq_qjQExpansion_coeff_aux`, `qj_qexpansion_coeff_eq`, `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`qjCoeffs`, `qjCoeffs_eq_qjQExpansion_coeff_aux`, `qj_qexpansion_coeff_eq`, `qj_qexpansion`]
- **Used by**: `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial`
- **Visibility**: public
- **Lines**: 114–116, proof 2 lines
- **Notes**: none

### `theorem exists_int_coeff_j_eq_principal_part_add_tsum_with_initial`
- **Type**: `∃ c : ℕ → ℤ, c 0 = 744 ∧ c 1 = 196884 ∧ c 2 = 21493760 ∧ c 3 = 864299970 ∧ ∀ z : ℍ, j z = 1 / cexp (2πI z) + ∑' n, c n · cexp (2πI z)^n`
- **What**: An explicit convergent expansion of the modular `j`-function: there is an integer sequence `c` whose first four values are 744, 196884, 21493760, 864299970 such that for every `z ∈ ℍ`, `j(z) = q⁻¹ + Σ c(n) qⁿ` with `q = e^{2πiz}`. This packages the pole/principal-part decomposition of `j` with named initial coefficients.
- **How**: Witnesses `c n := qjCoeffs (n+1)` (index shift removes the constant coefficient 1, which becomes the principal part `1/q`); the four numeric conjuncts are `qjCoeffs_one` … `qjCoeffs_four`, and the convergent-series identity is the project theorem `j_eq_qjCoeffs_tsum` with `qjCoeffs_zero` substituted to split off the `q⁻¹` term.
- **Hypotheses**: none (the statement is a closed existential over ℍ).
- **Uses from project**: [`j`, `qjCoeffs`, `qjCoeffs_zero`, `qjCoeffs_one`, `qjCoeffs_two`, `qjCoeffs_three`, `qjCoeffs_four`, `j_eq_qjCoeffs_tsum`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 118–136, proof 14 lines
- **Notes**: none

### `lemma j_laurentQExpansion_coeff_eq_qj_coeff_aux`
- **Type**: `(n : ℕ) : (laurentqExpansion 1 j).coeff ((n : ℤ) - 1) = (qExpansion 1 qj).coeff n`
- **What**: The Laurent q-expansion coefficients of `j` at index `n − 1` equal the power-series coefficients of `qj` at index `n` — the pole-shift by the pole order 1 of `j` at ∞.
- **How**: Two-step calc: `laurentqExpansion.coeff_neg_poleOrder_add` (a Laurent coefficient at `−poleOrder + n` equals a `to_qExpansion` coefficient) combined with `j_poleOrder` (`poleOrder 1 j = 1`), then `j_to_qExpansion` (`to_qExpansion 1 j = qExpansion 1 qj`, i.e. removing the pole of `j` yields `qj`).
- **Hypotheses**: none.
- **Uses from project**: [`j`, `qj`, `laurentqExpansion` (`UpperHalfPlane.laurentqExpansion`), `j_poleOrder`, `laurentqExpansion.coeff_neg_poleOrder_add`, `to_qExpansion` (`UpperHalfPlane.to_qExpansion`), `j_to_qExpansion`]
- **Used by**: `j_laurentQExpansion_coeff_neg_one`, `j_laurentQExpansion_coeff_zero`, `j_laurentQExpansion_coeff_one`, `j_laurentQExpansion_coeff_two`, `j_laurentQExpansion_coeff_three`
- **Visibility**: private
- **Lines**: 138–144, proof 6 lines
- **Notes**: none

### `theorem j_laurentQExpansion_coeff_neg_one`
- **Type**: `(laurentqExpansion 1 j).coeff (-1) = 1`
- **What**: The Laurent q-expansion of `j` has coefficient 1 at `q⁻¹`: the principal part of `j` at the cusp is exactly `q⁻¹`.
- **How**: Instance `n = 0` of `j_laurentQExpansion_coeff_eq_qj_coeff_aux` chained with the project lemma `qj_qExpansion_coeff_zero` (constant coefficient of `qj` is 1).
- **Hypotheses**: none.
- **Uses from project**: [`j`, `laurentqExpansion`, `j_laurentQExpansion_coeff_eq_qj_coeff_aux`, `qj_qExpansion_coeff_zero`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 146–147, proof 1 line
- **Notes**: none

### `theorem j_laurentQExpansion_coeff_zero`
- **Type**: `(laurentqExpansion 1 j).coeff 0 = 744`
- **What**: The constant Laurent coefficient of `j` is 744.
- **How**: Instance `n = 1` of `j_laurentQExpansion_coeff_eq_qj_coeff_aux` chained with `qj_qExpansion_coeff_one_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`j`, `laurentqExpansion`, `j_laurentQExpansion_coeff_eq_qj_coeff_aux`, `qj_qExpansion_coeff_one_aux`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 149–150, proof 1 line
- **Notes**: none

### `theorem j_laurentQExpansion_coeff_one`
- **Type**: `(laurentqExpansion 1 j).coeff 1 = 196884`
- **What**: The q¹ Laurent coefficient of `j` is 196884.
- **How**: Instance `n = 2` of `j_laurentQExpansion_coeff_eq_qj_coeff_aux` chained with `qj_qExpansion_coeff_two_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`j`, `laurentqExpansion`, `j_laurentQExpansion_coeff_eq_qj_coeff_aux`, `qj_qExpansion_coeff_two_aux`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 152–153, proof 1 line
- **Notes**: none

### `theorem j_laurentQExpansion_coeff_two`
- **Type**: `(laurentqExpansion 1 j).coeff 2 = 21493760`
- **What**: The q² Laurent coefficient of `j` is 21493760.
- **How**: Instance `n = 3` of `j_laurentQExpansion_coeff_eq_qj_coeff_aux` chained with `qj_qExpansion_coeff_three_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`j`, `laurentqExpansion`, `j_laurentQExpansion_coeff_eq_qj_coeff_aux`, `qj_qExpansion_coeff_three_aux`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 155–156, proof 1 line
- **Notes**: none

### `theorem j_laurentQExpansion_coeff_three`
- **Type**: `(laurentqExpansion 1 j).coeff 3 = 864299970`
- **What**: The q³ Laurent coefficient of `j` is 864299970.
- **How**: Instance `n = 4` of `j_laurentQExpansion_coeff_eq_qj_coeff_aux` chained with `qj_qExpansion_coeff_four_aux`.
- **Hypotheses**: none.
- **Uses from project**: [`j`, `laurentqExpansion`, `j_laurentQExpansion_coeff_eq_qj_coeff_aux`, `qj_qExpansion_coeff_four_aux`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 158–159, proof 1 line
- **Notes**: none

### File Summary
- Total declarations: 23 (0 defs, 23 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): [`qjCoeffs_eq_qjQExpansion_coeff_aux` (used by 5), `j_laurentQExpansion_coeff_eq_qj_coeff_aux` (used by 5)]
- Unused declarations (not used by anything in this file): [`ramanujanTau_one`, `ramanujanTau_two`, `ramanujanTau_three`, `Delta_qExpansion_coeff_two`, `Delta_qExpansion_coeff_three`, `Delta_qExpansion_coeff_four`, `Delta_qExpansion_coeff_five`, `exists_int_coeff_j_eq_principal_part_add_tsum_with_initial`, `j_laurentQExpansion_coeff_neg_one`, `j_laurentQExpansion_coeff_zero`, `j_laurentQExpansion_coeff_one`, `j_laurentQExpansion_coeff_two`, `j_laurentQExpansion_coeff_three`]
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: []
