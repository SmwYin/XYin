# Inventory: XYin/PhD/jFunction/qexp_coeffs.lean  (163 lines)

Explicit initial coefficients: Ramanujan τ(1..5), `qjCoeffs 0..4` (1, 744, 196884, 21493760, 864299970) and the corresponding Laurent coefficients of `j` at ∞, all obtained from the tactic-side computable coefficients (`deltaCoeffInt`, `qjCoeffInt`, qExpansion_tactic/Qj.lean) through the link lemmas `ramanujanTau_link`, `Delta_qxp_coeff_link`, `qj_qxp_coeff_link` (qExpansion_tactic/link.lean) and closed by `rfl` (kernel evaluation of the array computation). Imports `XYin.PhD.qExpansion_tactic.link` (→ jfunction, Qj).

## Declarations

### `lemma ramanujanTau_one`
- **Type**: `ramanujanTau 1 = 1`
- **What**: τ(1) = 1.
- **How**: `ramanujanTau_link` (link.lean:232) → `Delta_qexpansion.coeff 1`; `Delta_qexpansion_coeff_eq` (Qj.lean:162) → `deltaCoeffInt 1`; `rfl` evaluates `deltaCoeffsArrayUpTo 1` in the kernel.
- **Hypotheses**: none
- **Uses from project**: [ramanujanTau (Deltaqexpansions.lean:298), ramanujanTau_link (link.lean:232), Delta_qexpansion_coeff_eq (Qj.lean:162), deltaCoeffInt (Qj.lean:108, via rfl)]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 30–32
- **Notes**: same fact as mathlib `ModularForm.discriminant_qExpansion_coeff_one` (Discriminant.lean:210) and project `Delta_q_one_term` (Eisenstein.lean:374), now at ℤ level and by computation. 0 external uses.

### `lemma ramanujanTau_two`
- **Type**: `ramanujanTau 2 = -24`
- **What**: τ(2) = −24. **How**: as above with `deltaCoeffInt 2`. **Hypotheses**: none.
- **Uses from project**: [ramanujanTau, ramanujanTau_link, Delta_qexpansion_coeff_eq, deltaCoeffInt]
- **Used by**: unused in file. **Visibility**: public. **Lines**: 35–37. **Notes**: pairs with `Delta_qExpansion_coeff_two` (same fact in ℂ).

### `lemma ramanujanTau_three`
- **Type**: `ramanujanTau 3 = 252`
- **What**: τ(3) = 252. **How**: as above. **Hypotheses**: none.
- **Uses from project**: [ramanujanTau, ramanujanTau_link, Delta_qexpansion_coeff_eq, deltaCoeffInt]
- **Used by**: unused in file. **Visibility**: public. **Lines**: 40–42. **Notes**: no τ(4), τ(5) at ℤ level although the ℂ versions exist (70–77).

### `private lemma qjCoeffs_eq_qjQExpansion_coeff_aux`
- **Type**: `(n : ℕ) : qjCoeffs n = qj_qexpansion.coeff n`
- **What**: The analytic integer coefficients of q·j equal the tactic-computed ones `qjCoeffInt n`.
- **How**: cast both to ℂ: `qjCoeffs n` ↦ `(qExpansion 1 qj).coeff n` (from `coeTo_of_toIntegralPowerSeries qj_isIntegralPowerSeries`), and `qj_qxp_coeff_link` (link.lean:406); `Int.cast_injective` via `exact_mod_cast`.
- **Hypotheses**: none
- **Uses from project**: [qjCoeffs (jfunction.lean:319), qj_qexpansion (Qj.lean:148), qj, coeTo_of_toIntegralPowerSeries, qj_isIntegralPowerSeries, qj_qxp_coeff_link (link.lean:406)]
- **Used by**: qjCoeffs_zero, qjCoeffs_one, qjCoeffs_two, qjCoeffs_three, qjCoeffs_four
- **Visibility**: private
- **Lines**: 46–51, body 4 lines
- **Notes**: THE bridge `qjCoeffs = qjCoeffInt` between the analytic and computable coefficient notions — but private and buried here; `h` re-proves jfunction.lean:321 `qj_coeff_cast_aux` (also private). Should be public in link.lean.

### `lemma qjCoeffs_zero`
- **Type**: `qjCoeffs 0 = 1`
- **What**: The leading coefficient of the pole of j is 1.
- **How**: bridge lemma + `qj_qexpansion_coeff_eq` (Qj.lean:152) + `rfl` on `qjCoeffInt 0`.
- **Hypotheses**: none
- **Uses from project**: [qjCoeffs, qjCoeffs_eq_qjQExpansion_coeff_aux, qj_qexpansion_coeff_eq, qjCoeffInt (Qj.lean:141, via rfl)]
- **Used by**: exists_int_coeff_j_eq_principal_part_add_tsum_with_initial
- **Visibility**: public
- **Lines**: 55–57
- **Notes**: duplicates `qj_qExpansion_coeff_zero` (jfunction.lean:416, analytic proof) via computation; derivable there without the tactic layer. 0 external uses.

### `lemma Delta_qExpansion_coeff_two`
- **Type**: `(qExpansion 1 Delta).coeff 2 = -24`
- **What**: τ(2) = −24 in ℂ.
- **How**: `Delta_qxp_coeff_link` (link.lean:220), `Delta_qexpansion_coeff_eq`, `exact_mod_cast (rfl : deltaCoeffInt 2 = -24)`.
- **Hypotheses**: none
- **Uses from project**: [Delta (Delta.lean:170), Delta_qxp_coeff_link (link.lean:220), Delta_qexpansion_coeff_eq, deltaCoeffInt]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 60–62
- **Notes**: docstring calls this "the start of the discriminant q-expansion coefficient API" but `_zero`/`_one` companions are elsewhere (mathlib `discriminant_qExpansion_coeff_one`, jfunction.lean:108 private).

### `lemma Delta_qExpansion_coeff_three`
- **Type**: `(qExpansion 1 Delta).coeff 3 = 252`. **What**: τ(3). **How**: same. **Hypotheses**: none.
- **Uses from project**: [Delta, Delta_qxp_coeff_link, Delta_qexpansion_coeff_eq, deltaCoeffInt]. **Used by**: unused in file. **Visibility**: public. **Lines**: 65–67. **Notes**: —

### `lemma Delta_qExpansion_coeff_four`
- **Type**: `(qExpansion 1 Delta).coeff 4 = -1472`. **What**: τ(4). **How**: same. **Hypotheses**: none.
- **Uses from project**: [Delta, Delta_qxp_coeff_link, Delta_qexpansion_coeff_eq, deltaCoeffInt]. **Used by**: unused in file. **Visibility**: public. **Lines**: 70–72. **Notes**: —

### `lemma Delta_qExpansion_coeff_five`
- **Type**: `(qExpansion 1 Delta).coeff 5 = 4830`. **What**: τ(5). **How**: same. **Hypotheses**: none.
- **Uses from project**: [Delta, Delta_qxp_coeff_link, Delta_qexpansion_coeff_eq, deltaCoeffInt]. **Used by**: unused in file. **Visibility**: public. **Lines**: 75–77. **Notes**: `rfl` here reduces `deltaCoeffsArrayUpTo 5` (σ₃/σ₅ loops + three array convolutions) in the kernel — fine at this size, but this is `decide`-style kernel computation, not `native_decide`; no `Lean.ofReduceBool` axiom introduced.

### `private lemma qj_qExpansion_coeff_one_aux`
- **Type**: `(qExpansion 1 qj).coeff 1 = 744`
- **What**: The constant term of j is 744 (in ℂ).
- **How**: `qj_qxp_coeff_link` + `qj_qexpansion_coeff_eq` + `(rfl : qjCoeffInt 1 = 744)` cast.
- **Hypotheses**: none
- **Uses from project**: [qj, qj_qxp_coeff_link, qj_qexpansion_coeff_eq, qjCoeffInt]
- **Used by**: j_laurentQExpansion_coeff_zero
- **Visibility**: private
- **Lines**: 79–81
- **Notes**: same numeric fact as `qjCoeffs_one` (84) at ℤ level; one should be derived from the other by the cast lemma.

### `lemma qjCoeffs_one`
- **Type**: `qjCoeffs 1 = 744`. **What**: c(0) = 744. **How**: bridge + `qj_qexpansion_coeff_eq` + `rfl`. **Hypotheses**: none.
- **Uses from project**: [qjCoeffs, qjCoeffs_eq_qjQExpansion_coeff_aux, qj_qexpansion_coeff_eq, qjCoeffInt]. **Used by**: exists_int_coeff_…. **Visibility**: public. **Lines**: 84–86. **Notes**: 0 external uses.

### `private lemma qj_qExpansion_coeff_two_aux`
- **Type**: `(qExpansion 1 qj).coeff 2 = 196884`. **What**: c(1) in ℂ. **How**: as 79. **Hypotheses**: none.
- **Uses from project**: [qj, qj_qxp_coeff_link, qj_qexpansion_coeff_eq, qjCoeffInt]. **Used by**: j_laurentQExpansion_coeff_one. **Visibility**: private. **Lines**: 88–90. **Notes**: —

### `lemma qjCoeffs_two`
- **Type**: `qjCoeffs 2 = 196884`. **What**: c(1) = 196884 (first Moonshine coefficient). **How**: as 84. **Hypotheses**: none.
- **Uses from project**: [qjCoeffs, qjCoeffs_eq_qjQExpansion_coeff_aux, qj_qexpansion_coeff_eq, qjCoeffInt]. **Used by**: exists_int_coeff_…. **Visibility**: public. **Lines**: 94–96. **Notes**: —

### `private lemma qj_qExpansion_coeff_three_aux`
- **Type**: `(qExpansion 1 qj).coeff 3 = 21493760`. **What**: c(2) in ℂ. **How**: as 79. **Hypotheses**: none.
- **Uses from project**: [qj, qj_qxp_coeff_link, qj_qexpansion_coeff_eq, qjCoeffInt]. **Used by**: j_laurentQExpansion_coeff_two. **Visibility**: private. **Lines**: 98–100. **Notes**: —

### `lemma qjCoeffs_three`
- **Type**: `qjCoeffs 3 = 21493760`. **What**: c(2). **How**: as 84. **Hypotheses**: none.
- **Uses from project**: [qjCoeffs, qjCoeffs_eq_qjQExpansion_coeff_aux, qj_qexpansion_coeff_eq, qjCoeffInt]. **Used by**: exists_int_coeff_…. **Visibility**: public. **Lines**: 103–105. **Notes**: —

### `private lemma qj_qExpansion_coeff_four_aux`
- **Type**: `(qExpansion 1 qj).coeff 4 = 864299970`. **What**: c(3) in ℂ. **How**: as 79. **Hypotheses**: none.
- **Uses from project**: [qj, qj_qxp_coeff_link, qj_qexpansion_coeff_eq, qjCoeffInt]. **Used by**: j_laurentQExpansion_coeff_three. **Visibility**: private. **Lines**: 107–109. **Notes**: —

### `lemma qjCoeffs_four`
- **Type**: `qjCoeffs 4 = 864299970`. **What**: c(3). **How**: as 84. **Hypotheses**: none.
- **Uses from project**: [qjCoeffs, qjCoeffs_eq_qjQExpansion_coeff_aux, qj_qexpansion_coeff_eq, qjCoeffInt]. **Used by**: exists_int_coeff_…. **Visibility**: public. **Lines**: 112–114. **Notes**: —

### `theorem exists_int_coeff_j_eq_principal_part_add_tsum_with_initial`
- **Type**: `∃ c : ℕ → ℤ, c 0 = 744 ∧ c 1 = 196884 ∧ c 2 = 21493760 ∧ c 3 = 864299970 ∧ ∀ z : ℍ, j z = 1 / cexp (2πi z) + ∑' n, c n * cexp (2πi z) ^ n`
- **What**: j = q⁻¹ + 744 + 196884 q + 21493760 q² + 864299970 q³ + … with integer coefficients.
- **How**: witness `c n := qjCoeffs (n+1)`; the four values from `qjCoeffs_one..four`; the expansion is `j_eq_qjCoeffs_tsum` (jfunction.lean:410) with `qjCoeffs_zero` substituted.
- **Hypotheses**: none
- **Uses from project**: [j, qjCoeffs, qjCoeffs_one, qjCoeffs_two, qjCoeffs_three, qjCoeffs_four, j_eq_qjCoeffs_tsum (jfunction.lean:410), qjCoeffs_zero]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 120–134, body 10 lines
- **Notes**: ∃-packaging hides the canonical witness; the useful form is `j z = 1/q + ∑' n, qjCoeffs (n+1) * q^n` (= `j_eq_qjCoeffs_tsum` + `qjCoeffs_zero`). Showcase-only; 0 external uses.

### `private lemma j_laurentQExpansion_coeff_eq_qj_coeff_aux`
- **Type**: `(n : ℕ) : (laurentqExpansion 1 j).coeff ((n : ℤ) - 1) = (qExpansion 1 qj).coeff n`
- **What**: Laurent coefficient of j at n−1 = q-expansion coefficient of q·j at n (index shift by the pole order 1).
- **How**: `j_to_qExpansion` (jfunction.lean:483) + project `laurentqExpansion.coeff_neg_poleOrder_add` (LaurentQExpansion.lean:465) with `j_poleOrder`.
- **Hypotheses**: none
- **Uses from project**: [laurentqExpansion, j, qj, j_to_qExpansion, j_poleOrder (jfunction.lean:460), laurentqExpansion.coeff_neg_poleOrder_add]
- **Used by**: j_laurentQExpansion_coeff_neg_one, _zero, _one, _two, _three
- **Visibility**: private
- **Lines**: 138–141
- **Notes**: a general, public-worthy lemma re-proved as `hjcoeff` in Cox/CoxMatrices/LaurentExpansion.lean:284–286, in `jIntCoeff_eq_qjCoeffInt_three` (LevelThree.lean:122–130) and in `jIntCoeff_neg_one` (LaurentExpansion.lean:38–47). Belongs in jfunction.lean.

### `theorem j_laurentQExpansion_coeff_neg_one`
- **Type**: `(laurentqExpansion 1 j).coeff (-1) = 1`
- **What**: The principal part of j is exactly q⁻¹.
- **How**: shift lemma at n=0 + `qj_qExpansion_coeff_zero` (jfunction.lean:416).
- **Hypotheses**: none
- **Uses from project**: [laurentqExpansion, j, j_laurentQExpansion_coeff_eq_qj_coeff_aux, qj_qExpansion_coeff_zero]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 144–145
- **Notes**: same fact as `Cox.jIntCoeff_neg_one` (LaurentExpansion.lean:38) up to cast; 0 external uses.

### `theorem j_laurentQExpansion_coeff_zero`
- **Type**: `(laurentqExpansion 1 j).coeff 0 = 744`. **What**: constant Laurent coefficient. **How**: shift lemma at n=1 + `qj_qExpansion_coeff_one_aux`. **Hypotheses**: none.
- **Uses from project**: [laurentqExpansion, j, j_laurentQExpansion_coeff_eq_qj_coeff_aux, qj_qExpansion_coeff_one_aux]. **Used by**: unused in file. **Visibility**: public. **Lines**: 148–149. **Notes**: 0 external uses.

### `theorem j_laurentQExpansion_coeff_one`
- **Type**: `(laurentqExpansion 1 j).coeff 1 = 196884`. **What**: q-coefficient. **How**: shift at n=2 + `_two_aux`. **Hypotheses**: none.
- **Uses from project**: [laurentqExpansion, j, j_laurentQExpansion_coeff_eq_qj_coeff_aux, qj_qExpansion_coeff_two_aux]. **Used by**: unused in file. **Visibility**: public. **Lines**: 152–153. **Notes**: —

### `theorem j_laurentQExpansion_coeff_two`
- **Type**: `(laurentqExpansion 1 j).coeff 2 = 21493760`. **What**: q²-coefficient. **How**: shift at n=3 + `_three_aux`. **Hypotheses**: none.
- **Uses from project**: [laurentqExpansion, j, j_laurentQExpansion_coeff_eq_qj_coeff_aux, qj_qExpansion_coeff_three_aux]. **Used by**: unused in file. **Visibility**: public. **Lines**: 156–157. **Notes**: —

### `theorem j_laurentQExpansion_coeff_three`
- **Type**: `(laurentqExpansion 1 j).coeff 3 = 864299970`. **What**: q³-coefficient. **How**: shift at n=4 + `_four_aux`. **Hypotheses**: none.
- **Uses from project**: [laurentqExpansion, j, j_laurentQExpansion_coeff_eq_qj_coeff_aux, qj_qExpansion_coeff_four_aux]. **Used by**: unused in file. **Visibility**: public. **Lines**: 160–161. **Notes**: —

## File Summary
- Total declarations: 24 (0 defs, 24 lemmas/theorems, 0 instances)
- Key API (used by 3+ others in the file): qjCoeffs_eq_qjQExpansion_coeff_aux (5), j_laurentQExpansion_coeff_eq_qj_coeff_aux (5)
- Unused declarations (not used by anything in this file): ramanujanTau_one/two/three, Delta_qExpansion_coeff_two/three/four/five, exists_int_coeff_j_eq_principal_part_add_tsum_with_initial, j_laurentQExpansion_coeff_neg_one/zero/one/two/three — and **all 18 public lemmas have 0 uses outside this file** (`grep -rnw` each: none)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations
### Mathlib API candidates
- `ramanujanTau_one` (30) / `Delta_q_one_term` (Eisenstein.lean:374) = mathlib `ModularForm.discriminant_qExpansion_coeff_one` (`.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Discriminant.lean:210`).
- No mathlib values for τ(n≥2) or the j-coefficients (searched `196884`, `ramanujan`, `744` in Mathlib/NumberTheory: none).
### Missing API / repeated patterns
- `qjCoeffs_eq_qjQExpansion_coeff_aux` (46–51) is the only `qjCoeffs ↔ qjCoeffInt` bridge in the project and is private; promote to link.lean as `qjCoeffs_eq_qjCoeffInt`. Likewise `j_laurentQExpansion_coeff_eq_qj_coeff_aux` (138–141) should be public in jfunction.lean (re-proved 3× under Cox/).
- Every value is proved twice (ℤ: `qjCoeffs_k`, ℂ: `qj_qExpansion_coeff_k_aux`; ℤ: `ramanujanTau_k`, ℂ: `Delta_qExpansion_coeff_k`) with the pattern `rw [link, coeff_eq]; rfl` (12 sites). One `simp`/`decide`-driven macro or a table lemma `∀ n < 5, qjCoeffs n = [1,744,…].getD n 0` (cf. private `qjCoeffTableThree`, LevelThree.lean:43) would replace 16 lemmas.
- Missing `ramanujanTau_zero`, `ramanujanTau_four/five`, `Delta_qExpansion_coeff_zero/_one` in this "API".
### Junk candidates
- Emphasis (d): all 18 public lemmas are documentation-grade (0 external uses). `exists_int_coeff_…` (120–134) is a showcase theorem. The `_aux` ℂ-lemmas (79–109) exist only to feed the Laurent lemmas.
### Moral duplicates within this batch
- `qjCoeffs_zero` (55) ≡ `qj_qExpansion_coeff_zero` (jfunction.lean:416) ≡ `j_laurentQExpansion_coeff_neg_one` (144) ≡ `Cox.jIntCoeff_neg_one` (LaurentExpansion.lean:38).
- `ramanujanTau_two/three` ≡ `Delta_qExpansion_coeff_two/three`; `qjCoeffs_k` ≡ `qj_qExpansion_coeff_k_aux` ≡ `j_laurentQExpansion_coeff_(k-1)`.
- `qjCoeffTableThree` + `qjCoeffInt_eq_tableThree` (LevelThree.lean:43–49, private, `decide +kernel` for n<13) already contain all these j-values.
### Generalization notes
- The `rfl` closings depend on kernel reduction of `Array Int` folds; if precision grows they should switch to the tactic layer's `mkNativeDecideProofFor` (Qj.lean) or `decide +kernel` as in LevelThree.lean:49.
