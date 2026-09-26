# Inventory: XYin/PhD/Modularforms/Eisensteinqexpansions.lean  (155 lines)

Defines the project's normalised level-1 Eisenstein series `E k hk : ModularForm ↑Γ(1) k` (as `(1/2) • eisensteinSeriesMF hk 0`) and proves its q-expansion `E_k(z) = 1 + (1/ζ(k))·((−2πi)^k/(k−1)!)·Σ σ_{k−1}(n) qⁿ` by delegating to mathlib's `EisensteinSeries.q_expansion_riemannZeta`. The remaining ~110 lines (a `gammaSetN` / gcd-sigma decomposition of `Fin 2 → ℤ` and the intermediate identities `q_exp_iden_2`, `EQ0`–`EQ2`) are a superseded hand-rolled route that is no longer used by anything.

## Declarations

### `def standardcongruencecondition`
- **Type**: `Fin 2 → ZMod ((1 : ℕ+) : ℕ)`
- **What**: The zero congruence condition `a = 0` for level `N = 1`, used as the `a` argument of `eisensteinSeriesMF`.
- **How**: Literally `0`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `E`
- **Visibility**: public
- **Lines**: 20, proof body ≈ 0 lines
- **Notes**: Externally used by `Eisenstein.lean` (`E₄`, `E₆`, and as an unfolding key in `Ek_q_exp_zero`, `E4_q_exp`, `E6_q_exp`). mathlib's `ModularForm.E` simply writes `0` here.

### `def E`
- **Type**: `(k : ℤ) → 3 ≤ k → ModularForm (CongruenceSubgroup.Gamma ↑1) k`
- **What**: The normalised weight-`k` level-1 Eisenstein series `E_k`, scaled by `1/2` so that the constant term is 1 (the underlying `eisensteinSeriesMF` sums over coprime pairs, hence counts `±v` twice).
- **How**: `(1/2 : ℂ) • eisensteinSeriesMF hk standardcongruencecondition`.
- **Hypotheses**: `3 ≤ k` (weight ≥ 3 for absolute convergence).
- **Uses from project**: `standardcongruencecondition`
- **Used by**: `E_k_q_expansion`
- **Visibility**: public
- **Lines**: 22–24, proof body ≈ 0 lines
- **Notes**: mathlib has `ModularForm.E {k : ℕ} (hk : 3 ≤ k) : ModularForm 𝒮ℒ k` (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean:47`), defined as `((1/2 : ℂ) • eisensteinSeriesMF (mod_cast hk) 0).copy _ rfl Gamma_one_coe_eq_SL.symm`. The project version differs only in (a) `k : ℤ` vs `k : ℕ` and (b) the group index `↑Γ(1) = Subgroup.map (mapGL ℝ) (Gamma 1)` vs `𝒮ℒ`; these groups are propositionally equal (`CongruenceSubgroup.Gamma_one_coe_eq_SL`, `CongruenceSubgroups.lean:73`) but not definitionally, which is why mathlib uses `.copy`. Every downstream lemma in `Eisenstein.lean` transports mathlib results by `simpa [_root_.E, ModularForm.E, standardcongruencecondition]`. Inline `/- … -/` comment on lines 23–24 is duplicated verbatim at `Eisenstein.lean:56–57`. Externally used by `Eisenstein.lean` (`E4_eq`, `E6_eq`, `E4_apply`, `E6_apply`, `Ek_q_exp_zero`, `Ek_q_exp`, `Ek_ne_zero`, `E_even_imag_axis_real`).

### `def gammaSetN`
- **Type**: `ℕ → Set (Fin 2 → ℤ)`
- **What**: The set of integer vectors `N • v` with `v` primitive (coprime coordinates), i.e. the vectors of gcd exactly `N` (for `N ≠ 0`).
- **How**: Pointwise scalar action `({N} : Set ℕ) • gammaSet 1 1 0`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `gammaSetN_map`, `gammaSetN_map_eq`, `gammaSetN_Equiv`, `gammaSetN_eisSummand`, `GammaSet_one_Equiv`
- **Visibility**: public
- **Lines**: 28, proof body ≈ 0 lines
- **Notes**: mathlib expresses the same set as `gammaSet 1 N 0` (`EisensteinSeries/Defs.lean:45`, membership `gammaSet_one_mem_iff` line 63: `v ∈ gammaSet 1 r 0 ↔ (v 0).gcd (v 1) = r`) and proves `v = r • divIntMap r v` (`gammaSet_eq_gcd_mul_divIntMap`, line 113). Unused outside this file.

### `def gammaSetN_map`
- **Type**: `(N : ℕ) → gammaSetN N → gammaSet 1 1 0`
- **What**: Sends `N • v ∈ gammaSetN N` back to the primitive vector `v`.
- **How**: Unfolds `mem_smul_set` and takes the `Classical.choose` witness.
- **Hypotheses**: none
- **Uses from project**: `gammaSetN`
- **Used by**: `gammaSetN_map_eq`, `gammaSetN_Equiv`, `gammaSetN_eisSummand`
- **Visibility**: public
- **Lines**: 30–35, proof body ≈ 5 lines
- **Notes**: Defined by `choose` inside a `def` (non-computable, opaque). mathlib's `divIntMap r v := v / r` (`Defs.lean:85`) is the explicit inverse. Unused outside this file.

### `lemma gammaSet_top_mem`
- **Type**: `(v : Fin 2 → ℤ) : v ∈ gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1)`
- **What**: Membership in the level-1 primitive set is coprimality of the two coordinates.
- **How**: `simp [gammaSet, ← Int.isCoprime_iff_gcd_eq_one, Subsingleton.eq_zero]`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: `GammaSet_one_Equiv`
- **Visibility**: public
- **Lines**: 37–38, proof body ≈ 1 line
- **Notes**: Verbatim duplicate of mathlib `EisensteinSeries.mem_gammaSet_one` (`Defs.lean:87`).

### `lemma gammaSetN_map_eq`
- **Type**: `(N : ℕ) (v : gammaSetN N) : v.1 = N • gammaSetN_map N v`
- **What**: The chosen primitive vector really does scale back to `v`.
- **How**: `choose_spec.2` of the `mem_smul_set` witness.
- **Hypotheses**: none
- **Uses from project**: `gammaSetN`, `gammaSetN_map`
- **Used by**: `gammaSetN_Equiv`, `gammaSetN_eisSummand`
- **Visibility**: public
- **Lines**: 40–45, proof body ≈ 5 lines
- **Notes**: mathlib analogue `gammaSet_eq_gcd_mul_divIntMap` (`Defs.lean:113`). Unused outside this file.

### `def gammaSetN_Equiv`
- **Type**: `(N : ℕ) (hN : N ≠ 0) : gammaSetN N ≃ gammaSet 1 1 0`
- **What**: For `N ≠ 0`, vectors of gcd `N` are in bijection with primitive vectors via division/multiplication by `N`.
- **How**: `toFun := gammaSetN_map`, `invFun := N • ·`; `right_inv` uses `nsmul_right_injective hN`.
- **Hypotheses**: `N ≠ 0`
- **Uses from project**: `gammaSetN`, `gammaSetN_map`, `gammaSetN_map_eq`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 47–58, proof body ≈ 11 lines
- **Notes**: Duplicate of mathlib `EisensteinSeries.gammaSetDivGcdEquiv (r : ℕ) [NeZero r] : gammaSet 1 r 0 ≃ gammaSet 1 1 0` (`Defs.lean:124`). Unused anywhere in the project.

### `lemma gammaSetN_eisSummand`
- **Type**: `(k : ℤ) (z : ℍ) (n : ℕ) (v : gammaSetN n) : eisSummand k v z = ((n : ℂ)^k)⁻¹ * eisSummand k (gammaSetN_map n v) z`
- **What**: Pulling the gcd `n` out of an Eisenstein summand: `(n c z + n d)^{−k} = n^{−k} (c z + d)^{−k}`.
- **How**: Rewrite `v = n • v'` (`gammaSetN_map_eq`), then `mul_zpow`/`ring_nf`.
- **Hypotheses**: none
- **Uses from project**: `gammaSetN`, `gammaSetN_map`, `gammaSetN_map_eq`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 61–67, proof body ≈ 5 lines
- **Notes**: mathlib `eisSummand_of_gammaSet_eq_divIntMap` (`EisensteinSeries/QExpansion.lean:244`) is the same identity phrased with `divIntMap`. Unused anywhere.

### `def GammaSet_one_Equiv`
- **Type**: `(Fin 2 → ℤ) ≃ (Σ n : ℕ, gammaSetN n)`
- **What**: Every integer vector decomposes uniquely as `gcd • (primitive vector)`; the fibre over gcd `0` is `{0}` (represented as `0 • ![1,1]`).
- **How**: `toFun v := ⟨gcd, gcd • ![v0/gcd, v1/gcd]⟩` using `Int.gcd_div_gcd_div_gcd`; `left_inv` via `Int.mul_ediv_cancel'` + `Int.gcd_dvd_left/right`; `right_inv` via `Int.gcd_mul_left`.
- **Hypotheses**: none
- **Uses from project**: `gammaSetN`, `gammaSet_top_mem`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 69–106, proof body ≈ 37 lines
- **Notes**: Proof >30 lines. Duplicate of mathlib `EisensteinSeries.gammaSetDivGcdSigmaEquiv : (Fin 2 → ℤ) ≃ (Σ r : ℕ, gammaSet 1 r 0)` (`Defs.lean:132`, a 5-line proof via `Equiv.sigmaFiberEquiv`). Unused anywhere. Odd indentation (lines 87–106 indented 10–13 spaces).

### `theorem q_exp_iden_2`
- **Type**: `(k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) : ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k = 2 * riemannZeta k + 2 * ∑' c : ℕ+, ∑' d : ℤ, 1 / (c * z + d) ^ k`
- **What**: Splits the full lattice sum `Σ_{(c,d)} (cz+d)^{−k}` into the `c = 0` row (`2ζ(k)`) and twice the `c > 0` rows, using evenness of `k` to fold `c < 0` onto `c > 0`.
- **How**: `Summable.tsum_prod` + `tsum_int_eq_zero_add_two_mul_tsum_pnat` + `two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even`; the negative rows are folded by `tsum_comp_neg` and `Even.neg_pow`.
- **Hypotheses**: `3 ≤ k`, `k` even.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 109–119, proof body ≈ 9 lines
- **Notes**: This is exactly the first `rw` block inside mathlib's `tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow` (`EisensteinSeries/QExpansion.lean:221–227`), which uses the same three lemmas (`summable_prod_eisSummand`, `tsum_int_eq_zero_add_two_mul_tsum_pnat`, `two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even`, all at `RiemannZeta.lean:212`, `InfiniteSum/NatInt.lean:573`). Unused anywhere.

### `lemma EQ0`
- **Type**: `(k : ℕ) (z : ℍ) : ∑' (x : Fin 2 → ℤ), 1 / (x 0 * z + x 1) ^ k = ∑' x : ℤ × ℤ, 1 / (x.1 * z + x.2) ^ k`
- **What**: Re-indexes a sum over `Fin 2 → ℤ` as a sum over `ℤ × ℤ`.
- **How**: `(piFinTwoEquiv _).tsum_eq`.
- **Hypotheses**: none
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 122–125, proof body ≈ 2 lines
- **Notes**: One-line wrapper around `Equiv.tsum_eq`; mathlib does this with `finTwoArrowEquiv` in `summable_prod_eisSummand` (`QExpansion.lean:216`). Unused anywhere.

### `lemma EQ1`
- **Type**: `(k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) : ∑' (x : Fin 2 → ℤ), 1 / (x 0 * z + x 1) ^ k = 2 * riemannZeta k + 2 * ((-2πi)^k / (k-1)!) * ∑' n : ℕ+, σ (k-1) n * cexp (2πi z n)`
- **What**: The classical Fourier expansion of the (unnormalised) lattice Eisenstein sum `G_k`.
- **How**: `simpa [eisSummand, ← Complex.exp_nat_mul, …] using tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow`.
- **Hypotheses**: `3 ≤ k`, `k` even.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 128–133, proof body ≈ 2 lines
- **Notes**: Thin wrapper of mathlib `tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow` (`EisensteinSeries/QExpansion.lean:221`). Unused anywhere.

### `lemma EQ22`
- **Type**: `(k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) : ∑' (x : Fin 2 → ℤ), eisSummand k x z = riemannZeta k * ∑' (c : gammaSet 1 1 0), eisSummand k c z`
- **What**: The full lattice sum equals `ζ(k)` times the sum over primitive vectors (Möbius/gcd factorisation).
- **How**: `simpa [eisensteinSeries] using tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`.
- **Hypotheses**: `3 ≤ k`.
- **Uses from project**: `[]`
- **Used by**: `EQ2`
- **Visibility**: public
- **Lines**: 136–140, proof body ≈ 2 lines
- **Notes**: Thin wrapper of mathlib `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries` (`EisensteinSeries/QExpansion.lean:250`).

### `lemma EQ2`
- **Type**: `(k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) : ∑' (x : Fin 2 → ℤ), 1 / (x 0 * z + x 1) ^ k = riemannZeta k * ∑' (c : gammaSet 1 1 0), 1 / (c.1 0 * z + c.1 1) ^ k`
- **What**: `EQ22` with `eisSummand` unfolded to `1/(cz+d)^k`.
- **How**: `simpa [eisSummand] using EQ22`.
- **Hypotheses**: `3 ≤ k`.
- **Uses from project**: `EQ22`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 142–145, proof body ≈ 1 line
- **Notes**: Unused anywhere.

### `lemma E_k_q_expansion`
- **Type**: `(k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) : (E k hk) z = 1 + (1 / riemannZeta k) * ((-2πi)^k / (k-1)!) * ∑' n : ℕ+, σ (k-1) n * cexp (2πi z n)`
- **What**: The q-expansion of the normalised Eisenstein series `E_k` in the ζ-form (constant term 1).
- **How**: Unfolds `E`/`ModularForm.E`/`standardcongruencecondition` and `simpa` against mathlib `EisensteinSeries.q_expansion_riemannZeta`.
- **Hypotheses**: `3 ≤ k`, `k` even.
- **Uses from project**: `E`, `standardcongruencecondition`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 149–155, proof body ≈ 3 lines
- **Notes**: Externally used by `Eisenstein.lean` (`Ek_q_exp`, `E_even_imag_axis_real`). Thin wrapper of mathlib `EisensteinSeries.q_expansion_riemannZeta` (`EisensteinSeries/QExpansion.lean:276`); the Bernoulli form is `q_expansion_bernoulli` (line 299). Stale comment lines 147–148 ("already proven in the modular forms repo and being PRed (slowly) into mathlib") — it has landed.

## File Summary
- Total declarations: 15 (6 defs: `standardcongruencecondition`, `E`, `gammaSetN`, `gammaSetN_map`, `gammaSetN_Equiv`, `GammaSet_one_Equiv`; 9 lemmas/theorems; 0 instances; 0 other)
- Key API (used by 3+ others in the file): `gammaSetN` (5 users, all dead)
- Unused declarations (not used by anything in this file): `E_k_q_expansion` (used externally), `gammaSetN_Equiv`, `gammaSetN_eisSummand`, `GammaSet_one_Equiv`, `q_exp_iden_2`, `EQ0`, `EQ1`, `EQ2` — the last seven are unused anywhere in the project (grep -w over XYin).
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: `GammaSet_one_Equiv` (37 lines)

## Observations (evidence for the analysis phases)
### Mathlib API candidates
- `E` ↔ `ModularForm.E` (`.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean:47`), with `ModularForm.E₄`/`E₆` abbrevs at lines 51/54. Same construction; only the group index (`↑Γ(1)` vs `𝒮ℒ`) and `k : ℤ` differ. Mathlib transports across `Gamma_one_coe_eq_SL` (`CongruenceSubgroups.lean:73`) using `.copy`. Unlocks: `E_qExpansion_coeff`, `E_qExpansion_coeff_zero`, `E_ne_zero` (`EisensteinSeries/QExpansion.lean:324,348,353`), `E₄_qExpansion_coeff_one`/`E₆_qExpansion_coeff_one` (`LevelOne/DimensionFormula.lean:203,206`), `discriminant_eq_E₄_cube_sub_E₆_sq` (`LevelOne/GradedRing.lean:59`), `dimension_level_one` (`DimensionFormula.lean:249`) with no unfolding.
- `gammaSet_top_mem` = `EisensteinSeries.mem_gammaSet_one` (`EisensteinSeries/Defs.lean:87`), verbatim.
- `gammaSetN_Equiv` = `gammaSetDivGcdEquiv` (`Defs.lean:124`); `GammaSet_one_Equiv` = `gammaSetDivGcdSigmaEquiv` (`Defs.lean:132`); `gammaSetN_eisSummand` = `eisSummand_of_gammaSet_eq_divIntMap` (`EisensteinSeries/QExpansion.lean:244`); `gammaSetN_map_eq` = `gammaSet_eq_gcd_mul_divIntMap` (`Defs.lean:113`).
- `q_exp_iden_2` (109–119) is the inline first step of mathlib's `tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow` (`EisensteinSeries/QExpansion.lean:221–227`); `EQ1`, `EQ22`, `E_k_q_expansion` are one-line wrappers of `tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow` (221), `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries` (250), `q_expansion_riemannZeta` (276).
- `EQ0` is `(piFinTwoEquiv _).tsum_eq`; mathlib's `summable_prod_eisSummand` (216) uses `finTwoArrowEquiv` for the same re-indexing.
### Missing API / repeated patterns
- The `choose`-based `gammaSetN_map` (30–35) and `gammaSetN_map_eq` (40–45) repeat the same `simp [gammaSetN] at hv2; rw [mem_smul_set] at hv2; hv2.choose_spec` fragment; an explicit inverse `v / N` (mathlib `divIntMap`) removes both.
- The `simpa [_root_.E, ModularForm.E, standardcongruencecondition, …] using <mathlib lemma>` transport idiom (line 153 here; `Eisenstein.lean:224, 269, 298`) is repeated 4×; a single lemma `E_eq_mathlib (k) (hk) : ⇑(E k hk) = ⇑(ModularForm.E (k := k.toNat) _)` (or redefining `E` via `.copy` as mathlib does) would collapse them.
### Junk candidates
- Dead block lines 26–145 (`gammaSetN` … `EQ2`): 9 declarations, ~120 lines, no users in the project (verified `grep -rnw` over `XYin`), all superseded by mathlib. The live content of this file is 3 declarations (`standardcongruencecondition`, `E`, `E_k_q_expansion`, ~15 lines).
- Stale comment 147–148 ("being PRed (slowly) into mathlib").
- Duplicated inline comment 23–24 (same text at `Eisenstein.lean:56–57`).
- Non-mathlib names: `EQ0`, `EQ1`, `EQ22`, `EQ2`, `q_exp_iden_2`, `GammaSet_one_Equiv` (capitalised).
- Misleading `E (k : ℤ)`: the statement `3 ≤ k` over `ℤ` forces every caller to write `(show 3 ≤ k by lia)` casts (lines 116, 133, 140, 155).
### Moral duplicates within this batch
- `EQ22` vs `EQ2` (same statement, `eisSummand` folded/unfolded).
- `E` here vs `E₄`/`E₆` in `Eisenstein.lean:55–60` (which re-expand the definition instead of writing `E 4 _`, then prove `E4_eq : E₄ = E 4 _ := rfl`).
### Generalization notes
- `gammaSetN`, `gammaSetN_Equiv`, `GammaSet_one_Equiv` are pure `ℤ`-gcd combinatorics; nothing about `Fin 2` is used beyond `fin_cases`, but there is no reason to generalise since mathlib already has them.
