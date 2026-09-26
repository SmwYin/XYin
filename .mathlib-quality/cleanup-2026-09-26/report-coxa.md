# Cleanup report — worker `coxa` (HNF / cyclic sublattices / Cox matrices / LevelJ / LatticeJ), 2026-09-26

## 1. Final build

`lake build` (default targets `XYin` + `XYinTest`) in the sandbox:

```
Build completed successfully (3917 jobs).
```

No warnings are emitted for any owned file (checked in the `lake build` log and with
`lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`). No `sorry`, `axiom`,
`native_decide`, heartbeat/recursion options were introduced. All lines ≤ 100 characters.

## 2. Files changed (lines before → after)

| File | before | after |
|---|---|---|
| `XYin/PhD/Cox/HermiteNormalForm.lean` | 408 | 595 (new general API, see §4) |
| `XYin/PhD/Cox/CyclicSublattice.lean` | 541 | 355 |
| `XYin/PhD/Cox/CyclicSublattice/Classification.lean` | 370 | 225 |
| `XYin/PhD/Cox/CoxMatrices/Basic.lean` | 822 | 655 |
| `XYin/PhD/Cox/CoxMatrices/Cardinality.lean` | 278 | 280 (+4 public theorems) |
| `XYin/PhD/Cox/ModularFunction/LevelJ.lean` | 329 | 221 |
| `XYin/PhD/Cox/LatticeJ.lean` | 632 | 626 |
| **total** | **3380** | **2957** |

No files added or deleted; `XYin.lean` unchanged. Import changes: `HermiteNormalForm` += `Mathlib.LinearAlgebra.Matrix.Block`;
`LevelJ` += `XYin.PhD.Cox.HermiteNormalForm`; `Cardinality` −`Mathlib.Data.Nat.Totient` (transitive);
`LatticeJ` −`Mathlib.NumberTheory.ModularForms.NormTrace` (no downstream file used it).

## 3. Done items

### HermiteNormalForm.lean
- `IsColumnHermiteNormalForm.blockTriangular : A.BlockTriangular id`, `det_eq_prod_diagonal` (via mathlib
  `Matrix.det_of_upperTriangular`), `det_pos` (any `Fintype`/`LinearOrder` index); rank-two accessors `one_zero`,
  `zero_zero_pos`, `one_one_pos`, `zero_one_mem`, `eq_fin_two`, `det_eq`, `rankTwoContent_eq`;
  `Matrix.isColumnHermiteNormalForm_fin_two_iff`. `isColumnHermiteNormalForm_fin_two` is now a 1-line corollary (was 10).
  These replace the field-extraction quadruples (HNF:246, CyclicSublattice:75,283–304, Classification:31,63,
  Basic:253,362) and all `det_fin_two_of` hacks (CyclicSublattice:312,465, Classification:40, Basic:348,366).
- `rankTwoContent`: docstring now explains `D₁ = D_{n−1}` in rank 2 and that the rank-`n` criterion is `D_{n−1} = 1`
  (entry gcd 1 is not enough, `diag(1,2,2)`). New `rankTwoContent_fin_two_of` (rfl), `rankTwoContent_eq_finset_gcd`
  (mathlib `Finset.gcd`; closed with `normalize_eq`, `gcd_eq_nat_gcd`), which turns `rankTwoContent_dvd_entry` /
  `dvd_rankTwoContent` into public 2-line proofs via `Finset.gcd_dvd`/`Finset.dvd_gcd` (17 → 6 lines).
  `rankTwoContent_dvd_mul_left` public; new invariance lemmas `rankTwoContent_mul_of_isUnit_det`,
  `rankTwoContent_isUnit_det_mul`, `rankTwoContent_antiTranspose`, `rankTwoContent_adjugate`.
- Uniqueness unified: `IsColumnHermiteNormalForm.eq_of_mul_isUnit_det` (one 25-line proof via positivity of the
  diagonal of the unimodular matrix) replaces `Basic.columnHNF_eq_of_mul` (40 lines) and the body of
  `HermiteNormalForm.matrix_eq` (39 lines); `matrix_eq` is now 4 lines (`isUnit_det_of_right_inverse` +
  `Basis.toMatrix_mul_toMatrix_flip`); the residue lemma (HNF:232 ≡ Basic:239) exists once.
- `exists_right_mul_SL2_isColumnHermiteNormalForm` (public, from Basic's private `_aux`) and
  `Matrix.exists_SL2_mul_eq_upperTriangular` (left triangularisation) via the new public `Matrix.antiTranspose`
  (2×2 anti-transpose = old private `matrixStar`, with `antiTranspose_eq_submatrix_transpose`, `_antiTranspose`,
  `_mul` (from `transpose_mul` + `submatrix_mul_equiv`), `det_antiTranspose` (from `det_transpose` +
  `det_submatrix_equiv_self`)).
- `Matrix.toLin_injective_iff_det_ne_zero` (any domain, bases on different modules): used in
  `Submodule.exists_hermiteNormalForm` (33 → 21 lines) and Classification.
- `Matrix.SpecialLinearGroup.mul_coe_mul_coe_inv`, `coe_mul_coe_inv_mul` (replace 3 cancellation chains in Basic).
- `HermiteNormalForm.repr_apply` restated in simp-normal form (`bM.repr (h.bN j : M) i`; only internal users);
  new `repr_eq_mulVec`, `det_smul_repr` (Cramer: `det H • repr_bN y = adj H *ᵥ repr_bM y`), `ofToLin` (+`_matrix`),
  `det_eq_index`. `quotient_isAddCyclic_iff_…_toMatrix_eq_one`: content step 14 → 5 lines, `hAD` deleted.
  `bN_eq` golfed 8 → 3 lines.

### CyclicSublattice.lean (−186)
- `carrierEquiv` := `Submodule.equivSubtypeMap … |>.trans (LinearEquiv.ofEq …)` (28 → 4; deletes
  `carrierToPeriodPairLinearMap`, `_bijective`).
- `dualMatrix` deleted — the dual inclusion matrix is `Matrix.adjugate` of the HNF matrix; the 12 private lemmas
  `nsmul_basis_*`, `dualLinearMap_basis_*`, `dual_repr_*` (~95 lines) replaced by one 15-line `dualToMatrix_eq` via
  `HermiteNormalForm.det_smul_repr` + `Matrix.mulVec_single_one`; `dual_index_eq` via `Matrix.det_adjugate`;
  `dual_cyclic` via `rankTwoContent_adjugate`.
- `dualLinearMap` := `carrierEquiv ∘ₗ LinearMap.codRestrict … (m • id)` (13 → 3); injectivity 7 → 4 lines.
- Private `d/b/a/d_pos/a_pos/lower_left_eq_zero/originalMatrix_eq/hermite_repr_apply/d_mul_a_eq_m/dual_content_eq_one`
  deleted in favour of public `det_hermiteNormalForm_matrix`, `rankTwoContent_hermiteNormalForm_matrix`,
  `toPeriodPair_ω₁`, `toPeriodPair_ω₂`; `hnfPeriods_linearIndependent` 25 → 13 lines (via `det_pos`).
- `indexUnit` public + `@[simp] coe_indexUnit`; `dual_carrier_map_subtype`, `dual_toPeriodPair_lattice` stated
  with it (no external users); `dual_sub_j` term-mode; `dualCarrier_map_subtype_aux` inlined.
- Dead removed (step8): `map_carrier`, private `carrierEquiv_apply_coe`, `transportedBasis_apply_coe`;
  `@[simp]` dropped from private lemmas.

### Classification.lean (−145)
- `toCoxMatrix` term-mode `:= CoxMatrix.ofColumnHNF …` (28 → 3) + `@[simp] toCoxMatrix_a/_b/_d`;
  `toCoxMatrix_inclusionMatrix := inclusionMatrix_ofColumnHNF ..` (the 17-line
  `hermiteNormalForm_matrix_eq_inclusionMatrix` removed, it had no users).
- `inclusionLinearMap`, `_injective`, `inclusionHermiteNormalForm` (37 lines) → `HermiteNormalForm.ofToLin` +
  `toLin_injective_iff_det_ne_zero` (7 lines); `toCyclicSublatticeOfPeriodPair` term-mode; new simp lemma
  `toCyclicSublatticeOfPeriodPair_hermiteNormalForm_matrix`.
- `coxMatrix_toPeriodPair_lattice` now computed from `toPeriodPair_ω₁/ω₂`: the 7 private generator/span lemmas
  (`sublatticeGenerators`, `sublattice_eq_span`, `complexSublatticeGenerators`, `coe_sublatticeGenerators`,
  `sublattice_map_subtype`, `range_complexSublatticeGenerators`, `complexSublatticeSpan_eq_scaledLattice`, ~90 lines)
  deleted; `Units.mk0 (σ.d : ℂ)` ×4 → new `CoxMatrix.dUnit` (+`coe_dUnit`); `toCyclicSublattice_j` term-mode.
- Dead/alias removed: `cyclicSublattice_hnf_matrix`, `CoxMatrix.toCyclicSublattice_carrier`, `CoxMatrix.sublattice`.
- New `nat_card_cyclicSublattice : Nat.card (CyclicSublattice L m) = Fintype.card (CoxMatrix m)`.

### CoxMatrices/Basic.lean (−167 net, ~80 lines of new API included)
- `@[ext] structure CoxMatrix` (generates `CoxMatrix.ext/ext_iff`); `toFin_injective`, `inclusionMatrix_injective`
  are 1–3 line terms. New `a_dvd`, `d_dvd`, `div_d`, `div_a`, `coprime_gcd_b`; `d_pos`, `a_le`, `d_le` golfed.
- `@[simp] inclusionMatrix_{zero_zero,zero_one,one_zero,one_one}`, `antiTranspose_inclusionMatrix`,
  `antiTranspose_mobiusMatrix`; `inclusionMatrix_det`/`_content_eq_one` via the HNF lemmas.
- `CoxMatrix.ofColumnHNF` smart constructor + `@[simp] ofColumnHNF_a/_b/_d`, `@[simp] inclusionMatrix_ofColumnHNF`,
  `mobiusMatrix_ofColumnHNF`; replaces the private `exists_coxMatrix_of_isColumnHermiteNormalForm_aux` (28 lines),
  used by `exists_coxMatrix_reduction`, `exists_sl2_mul_eq_coxMatrix`, Classification.
- Private `matrixStar` + 5 lemmas → `Matrix.antiTranspose`; `columnHNF_eq_of_mul` + residue copy (47 lines) → HNF
  uniqueness; SL₂ cancellation chains → the two new SL lemmas; `coxInput_content_eq_one` 15 → 7 (entry
  divisibility instead of `ac_rfl`); `determinantScale_mul_eq` shared by `coxInput_eq` and the normalization;
  `coxRepresentative_one` 5 → 1 line, `coxInput_one` deleted.
- `complex_mobius_scale_eq_affine` duplicate + `levelJ_smul_eq_j_act_of_normalization` (63 lines) deleted:
  `rightCosetEval_equiv` uses LevelJ's public `levelJ_smul_eq_j_affine` + new `CoxMatrix.affineUpperHalfPlane_eq_act`.
- `exists_sl2_mul_eq_coxMatrix` 28 → 12 lines (via `exists_SL2_mul_eq_upperTriangular` + `ofColumnHNF`).
- New `CoxMatrix.act_eq_smul_of_mul_eq` (step7 L12): `γ·M = σ.mobiusMatrix`, `w = M·τ` ⇒ `σ.act τ = γ • w`.

### CoxMatrices/Cardinality.lean
- Fibration equivalence rewritten in term mode with `CoxMatrix.ext`, `d_dvd`, `div_d`, `coprime_gcd_b`
  (left/right inverse proofs 11 → 2 lines); two `rw` chains merged; `@[simp]` dropped from a private rfl lemma.
- New ℕ-valued API: `card_coxMatrix_eq_factorization_prod` (|C(m)| = ∏ (p^e + p^(e−1))),
  `card_coxMatrix_of_prime` (= p + 1), `gamma0_index_eq_card_coxMatrix`, `gamma0_index_eq_factorization_prod`.
  Headline ℚ `card_coxMatrix` unchanged. Module docstring updated.

### ModularFunction/LevelJ.lean (−108)
- The 99-line left triangularisation (`first_column_ne_zero_of_det_ne_zero_aux`, `exists_sl2_inv_mul_first_column_gcd_aux`,
  `matrix_eq_upper_triangular_aux`, `exists_positive_upper_triangularization_aux`, old normalization) → a 14-line
  corollary of `Matrix.exists_SL2_mul_eq_upperTriangular` (`lift` to ℕ).
- `natScaleUpperHalfPlane` := `⟨(N : ℝ), _⟩ • τ` via mathlib `UpperHalfPlane.posRealAction` (now public, coe lemma by
  `simp`), + `levelJ_apply : levelJ N τ = j (natScaleUpperHalfPlane N τ)` (not simp); `levelJ`'s definition is
  unchanged (Arithmetic unfolds it).
- `affineUpperHalfPlane`/`coe_affineUpperHalfPlane` public; `smul_natScale_smul_eq_affine`, `levelJ_smul_eq_j_affine`
  public and stated with `δ` instead of `δ⁻¹` (deletes `coe_inv_smul_natScale_smul`, 15 lines).
- Dead `coe_levelJModularFunction` (rfl) removed.

### LatticeJ.lean
- `Delta_eq_E4_E6` is a 1-line term (`Delta_eq_eta_pow.trans ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`).
- `levelOneWeightZeroCuspForm_aux` builds a `CuspForm 𝒮ℒ 0`, so mathlib `levelOne_weight_zero_const` replaces
  `ModularForm.eq_const_of_weight_zero` and the `NormTrace` import is dropped.
- New `PeriodPair.homothetic_of_pow_eq` (g₂ = c⁴g₂', g₃ = c⁶g₃' ⇒ homothetic) collapses the tails of the three
  `homothetic_of_j_eq_*_aux` proofs. `fun … =>` → `↦`.

## 4. New public API

HermiteNormalForm.lean (namespace `Matrix` unless stated):
- `IsColumnHermiteNormalForm.blockTriangular : A.BlockTriangular id`; `.det_eq_prod_diagonal : A.det = ∏ i, A i i`;
  `.det_pos : 0 < A.det`; `.one_zero`, `.zero_zero_pos`, `.one_one_pos`, `.zero_one_mem`;
  `.eq_fin_two : A = !![A 0 0, A 0 1; 0, A 1 1]`; `.det_eq : A.det = A 0 0 * A 1 1`;
  `.rankTwoContent_eq : A.rankTwoContent = gcd (gcd |A₁₁| |A₀₁|) |A₀₀|`;
  `.eq_of_mul_isUnit_det : A, B HNF → IsUnit U.det → A * U = B → A = B`.
- `isColumnHermiteNormalForm_fin_two_iff : A HNF ↔ A 1 0 = 0 ∧ 0 < A 0 0 ∧ 0 < A 1 1 ∧ A 0 1 ∈ Ico 0 (A 0 0)`.
- `rankTwoContent_fin_two_of`, `rankTwoContent_eq_finset_gcd`, `rankTwoContent_dvd_entry`, `dvd_rankTwoContent`,
  `rankTwoContent_dvd_mul_left` (now public), `rankTwoContent_mul_of_isUnit_det`, `rankTwoContent_isUnit_det_mul`,
  `rankTwoContent_antiTranspose`, `rankTwoContent_adjugate`.
- `exists_right_mul_SL2_isColumnHermiteNormalForm : 0 < A.det → ∃ U : SL(2,ℤ), (A * U).IsColumnHNF`.
- `exists_SL2_mul_eq_upperTriangular : 0 < M.det → ∃ γ a b d, 0<a ∧ 0<d ∧ b ∈ Ico 0 d ∧ a*d = M.det ∧ γ*M = !![a,b;0,d]`.
- `antiTranspose` (def) + `antiTranspose_eq_submatrix_transpose`, `antiTranspose_antiTranspose` (simp),
  `antiTranspose_mul`, `det_antiTranspose` (simp).
- `toLin_injective_iff_det_ne_zero : Injective (toLin v₁ v₂ A) ↔ A.det ≠ 0` (over a domain).
- `SpecialLinearGroup.mul_coe_mul_coe_inv : A * U * U⁻¹ = A`, `SpecialLinearGroup.coe_mul_coe_inv_mul : U * (U⁻¹ * A) = A`.
- `Module.Basis.HermiteNormalForm.repr_eq_mulVec`, `.det_smul_repr`, `.ofToLin` (+ simp `ofToLin_matrix`), `.det_eq_index`.

CyclicSublattice.lean: `det_hermiteNormalForm_matrix : S.hermiteNormalForm.matrix.det = m`,
`rankTwoContent_hermiteNormalForm_matrix : … = 1`, `toPeriodPair_ω₁ = H₀₀ ω₁`, `toPeriodPair_ω₂ = H₀₁ ω₁ + H₁₁ ω₂`,
`indexUnit` (now public), `coe_indexUnit` (simp).

Classification.lean: `toCoxMatrix_a/_b/_d` (simp), `CoxMatrix.toCyclicSublatticeOfPeriodPair_hermiteNormalForm_matrix`
(simp), `nat_card_cyclicSublattice`, `CoxMatrix.dUnit`, `CoxMatrix.coe_dUnit` (simp).

CoxMatrices/Basic.lean: `CoxMatrix.ext`/`ext_iff` (`@[ext]`), `a_dvd`, `d_dvd`, `div_d`, `div_a`, `coprime_gcd_b`,
`inclusionMatrix_{zero_zero,zero_one,one_zero,one_one}` (simp), `antiTranspose_inclusionMatrix`,
`antiTranspose_mobiusMatrix`, `ofColumnHNF` (+ simp `_a/_b/_d`, `inclusionMatrix_ofColumnHNF`), `mobiusMatrix_ofColumnHNF`,
`affineUpperHalfPlane_eq_act`, `act_eq_smul_of_mul_eq`.

Cardinality.lean: `card_coxMatrix_eq_factorization_prod`, `card_coxMatrix_of_prime`, `gamma0_index_eq_card_coxMatrix`,
`gamma0_index_eq_factorization_prod`.

LevelJ.lean: `natScaleUpperHalfPlane` (+coe simp), `levelJ_apply`, `affineUpperHalfPlane` (+coe simp),
`smul_natScale_smul_eq_affine`, `levelJ_smul_eq_j_affine`.

LatticeJ.lean: `PeriodPair.homothetic_of_pow_eq`.

All previously public names used outside the owned set keep name and statement (including headline
`theorem_11_23`, `j_surjective`, `j_eq_iff_exists_sl2_smul_eq`, `card_coxMatrix`).

## 5. Kept on purpose

- `Module.Basis.HermiteNormalForm.bN_eq` (step8: dead) — genuine uniqueness statement of the HNF basis; tidied to 3 lines.
- `Cox.rightCosetMul_mk` (step8: dead) — `@[simp]` lemma that `exists_rightCosetMul_baseRightCoset_eq`'s `simp` uses.
- `PeriodPair.coe_smulLatticeEquiv_apply/_symm_apply` — `@[simp]` API.
- `exists_coprime_add_mul_of_gcd_gcd_eq_one` (private, genuine), the whole ψ divisor-sum machinery in Cardinality.
- `cyclicSublatticeEquivCoxMatrix` (Cox Lemma 11.24 as stated in the book).
- New API with no current user in the owned set (for the next workers): `act_eq_smul_of_mul_eq`, `div_a`,
  `card_coxMatrix_of_prime`, `gamma0_index_*`, `nat_card_cyclicSublattice`, `antiTranspose_mobiusMatrix`.

## 6. Deferred (with reason)

- **Dedekind ψ as a definition** (`pmul μ μ * id` / `Nat.dedekindPsi`): not done — it does not shorten anything: the
  multiplicativity of the fibre sum `∑_{d∣m} (d/g)·φ(g)` still needs the CRT argument and the prime-power computation;
  ψ would only name the target. The ℕ closed form and `Γ₀` index formula are exposed instead.
- Redefining `rankTwoContent` *as* `Finset.gcd` (definition change): kept the `Nat.gcd` definition
  (SingularModuli unfolds it with `simp only [Matrix.rankTwoContent, …]`); `rankTwoContent_eq_finset_gcd` added.
- `PeriodPair.smul_lattice_eq_span` (step7 L33): the Classification block it targeted is deleted; the lemma is `rfl`.
- `exists_hnf_transform` via `IsCoprime.exists_SL2_col`; `exists_unit_mul_pos_aux` → `Int.sign`: not attempted (small).
- `CyclicSublattice` ℂ-free generalisation (G-22/G-23), rank-`n` HNF (G-24 ii): restructurings, out of scope.
- Style-only renames (`dual_base_j` is misnamed, `theorem_11_*` names): deferred by policy.

### Follow-ups outside the owned set
- `Cox/SingularModuli.lean:155–186` `coxMatrix_act_eq_smul_aux` → `σ.act_eq_smul_of_mul_eq hmat τ τ hw` with `hw`
  from `q.equation` (≈25 lines); `:141–153` `fixingMatrix_content_eq_one` can start from `Matrix.rankTwoContent_fin_two_of`.
- `Cox/Kronecker.lean:58` → `CoxMatrix.a_dvd`/`d_dvd`/`div_d`; `:67`, `:78` (`apply CoxMatrix.toFin_injective; simp [toFin, …]`)
  → `CoxMatrix.ext …` / `ext <;> simp`.
- `Cox/UpperHalfPlaneFunctionField.lean:211` → `CoxMatrix.ext`.
- `Cox/CoxMatrices/LaurentExpansion.lean:313–314`, `:339–340` → `σ.d_dvd`, `σ.div_d`; `:324–326` → `σ.coprime_gcd_b`;
  `:349–351` → `CoxMatrix.ext rfl hb hd`.
- `Cox/LevelThree.lean:733–738` → `card_coxMatrix_of_prime` (import `Cox.CoxMatrices.Cardinality` if not transitive).
- `Cox/Arithmetic.lean:284` (`unfold levelJ jN`) → `rw [levelJ_apply]` (+ `natScaleUpperHalfPlane` form).
- `jFunction/jLevelN.lean:33–38`: host an ℕ-scaling helper there (step5 row 74) so LevelJ's `natScaleUpperHalfPlane`
  and `jN` share it.
- `Modularforms/IsCuspForm.lean`: add `ModularForm.tendsto_atImInfty_coeff_zero` (step5 H6); then LatticeJ's
  `E4_tendsto_atImInfty_aux` becomes a 1-liner (not worth doing inside LatticeJ alone).
- `Modularforms/Eisenstein.lean`/`Delta.lean`: hoist `Delta_eq_E4_E6` (step5 row 4); LatticeJ keeps its 2-line copy.

## 7. Performance

No kernel-computation file was edited. `Cox/LevelThree.lean` is rebuilt (it imports Cox matrices), but none of its
`decide +kernel` goals reduces a definition from the owned set (they concern `explicitCandidateClearedJet*`;
`sigmaZero` only appears under `norm_num`). Full `lake build` after the changes: ≈ 1 min 44 s wall.
