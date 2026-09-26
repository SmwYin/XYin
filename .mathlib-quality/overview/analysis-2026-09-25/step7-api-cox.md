# Step 7 — API Design Review, Cox ALGEBRAIC side (2026-09-25)

Scope: `XYin/PhD/Cox/{HermiteNormalForm, CyclicSublattice, CyclicSublattice/Classification,
CoxMatrices/{Basic,Cardinality,LaurentExpansion}, FormalCoxProduct, ModularPolynomial/{AnalyticSupport,
Construction,IntegralDescent,Interpolation,Irreducibility}, LaurentPolynomialEvaluation, DiagonalLaurent,
SymmetricCubicLaurent, Kronecker, KroneckerFrobenius, LevelThree, Arithmetic, SingularModuli,
UpperHalfPlaneFunctionField, ModularFunctionField}.lean` (≈8,150 lines, 22 files).
All line numbers are CURRENT (re-grepped 2026-09-25 against the working tree).
Mathlib = pinned rev 2abc242 (`.lake/packages/mathlib/Mathlib/`), every "mathlib has X" claim below is grep-verified.

Verification performed (4 scratch compiles, `lake env lean`, files in the session scratchpad
`step7cox_check{1,2,3,4}.lean`):
- COMPILED (proof accepted): `CoxMatrix.ext` (`cases σ; cases τ; simp_all`), `CoxMatrix.d_dvd/a_dvd/div_d/coprime_gcd_b`,
  `inclusionMatrix` entry `rfl` simp lemmas, `IsColumnHermiteNormalForm.det_eq`/`det_pos` via `Matrix.det_of_upperTriangular`,
  `Matrix.isColumnHermiteNormalForm_fin_two_iff`, `Matrix.rankTwoContent_fin_two_of` (rfl),
  `SpecialLinearGroup.mul_coe_mul_coe_inv`, `matrixStar A = (A.submatrix Fin.rev Fin.rev)ᵀ`,
  `(Gamma0 m).index = Fintype.card (CoxMatrix m)` (5 lines), `HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt` (2 lines),
  `HahnSeries.mapRingHom` (typeclasses `[PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]`),
  `HahnSeries.coeffSubring (S : Subring R)`, `HahnSeries.leadingCoeff_pow` (generic, `[NoZeroDivisors R]`),
  `CharP (HahnSeries Γ R) p` instance, `Cox.jLaurentSeriesWidth R m` (via `HahnSeries.ofSuppBddBelow`) + `_coeff` rfl.
- STATEMENT TYPECHECKED ONLY (`sorry` body): `LaurentSeries.coeff_single_neg_mul_coe_expand`,
  `PowerSeries.pow_prime_pow_eq_expand`, `polynomial_eval₂_laurentSeries_order`, `LaurentSeries.substMonomial` (def),
  `CoxMatrix.act_eq_sl2_smul_of_mul`.
- NOT compile-checked: everything else (marked "(not compiled)").

---

## 0. Prior July report (`analysis/step7-api.md`) — re-verification of Cox-algebraic items

| July item | Status 2026-09-25 | Current evidence |
|---|---|---|
| `analyticOrderAt_const_mul_pow` (§1) | STILL OPEN (shared w/ analytic agent) | inline at `CoxMatrices/LaurentExpansion.lean:151–160` |
| `poleOrder_eq_of_meromorphicOrderAt_eq` (§1) | DONE | exists as `LaurentQExpansion.lean:243` and `poleOrder_eq_toNat_neg_meromorphicOrderAt` (:261); consumed at `LaurentExpansion.lean:183` |
| `laurentqExpansion_pow` / `_polynomial_eval₂` (§1) | STILL OPEN | duplicated `IntegralDescent.lean:25–52` ≡ `DiagonalLaurent.lean:152–185` (see L20) |
| index-generic `symmetricCubicExpansion_coeff` (§1) | HALF DONE | `_coeff_aux` exists (`SymmetricCubicLaurent.lean:44–62`); four 1-line wrappers `:64–86` still present, consumed once each at `:97–100` |
| `CoxMatrix.ofColumnHNF` (§1) | STILL OPEN (partly) | July duplicate inside `exists_coxMatrix_reduction` is gone (`Basic.lean:387–397` now calls the aux); the aux body `Basic.lean:358–385` is the def; THIRD copy at `Classification.lean:28–55` (see L10) |
| `UpperHalfPlane.natScale` (§1) | STILL OPEN | `ModularFunction/LevelJ.lean:29` private `natScaleUpperHalfPlane`; mathlib `UpperHalfPlane.posRealAction` (`Analysis/Complex/UpperHalfPlane/Basic.lean:197`) unused; anonymous `⟨(m:ℂ)*…, _⟩` at `Basic.lean:725`, `Arithmetic.lean:264` |
| canonical `jIntCoeff` + cast API (§1) | STILL OPEN | 3 notions persist: `qjCoeffs` (jfunction:319), `jIntCoeff` (LaurentExpansion:31, `Classical.choose`), `qjCoeffInt` (Qj); bridge `LevelThree.lean:122` private, `jIntCoeff_eq_zero_of_lt` lives at `Kronecker.lean:149` not beside `jIntCoeff_neg_one` (LaurentExpansion:38) |
| LevelThree jet generalisation (§1) | STILL OPEN, now measured | 29 `decide +kernel` sites, 35-decl split `LevelThree.lean:349–502` + 40-line conjunction `:518–557`; single `decide +kernel` for all ten coefficients measured 6.7 s (batch M) → see L39 |
| `transformedJSeries_coeff` `@[simp]` (§2) | STILL OPEN | `LaurentExpansion.lean:66` not simp; 17 explicit `rw` uses across 7 files |
| `@[simp]` on `BivariatePolynomial` normalisers (§2) | PARTLY | only `diagonal_swap` is simp (`Construction.lean:144`); `coeff_coeff_swap`(:97), `specializeY_eval`(:70), `diagonal_eval`(:116), `map_swap`(:108) not |
| `CoxMatrix` inclusionMatrix entry simp set (§2) | STILL OPEN | 8 manual unfold sites (see §2) |
| `@[ext] CoxMatrix.ext` (§3) | STILL OPEN (VERIFIED 3-line proof) | `Basic.lean:101–103, 296–298`, `LaurentExpansion.lean:349–351`, `toFin_injective` as ext-substitute at `Cardinality.lean:91`, `Kronecker.lean:67,78`, `UHPFF.lean:211` |
| `HolomorphicFunction` FunLike/evaluation_apply/ext (§3) | STILL OPEN | 8 `Subtype.ext; funext` / `congrArg (fun f ↦ f.1 τ)` sites (see L29) |
| `IsGamma0ModularFunction` closure API (§3) | RENAMED, STILL OPEN | predicate is now `CuspData` (`CuspData.lean:30`, anonymous 3-conjunction); `CuspData.mul`, `.polynomialIn` exist; `.add/.sub/.neg/.const/.pow` missing; 27 `.1/.2.1/.2.2` projection sites |
| `laurentqExpansion` sub/pow/smul/polynomial (§4) | STILL OPEN | Algebra.lean has add/mul/neg/finset_sum/finset_prod only |
| `levelJ 1 = j`, `levelJ_apply` (§4) | STILL OPEN | `LevelJ.lean:25` `levelJ N := @jN N ⟨_⟩`; `Arithmetic.lean:284` `unfold levelJ jN` |
| change-of-ring layer / `laurentSeriesMapRingHom_ofPowerSeries` square (§4) | STILL OPEN | `LaurentPolynomialEvaluation.lean:22` hand-built; `integerCoeffLaurentSeries` private `IntegralDescent.lean:72–94`; second copy `FormalCoxProduct.lean:51–72` (see L27) |
| `columnHNF_eq_of_mul` 61 lines (§5) | 40 lines now, STILL OPEN | `Basic.lean:247–286`; NEW: it is byte-identical to `HermiteNormalForm.matrix_eq` (`HermiteNormalForm.lean:241–278`) (see L3) |
| `exists_coxMatrix_reduction` 59 lines (§5) | DONE | 11 lines (`Basic.lean:387–397`) |
| `poleOrder_coxAction_aux` 54 (§5) | 42 lines, PARTLY | tail collapsed via `poleOrder_eq_toNat_neg_meromorphicOrderAt`; `analyticOrderAt_const_mul_pow` block still inline |
| `laurentqExpansion_coxAction_coeff_aux` 90 (§5) | 45 lines, PARTLY | `LaurentExpansion.lean:258–300` |
| `to_qExpansion_coxAction_aux` 44 (§5) | 46 lines, STILL OPEN | `LaurentExpansion.lean:196–241` |
| `cox_b_eq` 41 (§5) | 23 lines, mostly DONE | `UHPFF.lean:179–201` |
| `aeval_base_eq_zero_of_forall_eval_eq_zero` 44 (§5) | 41 lines, STILL OPEN | `Arithmetic.lean:53–92` |

---

## 1. Missing lemmas (would simplify multiple proofs)

Format: **Name** — Statement — Home — Sites hand-rolling it — Lines saved — Composes from — Action.

### L1. `Matrix.exists_SL2_inv_mul_eq_upperTriangular` (kills LevelJ:159–257 + Basic:343 copy)
```lean
theorem Matrix.exists_SL2_inv_mul_eq_upperTriangular (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : 0 < M.det) :
    ∃ (δ : SL(2, ℤ)) (g s : ℕ) (r : ℤ), 0 < g ∧ 0 < s ∧ ((g * s : ℕ) : ℤ) = M.det ∧
      r ∈ Set.Ico 0 (s : ℤ) ∧ (δ⁻¹ : SL(2, ℤ)).1 * M = !![(g : ℤ), r; 0, (s : ℤ)]
```
- Home: `HermiteNormalForm.lean` (add `import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`) or a public section of `CoxMatrices/Basic.lean`.
- Sites: `ModularFunction/LevelJ.lean:159–166` (`first_column_ne_zero_of_det_ne_zero_aux`), `:168–201` (`exists_sl2_inv_mul_first_column_gcd_aux`, 34 lines), `:203–210` (`matrix_eq_upper_triangular_aux` = `Matrix.eta_fin_two`), `:212–241` (`exists_positive_upper_triangularization_aux`, 30 lines), `:243–257` (`exists_levelJ_cusp_normalization`, 15 lines) — 99 lines re-deriving left-SL₂ triangularisation; `CoxMatrices/Basic.lean:343–356` (`exists_sl_right_mul_isColumnHermiteNormalForm_aux`, private) + `:793–820` (`exists_sl2_mul_eq_coxMatrix`, whose body `:797–820` IS this lemma plus CoxMatrix packaging).
- Saved: ≈ 99 − 12 (LevelJ) + 15 (Basic:797–820 → `obtain … := exists_SL2_inv_mul…; exact ofColumnHNF …`) ≈ 100 lines.
- Composes from: `exists_sl_right_mul_isColumnHermiteNormalForm_aux (matrixStar M)` + `matrixStar_mul`/`matrixStar_involutive` (exactly `Basic.lean:797–820`), `Matrix.det_of_upperTriangular` (`LinearAlgebra/Matrix/Block.lean:324`). Note: the conclusion shape is exactly mathlib's `FixedDetMatrices.reps` (`LinearAlgebra/Matrix/FixedDetMatrices.lean:69`: `A 1 0 = 0 ∧ 0 < A 0 0 ∧ 0 ≤ A 0 1 ∧ |A 0 1| < |A 1 1|`); `reduce_mem_reps` (:175) gives existence of a representative in the left-`SL₂` orbit, so an alternative proof is via mathlib (but `reps`/`reduce` have no "∃ δ, δ • A = reduce A" API stated, so the project route is shorter).
- Action: publish; make LevelJ:159–257 a 10-line corollary; make `exists_sl2_mul_eq_coxMatrix` a 5-line corollary.

### L2. Publicise the private HNF trio into `HermiteNormalForm.lean`
- `Matrix.rankTwoContent_dvd_mul_left` (`HermiteNormalForm.lean:76`, private): needed for `rankTwoContent_sl_mul : (U.1 * A).rankTwoContent = A.rankTwoContent`, which `Basic.lean:805–811` (`hstarcontent`, `ac_rfl`) and `SingularModuli.lean:141–153` + `:193` circumvent via `matrixStar`.
- `Matrix.rankTwoContent_mul_sl` (`Basic.lean:225–231`, private) → HNF.lean public (uses `U⁻¹` + `_dvd_mul_right`; with `_dvd_mul_left` public also add the left version by the same 6 lines).
- `Matrix.exists_SL2_right_mul_isColumnHermiteNormalForm` (`Basic.lean:343–356`, private aux) → HNF.lean public (14 lines; used at `Basic.lean:390, 797`; needed by L1).
- Plus `rankTwoContent_transpose`/`rankTwoContent_matrixStar` (`Basic.lean:805–808`, `ac_rfl`).
- Saved: ≈ 12 lines + removes two `ac_rfl`-on-gcd hacks (`Basic.lean:222, 808`).
- Action: move + `private` → public; delete `SingularModuli`'s reliance on `matrixStar` order.

### L3. `Matrix.IsColumnHermiteNormalForm.eq_of_mul_isUnit_det` (uniqueness) — DUPLICATE FOUND
`CoxMatrices/Basic.lean:247–286` (`columnHNF_eq_of_mul`, 40 lines) and `HermiteNormalForm.lean:241–278` (`HermiteNormalForm.matrix_eq`, 39 lines) are the SAME proof line-for-line (`hz hz' hd hd' ha ha' hr hr' h00 … hrr'`, `ext i j; fin_cases`). Also `reduced_eq_of_eq_add_mul` (`HermiteNormalForm.lean:232`) ≡ `reduced_eq_of_eq_add_mul_aux` (`Basic.lean:239`).
```lean
theorem Matrix.IsColumnHermiteNormalForm.eq_of_mul_isUnit_det {A B U : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : A.IsColumnHermiteNormalForm) (hB : B.IsColumnHermiteNormalForm) (hU : IsUnit U.det)
    (hmul : A * U = B) : A = B
```
- Home: `HermiteNormalForm.lean` (namespace `Matrix`). Then `HermiteNormalForm.matrix_eq h h'` is 4 lines: `U := h.bN.toMatrix h'.bN`, `IsUnit U.det` from `Module.Basis.toMatrix_mul_toMatrix_flip` (`isUnit_of_mul_eq_one`), `hmul := matrix_mul_toMatrix_eq h h'`.
- Saved: ≈ 43 lines. Action: dedupe; keep one copy in HNF.lean.

### L4. HNF-field extraction quadruple → `Matrix.isColumnHermiteNormalForm_fin_two_iff` (VERIFIED) + `eq_fin_two`
```lean
theorem Matrix.isColumnHermiteNormalForm_fin_two_iff (A : Matrix (Fin 2) (Fin 2) ℤ) :
    A.IsColumnHermiteNormalForm ↔ A 1 0 = 0 ∧ 0 < A 0 0 ∧ 0 < A 1 1 ∧ A 0 1 ∈ Set.Ico 0 (A 0 0)
theorem Matrix.IsColumnHermiteNormalForm.eq_fin_two {A} (h : A.IsColumnHermiteNormalForm) :
    A = !![A 0 0, A 0 1; 0, A 1 1]   -- today private `originalMatrix_eq` CyclicSublattice:300 and `matrix_eq_upper_triangular_aux` LevelJ:203
```
- Sites (7, not 5): `HermiteNormalForm.lean:246–253`, `CoxMatrices/Basic.lean:253–260`, `:362–365`, `CyclicSublattice.lean:75–80`, `:274–291` (three private `d/b/a` + `d_pos/a_pos/lower_left_eq_zero`, 18 lines), `Classification.lean:31–36`, `:63–70`.
- Saved: ≈ 35 lines. Composes from: `Matrix.eta_fin_two` (`LinearAlgebra/Matrix/Notation.lean:464`), `isColumnHermiteNormalForm_fin_two` (HNF:86). Action: add both; replace the 7 blocks by `obtain ⟨hz, hd, ha, hb⟩ := (isColumnHermiteNormalForm_fin_two_iff _).1 h`.

### L5. `Matrix.IsColumnHermiteNormalForm.det_eq` / `det_pos` / `det_ne_zero` via `det_of_upperTriangular` (VERIFIED)
```lean
theorem Matrix.IsColumnHermiteNormalForm.det_eq {A : Matrix (Fin 2) (Fin 2) ℤ}
    (h : A.IsColumnHermiteNormalForm) : A.det = A 0 0 * A 1 1 :=
  by rw [Matrix.det_of_upperTriangular (fun i j hij => h.belowDiagonal_eq_zero i j hij)]; simp [Fin.prod_univ_two]
theorem Matrix.IsColumnHermiteNormalForm.det_pos … : 0 < A.det
```
- Sites (5): `CyclicSublattice.lean:311–313`, `:465–466` (`det_fin_two_of` + `mul_zero, sub_zero`), `Classification.lean:38–40`, `Basic.lean:348–350`, `:366–367`; also `Cox.CoxMatrix.inclusionMatrix_det` (`Basic.lean:67–72`).
- Composes from: `Matrix.det_of_upperTriangular` (`Block.lean:324`; `IsColumnHermiteNormalForm.belowDiagonal_eq_zero` IS `Matrix.BlockTriangular A id`, `Block.lean:61`). Saved ≈ 12 lines; generalises to rank `n`. Action: add to HNF.lean; add `CyclicSublattice.hnf_det_eq : S.hermiteNormalForm.matrix.det = m` (replacing private `d_mul_a_eq_m` `:306–315` and `Classification.lean:37–40`).

### L6. `Matrix.rankTwoContent_fin_two_of` (rfl, VERIFIED), `rankTwoContent_upperTriangular`, and (PR-grade) `rankTwoContent_eq_finset_gcd`
```lean
@[simp] theorem Matrix.rankTwoContent_fin_two_of (d b c a : ℤ) :
    rankTwoContent !![d, b; c, a] = Nat.gcd (Nat.gcd (Nat.gcd d.natAbs b.natAbs) c.natAbs) a.natAbs := rfl
theorem Matrix.rankTwoContent_upperTriangular (d b a : ℤ) :
    rankTwoContent !![d, b; 0, a] = Nat.gcd (Nat.gcd a.natAbs b.natAbs) d.natAbs   -- `simp [rankTwoContent]; ac_rfl`
theorem Matrix.rankTwoContent_eq_finset_gcd (A) :
    (A.rankTwoContent : ℤ) = Finset.univ.gcd (fun p : Fin 2 × Fin 2 ↦ A p.1 p.2)  -- mathlib `Finset.gcd` (Algebra/GCDMonoid/Finset.lean:124); residual `normalize` goal (HNF batch scratch)
```
- AC-gcd idiom sites (7 + 4 `ac_rfl`): `HermiteNormalForm.lean:338`, `CyclicSublattice.lean:475–476`, `Classification.lean:46–47`, `Basic.lean:76–77`, `:377`, `Cardinality.lean:63`, `:82`; `ac_rfl` at `Basic.lean:222`, `:808`, `SingularModuli.lean:148`, `:152`.
- Saved ≈ 15 lines + robustness (the `simpa [Nat.gcd_comm, Nat.gcd_left_comm, Nat.gcd_assoc]` calls are fragile). With `rankTwoContent_eq_finset_gcd`, HNF:48–83 collapse to `Finset.gcd_dvd`/`Finset.dvd_gcd` (`GCDMonoid/Finset.lean:141,144`). Action: add the two rfl/ac lemmas now; keep `_eq_finset_gcd` as PR candidate.

### L7. `CoxMatrix.coprime_gcd_b` (VERIFIED) — the canonical primitivity re-association
```lean
theorem CoxMatrix.coprime_gcd_b (σ : CoxMatrix m) : (Nat.gcd σ.a σ.d).Coprime σ.b
```
- Sites: `Cardinality.lean:63–64`, `:82–83`, `Basic.lean:76–77` (via `inclusionMatrix_content_eq_one`), `LaurentExpansion.lean:324–326` (`reindex` primitivity proof). Saved ≈ 8 lines. Action: add beside `d_pos`.

### L8. `CoxMatrix.ext` `@[ext]` (VERIFIED)
```lean
@[ext] theorem CoxMatrix.ext {σ τ : CoxMatrix m} (ha : σ.a = τ.a) (hb : σ.b = τ.b) (hd : σ.d = τ.d) : σ = τ
```
- Sites (7): `Basic.lean:96–103` (`toFin_injective` → `fun _ _ h ↦ ext (congrArg …) …`), `:288–298` (`inclusionMatrix_injective`), `LaurentExpansion.lean:346–351`, and the ext-substitutes `apply CoxMatrix.toFin_injective; simp [CoxMatrix.toFin, …]` at `Cardinality.lean:91–95`, `Kronecker.lean:67–68`, `:78–79`, `UHPFF.lean:211–212`.
- Saved ≈ 15 lines; removes every `simp [CoxMatrix.toFin]` unfold. Action: add; `toFin` stays only for `Fintype`.

### L9. `CoxMatrix.d_dvd` / `a_dvd` / `div_d` (VERIFIED)
```lean
theorem CoxMatrix.d_dvd (σ : CoxMatrix m) : σ.d ∣ (m : ℕ)      theorem CoxMatrix.a_dvd (σ) : σ.a ∣ (m : ℕ)
theorem CoxMatrix.div_d (σ : CoxMatrix m) : (m : ℕ) / σ.d = σ.a
```
- Sites (5): `Cardinality.lean:56–59`, `:93–94`, `LaurentExpansion.lean:313–314`, `:339–340`, `Kronecker.lean:58`. Saved ≈ 10 lines. Action: add beside `d_pos`.

### L10. `CoxMatrix.ofColumnHNF` smart constructor + `_a/_b/_d`, `inclusionMatrix_ofColumnHNF`
```lean
def CoxMatrix.ofColumnHNF {m : ℕ+} (H : Matrix (Fin 2) (Fin 2) ℤ) (hH : H.IsColumnHermiteNormalForm)
    (hdet : H.det = (m : ℤ)) (hcontent : H.rankTwoContent = 1) : CoxMatrix m
@[simp] theorem CoxMatrix.ofColumnHNF_a … : (ofColumnHNF H hH hdet hcontent).a = (H 1 1).natAbs   -- `_b`, `_d` likewise
@[simp] theorem CoxMatrix.inclusionMatrix_ofColumnHNF … : (ofColumnHNF H hH hdet hcontent).inclusionMatrix = H
```
- Sites (3 copies of the construction): `Basic.lean:358–385` (private aux = the body), `Classification.lean:28–55` (`toCoxMatrix`, tactic-mode, 28 lines) + `:59–75` (`hermiteNormalForm_matrix_eq_inclusionMatrix`, 17 lines, becomes `(inclusionMatrix_ofColumnHNF …).symm`), `Cardinality.lean:66–83` ((a,b,d)-data variant — add a sibling `CoxMatrix.mk'`/keep).
- Saved ≈ 45 lines; `toCoxMatrix_a/_b/_d` then come for free (`Classification.lean:74` `simp [toCoxMatrix, …]` disappears). Composes from L4, L5, L6. Action: define once in Basic.lean; `toCoxMatrix S := ofColumnHNF S.hermiteNormalForm.matrix _ (by rw [hnf_det_eq]) (quotient_isAddCyclic_iff… .mp S.cyclic)`.

### L11. `reindex_a/_b/_d` `@[simp]` + term-mode `reindex`
- `reindex` (`LaurentExpansion.lean:311–326`) is `fun σ ↦ by … refine {…}`; restate as a term-mode structure literal (proof fields `by`), then `@[simp] reindex_a : (reindex k hk σ).a = σ.a := rfl`, `reindex_b … = (σ.b * k) % σ.d`, `reindex_d`.
- Sites: `LaurentExpansion.lean:333, 335, 338`, `FormalCoxProduct.lean:113` (`simp only [reindex]`). Saved ≈ 6 lines; also lets `reindex_bijective` use `CoxMatrix.ext` (L8). Action: do it.

### L12. `CoxMatrix.act_eq_sl2_smul_of_mul` (statement TYPECHECKED) — generic "act (γ·M) = γ • (M·τ)"
```lean
theorem CoxMatrix.act_eq_sl2_smul_of_mul {m : ℕ+} (σ : CoxMatrix m) (γ : SL(2, ℤ))
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : γ.1 * M = σ.mobiusMatrix) (τ w : ℍ)
    (hw : (w : ℂ) = (((M 0 0 : ℤ) : ℂ) * τ + (M 0 1 : ℤ)) / (((M 1 0 : ℤ) : ℂ) * τ + (M 1 1 : ℤ))) :
    σ.act τ = γ • w
```
- Sites: `SingularModuli.lean:155–186` (`coxMatrix_act_eq_smul_aux`, 33 lines; `M := q.fixingMatrix n`, `w := τ` by `q.equation`), `Basic.lean:699–717` (`complex_mobius_scale_eq_affine`, 19 lines) + `:719–761` (`levelJ_smul_eq_j_act_of_normalization`, 43 lines; `M := diag(m,1)·γ`, `w := natScale m (γ • τ)`), `LevelJ.lean:72–90` (third copy of `complex_mobius_scale_eq_affine`, out of scope but same lemma).
- Saved ≈ 80 lines (one 15-line `field_simp`/`linear_combination` proof replaces three). Better long-term: `CoxMatrix.toGL σ : GL (Fin 2) ℝ` with `act_eq_toGL_smul : σ.act τ = σ.toGL • τ` (mathlib `UpperHalfPlane.glAction`, `Analysis/Complex/UpperHalfPlane/MoebiusAction.lean:188`) so that `act` of a product is `mul_smul` (not compiled). Action: add the lemma to `CoxMatrices/Basic.lean` beside `coe_act`.

### L13. `matrixStar` via `submatrix`/`transpose` (identity VERIFIED)
- `matrixStar A = (A.submatrix Fin.rev Fin.rev)ᵀ` (`Basic.lean:154–156`); then `matrixStar_involutive` (:158) = `Matrix.transpose_transpose` + `submatrix_submatrix` + `Fin.rev_rev`; `matrixStar_mul` (:163–168) = `Matrix.transpose_mul` + `Matrix.submatrix_mul_equiv`; `matrixStar_det` (:170–173) = `Matrix.det_transpose` + `Matrix.det_submatrix_equiv_self`; `rankTwoContent_matrixStar` (:805–808) = `ac_rfl`. Saved ≈ 12 lines; generalises to `Fin n`/`CommRing`. Action: redefine and make public (`Matrix.antiTranspose`?), also lets L1/L2 avoid `fin_cases` proofs.

### L14. `Matrix.SpecialLinearGroup.mul_coe_mul_coe_inv` (VERIFIED) + `coe_inv_mul_coe_mul`
```lean
theorem Matrix.SpecialLinearGroup.mul_coe_mul_coe_inv (A : Matrix (Fin 2) (Fin 2) ℤ) (U : SL(2, ℤ)) : A * U.1 * (U⁻¹).1 = A
theorem Matrix.SpecialLinearGroup.coe_inv_mul_coe_mul (U : SL(2, ℤ)) (A) : (U⁻¹).1 * (U.1 * A) = A
```
- Sites (4): `Basic.lean:228–230`, `:405–407`, `:443–446`, `:574–579` (the 5-lemma `rw` chain `coe_mul, ← mul_assoc, mul_inv_cancel, coe_one, mul_one`). Saved ≈ 10 lines. Action: add (or a `MulAction SL(2,ℤ)ᵐᵒᵖ (Matrix …)` instance so `smul_inv_smul` applies).

### L15. `Cox.gamma0_index_eq_card_coxMatrix` (VERIFIED, 5 lines) and `Gamma0_index` (Dedekind ψ)
```lean
theorem Cox.gamma0_index_eq_card_coxMatrix (m : ℕ+) :
    (CongruenceSubgroup.Gamma0 (m : ℕ)).index = Fintype.card (CoxMatrix m) := by
  rw [Subgroup.index_eq_card, Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel
    (s := CongruenceSubgroup.Gamma0 (m : ℕ))).symm, Nat.card_congr (coxMatrixEquivRightCosets m).symm,
    Nat.card_eq_fintype_card]
```
- Never stated anywhere (grep `Gamma0.*index`: 0 hits). Composes from `Subgroup.index_eq_card` (`GroupTheory/Index.lean:348`), `Nat.card_eq_fintype_card`. With L16: `(Gamma0 m).index = ψ(m)` — mathlib `CongruenceSubgroups.lean` has only `instFiniteIndexGamma0` (:206), no index formula → mathlib-worthy. Action: add to `CoxMatrices/Cardinality.lean`.

### L16. ℕ-valued `card_coxMatrix` + `dedekindPsi : ArithmeticFunction ℕ`
```lean
def dedekindPsi : ArithmeticFunction ℕ := ⟨fun n ↦ ∑ d ∈ n.divisors, (d / Nat.gcd (n / d) d) * (Nat.gcd (n / d) d).totient, by simp⟩  -- = `coxDivisorSumArithmeticFunctionAux` Cardinality:205
theorem isMultiplicative_dedekindPsi : dedekindPsi.IsMultiplicative                 -- Cardinality:211
theorem dedekindPsi_prime_pow (hp : p.Prime) (he : 0 < e) : dedekindPsi (p ^ e) = p ^ e + p ^ (e - 1)   -- Cardinality:186
theorem card_coxMatrix_eq_dedekindPsi (m : ℕ+) : Fintype.card (CoxMatrix m) = dedekindPsi m           -- Cardinality:102
theorem card_coxMatrix_prime (p : ℕ+) [Fact p.Prime] : Fintype.card (CoxMatrix p) = p + 1              -- from `primeCoxMatrixEquiv`; hand-derived at LevelThree:733–738
theorem card_coxMatrix (m) : (Fintype.card (CoxMatrix m) : ℚ) = m * ∏ p ∈ m.primeFactors, (1 + 1 / p)   -- existing :270
```
- Sites: `Cardinality.lean:102–111`, `:140–231` (private ψ machinery, 90 lines), `:270` (ℚ only, unused project-wide); `LevelThree.lean:733–738`. Mathlib has NO Dedekind ψ (grep `dedekind psi|dedekindPsi` in NumberTheory: none). Saved: 0 lines, unlocks ℕ formula + `Gamma0_index`. Action: rename privates to public API.

### L17. `Matrix.mul_fin_two` at the entrywise 2×2 sites
- `Matrix.mul_fin_two` (`LinearAlgebra/Matrix/Notation.lean:475`) is used once (`HermiteNormalForm.lean:115`). The idiom `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]` appears at `Basic.lean:167–168`, `:201–202`, `:340–341`, `:464–466`, `:558–560`, `SingularModuli.lean:164`, `LevelJ.lean:120` (7 sites) → `rw [Matrix.eta_fin_two γ.1, Matrix.mul_fin_two]` + `Matrix.ext_iff`/`simp`. Saved ≈ 2 lines/site (14) but mostly removes 7 `fin_cases` case splits. Action: mechanical.

### L18. `laurentqExpansion_polynomialIn` / `laurentqExpansion_pow` / `meromorphicAt_cuspFunction_polynomialIn` (ANALYTIC AGENT — reference only)
```lean
theorem laurentqExpansion_polynomialIn {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : MeromorphicAt (cuspFunction h f) 0) (P : ℂ[X]) :
    laurentqExpansion h (polynomialIn P f) = P.eval₂ (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (laurentqExpansion h f)
```
- My-scope sites: `IntegralDescent.lean:25–52` (28 lines) ≡ `DiagonalLaurent.lean:152–185` (34 lines) verbatim modulo width; `IntegralDescent.lean:54–70` ≡ `DiagonalLaurent.lean:33–55` + `:219–224` (order/leadingCoeff/lowest-coefficient at width 1 vs m); `LevelThree.lean:715–725` (`norm_num` cast shims of the width-m lemmas at m = 3). Saved ≈ 60 lines. Home: `LaurentQExpansion/Algebra.lean`.

### L19. `LaurentSeries.coeff_single_neg_mul_coe_expand` (statement TYPECHECKED; proof = KF:104–139 skeleton, not verified)
```lean
theorem LaurentSeries.coeff_single_neg_mul_coe_expand {R : Type*} [CommRing R] (N : ℕ) (hN : N ≠ 0) (F : PowerSeries R) (k : ℤ) :
    (HahnSeries.single (-(N : ℤ)) (1 : R) * (F.expand N hN : LaurentSeries R)).coeff k =
      if (N : ℤ) ∣ k ∧ -(N : ℤ) ≤ k then PowerSeries.coeff ((k / N + 1).toNat) F else 0
```
- Sites (≥ 5, ≈ 180 lines): `Kronecker.lean:389–411` + `:412–424` + `:444–458` (`jUnitPrimeNormalForm_coeff_mul_of_lower/_of_lt/_of_not_dvd`, N = p), `KroneckerFrobenius.lean:104–139` (N = p²), `:77–96` (N = 1 variant), `LevelThree.lean:577–600` (N = 3), `:609–636` (N = 9); plus the three private `dvd ↔ dvd natAbs` shims `KF:98–102`, `LevelThree:559–575` that exist only for these blocks.
- Composes from: `HahnSeries.coeff_single_mul` (`HahnSeries/Multiplication.lean:471`), `LaurentSeries.coeff_coe_powerSeries` (`LaurentSeries.lean:204`), `PowerSeries.coeff_expand` (`PowerSeries/Expand.lean:110`), `HahnSeries.embDomain_notin_range` (`HahnSeries/Basic.lean:477`), `Int.toNat_of_nonneg`. Saved ≈ 140 lines. Home: `LaurentPolynomialEvaluation.lean` (or a new `LaurentSeriesLemmas.lean`). Action: prove once (≈ 15 lines), rewrite the 5 sites as `rw [coeff_single_neg_mul_coe_expand]; split_ifs`.

### L20. `Cox.jLaurentSeriesWidth R m` (def VERIFIED) — one series instead of four — and the CORRECT `sigmaZero` identity
```lean
noncomputable def jLaurentSeriesWidth (R : Type*) [Ring R] (m : ℕ+) : LaurentSeries R :=
  HahnSeries.ofSuppBddBelow (fun k ↦ if (m : ℤ) ∣ k ∧ -(m : ℤ) ≤ k then (jIntCoeff (k / m) : R) else 0) ⟨-(m : ℤ), …⟩
@[simp] theorem jLaurentSeriesWidth_coeff … := rfl
theorem jLaurentSeriesWidth_map (f : R →+* S) (m) : (jLaurentSeriesWidth R m).map f = jLaurentSeriesWidth S m
theorem jLaurentSeriesWidth_eq_single_mul_expand (R) (m : ℕ+) :
    jLaurentSeriesWidth R m = HahnSeries.single (-(m : ℤ)) 1 *
      ((PowerSeries.mk fun n ↦ (jIntCoeff ((n : ℤ) - 1) : R)).expand m (PNat.ne_zero m) : LaurentSeries R)   -- via L19
theorem jLaurentSeriesWidth_order [Nontrivial R] (m) : (jLaurentSeriesWidth R m).order = -(m : ℤ)          -- via L23
theorem jLaurentSeriesWidth_leadingCoeff [Nontrivial R] (m) : … = 1
theorem transformedJSeries_sigmaZero {K} [Field K] (ζ : K) (m : ℕ+) :
    transformedJSeries ζ (sigmaZero m) = jLaurentSeriesWidth K ⟨m * m, _⟩     -- `b = 0` kills the phase; `a² = m²`
```
- Instances: `jIntegralLaurentSeries` (`Kronecker.lean:160–169`) = `jLaurentSeriesWidth ℤ 1`; `jIntegralLaurentSeriesWidth m` (`:184–195`) = `jLaurentSeriesWidth ℤ m`; `jUnitLaurentSeriesMod p` (`:244`) = `jLaurentSeriesWidth (ZMod p) 1`; `jLaurentSeriesMod p` (`:300–311`) = `jLaurentSeriesWidth (ZMod p) p`; `unitJPowerSeries K` (`KF.lean:66–68`) = `(jLaurentSeriesWidth K 1).powerSeriesPart`; `qjIntegralPowerSeriesThree` (`LevelThree.lean:132`) same; `widthLaurentSeriesThree`/`sigmaLaurentSeriesThree` (`LevelThree.lean:141–145`) = widths 3 and 9.
- CORRECTION to the task prompt / Kronecker inventory: "`jLaurentSeriesMod p = transformedJSeries 1 (sigmaZero p)`" is FALSE — `transformedJSeries ζ (sigmaZero p)` is supported on `p² ∣ k` (`a = p`), `jLaurentSeriesMod p` on `p ∣ k`; the true relation is `transformedJSeries 1 (sigmaZero p) = jLaurentSeriesMod p ^ p` (already `KF.lean:177–187`) and, structurally, `transformedJSeries ζ (sigmaZero m) = jLaurentSeriesWidth K (m*m)` (the `_eq_expand` statement above). What IS a one-line `ext`: `jLaurentSeriesMod p = (jIntegralLaurentSeriesWidth p).map _` (exists: `Kronecker.lean:320–328`).
- Saved: 4 `isPWO_support'` blocks (`Kronecker.lean:162–169, 187–195, 303–311`, `LaurentExpansion.lean:56–64`, `Kronecker.lean:579–587` = 5 × 8 lines) via `HahnSeries.ofSuppBddBelow` (`HahnSeries/Basic.lean:574`); `jUnitLaurentSeriesMod_order` (`:263–280`) ≡ `jLaurentSeriesMod_order` (`:339–359`) → one lemma; `KF.lean:66–139` (74 lines) → 3; `LevelThree.lean:577–636` (60 lines) → 4 (`widthLaurentSeriesThree = jLaurentSeriesWidth ℤ 3` by `rfl`/`_eq_single_mul_expand`). Total ≈ 200 lines. Action: do it in `Kronecker.lean`; move `jIntCoeff_eq_zero_of_lt` (`Kronecker.lean:149`) to `LaurentExpansion.lean:38` beside `jIntCoeff_neg_one` as `jIntCoeff_of_lt_neg_one` and use it to drop the redundant `-(a²) ≤ k` clause in `transformedJSeries` (`LaurentExpansion.lean:52, 69`).

### L21. `LaurentSeries.substMonomial` (def TYPECHECKED via `ofSuppBddBelow`, BddBelow proof pending) + analytic bridge (ANALYTIC AGENT)
```lean
noncomputable def LaurentSeries.substMonomial {K} [Field K] (c : K) (r : ℕ) (F : LaurentSeries K) : LaurentSeries K :=
  HahnSeries.ofSuppBddBelow (fun k ↦ if (r : ℤ) ∣ k then c ^ (k / r) * F.coeff (k / r) else 0) _
@[simp] theorem coeff_substMonomial … ;  theorem substMonomial_map (f : K →+* L) : (substMonomial c r F).map f = substMonomial (f c) r (F.map f)
theorem substMonomial_one_eq_embDomain (r) : substMonomial 1 r F = HahnSeries.embDomain ⟨(r * ·), …⟩ F   -- mathlib `HahnSeries.embDomain` Basic.lean:441, `embDomainRingHom` Multiplication.lean:899
```
- Two series defs are instances: `transformedJSeries ζ σ` (`LaurentExpansion.lean:50`) = `substMonomial (ζ^(σ.a*σ.b)) (σ.a^2) (jLaurentSeriesWidth K 1)`; `cyclotomicTransformedJSeries p σ` (`Kronecker.lean:572`) = same with phase `phasePolynomial p (σ.a*σ.b)` over `ℤ[X]` (needs a phase-hom generalisation: `φ : Multiplicative ℤ →* K`). Then `transformedJSeries_map` (`FormalCoxProduct.lean:29`, private), `cyclotomicTransformedJSeries_map_complex/_map_mod` (`Kronecker.lean:607–643`, 37 lines) and `cyclotomicCoxPolynomial_map_complex/_map_mod` (`:651–666`) are ONE `substMonomial_map`. Together with the analytic bridge `laurentqExpansion_comp_of_qParam_eq` (LaurentExpansion inventory; analytic agent), `LaurentExpansion.lean:93–300` (≈ 180 lines) collapses. Saved (algebraic side only) ≈ 60 lines. Action: introduce `substMonomial` in LPE; restate `transformedJSeries` through it.

### L22. `HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt` (VERIFIED, 2 lines)
```lean
theorem HahnSeries.order_eq_of_coeff_ne_zero_of_forall_lt {x : HahnSeries Γ R} {g : Γ}
    (h : x.coeff g ≠ 0) (h' : ∀ i < g, x.coeff i = 0) : x.order = g :=
  le_antisymm (order_le_of_coeff_ne_zero h) ((le_order_iff_forall (ne_zero_of_coeff_ne_zero h)).2 h')
```
- Sites (4): `Kronecker.lean:263–280` (18 → 4), `:339–359` (21 → 4), `DiagonalLaurent.lean:257–262` (`htop` block), `:65–77` (`transformedJSeries_order`, 13 → 4). Composes from `HahnSeries.order_le_of_coeff_ne_zero` (Basic:383), `le_order_iff_forall` (Basic:552), `ne_zero_of_coeff_ne_zero` (Basic:126). Saved ≈ 45 lines. Action: add to LPE (upstream candidate).

### L23. `polynomial_eval₂_laurentSeries_{coeff_eq_zero_of_lt, order, leadingCoeff}` in LPE + `HahnSeries.leadingCoeff_pow` (VERIFIED)
```lean
theorem Cox.polynomial_eval₂_laurentSeries_coeff_eq_zero_of_lt {K} [CommRing K] [IsDomain K] (J) (w) (hw : 0 < w)
    (horder : J.order = -(w : ℤ)) (P : K[X]) {k : ℤ} (hk : k < -((w : ℤ) * P.natDegree)) : (P.eval₂ HahnSeries.C J).coeff k = 0
theorem Cox.polynomial_eval₂_laurentSeries_order … (hP : P ≠ 0) : (P.eval₂ HahnSeries.C J).order = -((w : ℤ) * P.natDegree)   -- typechecked
theorem Cox.polynomial_eval₂_laurentSeries_leadingCoeff … : (P.eval₂ HahnSeries.C J).leadingCoeff = P.leadingCoeff
theorem HahnSeries.leadingCoeff_pow [NoZeroDivisors R] (x) (n) : (x ^ n).leadingCoeff = x.leadingCoeff ^ n   -- VERIFIED 3-line induction; NOT in mathlib (grep `leadingCoeff_pow` in RingTheory/HahnSeries: none)
```
- Sites: `DiagonalLaurent.lean:226–242`, `:244–266` (41 lines at `K = ℂ`, `J = laurentqExpansion m j`, nothing ℂ-specific used), `LPE.lean:103–110` (`laurentSeries_pow_leadingCoeff_of_eq_one`) + `SymmetricCubicLaurent.lean:160–165` (both instances of `leadingCoeff_pow`); the `[Field K]` in LPE:93–149 can be `[CommRing K] [IsDomain K]`. Saved ≈ 40 lines. Action: move/generalise.

### L24. `HahnSeries.coeffSubring` (VERIFIED) + `HahnSeries.mapRingHom` (VERIFIED with `[AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]`) + `laurentSeriesMapRingHom_apply`
```lean
def HahnSeries.coeffSubring [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Ring R] (S : Subring R) : Subring (HahnSeries Γ R)
    -- carrier {x | ∀ g, x.coeff g ∈ S}
def HahnSeries.mapRingHom [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R] [Semiring S] (f : R →+* S) : HahnSeries Γ R →+* HahnSeries Γ S
@[simp] theorem Cox.laurentSeriesMapRingHom_apply (f) (F) : laurentSeriesMapRingHom f F = F.map f := rfl
```
- Sites: `IntegralDescent.lean:72–94` (`integerCoeffLaurentSeries`, 23 lines → `coeffSubring (Int.castRingHom ℂ).range`), `FormalCoxProduct.lean:51–72` (`integralLaurentSeries`, 22 lines → `coeffSubring (integralClosure ℤ K).toSubring`; its `[CharZero K]` is unused), `LPE.lean:22–28` and `FormalCoxProduct.lean:42–46` (two hand-built ring homs), `IntegralPowerSeries.lean:150` (`IntegralPowerSeriesSubring`, analytic scope). The `rfl`-reliance between `F.map f` and `laurentSeriesMapRingHom f F` (`Kronecker.lean:501–503, 518–521` `exact` by defeq; `LevelThree.lean:650–654` `change`) disappears with the `_apply` simp lemma. Mathlib has neither (`grep mapRingHom|Subring` in `RingTheory/HahnSeries/*`, `LaurentSeries.lean`: none). Saved ≈ 50 lines; both are PR candidates. Action: add to LPE (or `ForMathlib/HahnSeries.lean`).

### L25. `BivariatePolynomial.map` as a ring hom (`map_neg/map_sub/map_add/map_mul` free) + `modularPolynomial_map_complex_swap` + `modularPolynomialC_swap`
```lean
abbrev BivariatePolynomial.mapRingHom (f : R →+* S) : BivariatePolynomial R →+* BivariatePolynomial S := Polynomial.mapRingHom (Polynomial.mapRingHom f)
theorem modularPolynomial_map_complex_swap (m : ℕ+) :
    BivariatePolynomial.map (Int.castRingHom ℂ) (Polynomial.Bivariate.swap (modularPolynomial m)) = Polynomial.Bivariate.swap (modularPolynomialC m)
theorem modularPolynomialC_swap (m : ℕ+) (hm : 1 < (m : ℕ)) : Polynomial.Bivariate.swap (modularPolynomialC m) = modularPolynomialC m  -- MISSING as a named theorem: hand-derived at Arithmetic:341–344 and assumed as hypothesis `hsymm` throughout LevelThree:759–856
```
- Sites: `Arithmetic.lean:128–132`, `:192–198` (7-line `map_neg` detour with `change`), `:341–344`; `BivariatePolynomial.map` unfolded by `simp only [BivariatePolynomial.map]` at `Kronecker.lean:504, 522`, `LevelThree.lean:742, 750`, `Arithmetic.lean:195`, `Construction.lean:113, 130`, `IntegralDescent.lean:301` (8 sites). Saved ≈ 25 lines. Action: add both lemmas to `IntegralDescent.lean`/`Arithmetic.lean`; mark `BivariatePolynomial.map_swap` `@[simp]`.

### L26. `modularPolynomialC_eval_act_j` and `formalCoxPolynomial_eval_transformedJSeries`
```lean
theorem modularPolynomialC_eval_act_j (m : ℕ+) (σ : CoxMatrix m) (τ : ℍ) : (modularPolynomialC m).eval (j (σ.act τ)) (j τ) = 0
theorem formalCoxPolynomial_eval_transformedJSeries {K} [Field K] (m) (ζ : K) (σ) : (formalCoxPolynomial m ζ).eval (transformedJSeries ζ σ) = 0
```
- Sites replaying `specializeY_eval, modularPolynomialC_specializeY, coxPhiAtJ, eval_prod, prod_eq_zero (mem_univ σ)`: `Construction.lean:362–369` (`_eval_levelJ_j` = `σ := sigmaZero m` + `j_act_sigmaZero`), `SingularModuli.lean:209–216`, `LevelThree.lean:689–700` (`m = 3, σ = σ₀`, Laurent version), `Irreducibility.lean:71–79` (function-field version), `Classification.lean:330–333`. Saved ≈ 20 lines, and `SingularModuli`/`LevelThree` stop unfolding `coxPhiAtJ`. Action: add both right after `modularPolynomialC_specializeY` / `formalCoxPolynomial`.

### L27. `BivariatePolynomial.diagonal_coeff_one` (move) + `diagonal_coeff_zero`
- `Arithmetic.lean:239–256` private, `[CommRing R]` → `[CommSemiring R]`; belongs beside `diagonal_eval/_map/_swap` (`Construction.lean:116–156`). Action: move + generalise.

### L28. `LevelOneCuspData.of_widthM` + `Polynomial.prod_X_sub_C_coeff_mem` (the A15 pipeline, duplicated 2–3×)
```lean
theorem LevelOneCuspData.of_widthM {m : ℕ+} {f : ℍ → ℂ}
    (hH : ∀ z : ℂ, 0 < z.im → MeromorphicAt (f ∘ UpperHalfPlane.ofComplex) z)
    (hslash : ∀ δ : SL(2, ℤ), f ∣[(0 : ℤ)] δ = f)
    (hcusp : MeromorphicAt (cuspFunction ((m : ℕ) : ℝ) f) 0) : LevelOneCuspData f
theorem Polynomial.prod_X_sub_C_coeff_mem {R ι} [CommRing R] (S : Subring R) (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, f i ∈ S) (n : ℕ) : (∏ i ∈ s, (X - C (f i))).coeff n ∈ S
    -- `(lifts_iff_coeff_lifts _).1 (Subring.prod_mem (Polynomial.liftsRing S.subtype) …)`; mathlib `Polynomial.liftsRing` (Lifts.lean:209), `lifts_iff_coeff_lifts` (:72)
```
- Sites: `Interpolation.lean:262–289` ≡ `Construction.lean:250–277` (level-one descent: `meromorphicAt_cuspFunction_of_nat_mul` + `periodic_comp_of_slashInvariant_one` + `hfun`); `AnalyticSupport.lean:40–58, 61–80` ≡ `Interpolation.lean:141–154, 156–173` (coefficient closure, MDiff vs cusp-meromorphic, 85 lines); `Construction.lean:212–236` and `IntegralDescent.lean:200–214` (hand Vieta `Finset.prod_X_add_C_coeff`). Requires `holomorphicFunctions` (`FieldAction.lean:26`, exists) and a new `cuspMeromorphicSubring h : Subring (ℍ → ℂ)` (needs `meromorphicAt_cuspFunction_neg`, today `const (-1) * _` at `AnalyticSupport.lean:48–50`, `IntegralDescent.lean:180–183`). Saved ≈ 130 lines. Action: add both; analytic-agent coordination for `cuspMeromorphicSubring`.

### L29. `HolomorphicFunction.ext` / `evaluation_apply` / `evaluation_comp_evalJ` / `evalJFracPoly_comp_eq`
```lean
@[ext] theorem HolomorphicFunction.ext {f g : HolomorphicFunction} (h : ∀ τ, f.1 τ = g.1 τ) : f = g
@[simp] theorem evaluation_apply (τ) (f : HolomorphicFunction) : evaluation τ f = f.1 τ := rfl
theorem evaluation_comp_evalJ (τ : ℍ) : (evaluation τ).comp evalJ = Polynomial.evalRingHom (j τ)
theorem algebraMap_ratFunc_comp_algebraMap : (algebraMap (RatFunc ℂ) FunctionField).comp (algebraMap ℂ[X] (RatFunc ℂ)) = evalJFracPoly
```
- Sites: `Subtype.ext; funext` at `UHPFF.lean:122–125`, `:259–261`, `Arithmetic.lean:65–66`, `Irreducibility.lean:35–36`, `Interpolation.lean:457–458`, `MFF.lean:97–100`; `congrArg (fun f ↦ f.1 τ)` at `UHPFF.lean:81`, `:239` (8 sites); `evaluation_comp_evalJ` inline at `MFF.lean:41–42`, `Arithmetic.lean:69–72`; the two-route `Polynomial.map` reconciliation at `Arithmetic.lean:79–88`, `Irreducibility.lean:53–60`. Saved ≈ 30 lines. Action: add to `UHPFF.lean`.

### L30. `evalJLevel_mem_jLevelFunctionField` via mathlib adjoin API
- `MFF.lean:135–149` (15 lines) = `Algebra.adjoin_singleton_eq_range_aeval` (`RingTheory/Adjoin/Polynomial/Basic.lean:52`) + `IntermediateField.algebra_adjoin_le_adjoin` (`Adjoin/Algebra.lean:30`) once `evalJLevel_eq_aeval_map : evalJLevel N P = Polynomial.aeval (levelJFieldElement N) (P.map (algebraMap ℂ[X] (RatFunc ℂ)))` (from `Polynomial.hom_eval₂` + `ratFuncEvalJ_algebraMap`); `theorem_11_9_ii` second inclusion (`:182–184`) = `IntermediateField.adjoin_simple_le_iff` (`Adjoin/Defs.lean:583`) with `F⟮α⟯` notation; `toMeromorphicField_mem_jLevelFunctionField` (`:152–158`) = `IntermediateField.mem_adjoin_simple_iff` (`Adjoin/Basic.lean:61`). Saved ≈ 15 lines. Action: restate `jLevelFunctionField N := (RatFunc ℂ)⟮levelJFieldElement N⟯`.

### L31. `indexUnit`/`CoxMatrix.dUnit` public (`Units.mk0` ×8)
```lean
def PNat.complexUnit (m : ℕ+) : ℂˣ := Units.mk0 (m : ℂ) (by exact_mod_cast m.ne_zero)   -- today private `indexUnit` CyclicSublattice:485
def CoxMatrix.dUnit (σ : CoxMatrix m) : ℂˣ := Units.mk0 (σ.d : ℂ) (by exact_mod_cast σ.d_pos.ne')
```
- Sites: `CyclicSublattice.lean:486, 515, 523, 528`; `Classification.lean:264, 266, 297, 313`. Saved ≈ 8 lines + statement readability of `dual_carrier_map_subtype`, `coxMatrix_toPeriodPair_lattice`. Action: add with `@[simp] coe_` lemmas.

### L32. Integrality as subring membership, not `∃ z : ℤ`
- `∃ z : ℤ, … = (z : ℂ)` at `FormalCoxProduct.lean:168, 213`, `IntegralDescent.lean:107–109, 117–120, 146, 235`, and unpacked by hand at `IntegralDescent.lean:98–100, 124–127, 139–142, 237–239`; source `j_laurentQExpansion_isIntegral` (`jfunction.lean:493`). Restate as `∈ (Int.castRingHom ℂ).range` (or `∈ HahnSeries.coeffSubring …`, L24); `jIntCoeff_spec` then gives membership directly. Saved ≈ 15 lines; removes 4 `obtain ⟨z, hz⟩ … ⟨z, hz.symm⟩` dances. Action: change statements (4) + consumers.

### L33. `PeriodPair.smul_lattice_eq_span` + `Submodule.coe_add/coe_smul` simp
```lean
theorem PeriodPair.smul_lattice_eq_span (a : ℂˣ) (L : PeriodPair) : (a • L).lattice = Submodule.span ℤ {a * L.ω₁, a * L.ω₂}
```
- Sites: `Classification.lean:261–278` (18 lines → 2 rewrites), `:224–243` (`coe_sublatticeGenerators`, 20 lines; the local `hcoe_add/hcoe_zsmul` are mathlib `Submodule.coe_add`/`coe_smul`). Composes from `PeriodPair.smul_ω₁/₂` (`LatticeJ.lean:46/48`, simp), `PeriodPair.lattice` def. Saved ≈ 25 lines. Home: `LatticeJ.lean` (analytic agent's file; algebraic consumer).

### L34. `Matrix.toLin_injective_of_det_ne_zero`
```lean
theorem Matrix.toLin_injective_of_det_ne_zero {R M ι} [CommRing R] [IsDomain R] … (b : Basis ι R M) {A : Matrix ι ι R}
    (hA : A.det ≠ 0) : Function.Injective (Matrix.toLin b b A)
```
- Sites: `Classification.lean:98–110` ≡ `HermiteNormalForm.lean:376–389` (converse direction: injective ⇒ det ≠ 0; both from `LinearMap.det_toMatrix` + `LinearMap.det_eq_zero_iff_ker_ne_bot`). Mathlib has only `Matrix.ker_toLin_eq_bot` for `IsUnit A.det` (`ToLinearEquiv.lean:95`) and `ker_toLin'_eq_bot_iff` (`ToLin.lean:484`). Also `letI Module.Free/Finite of_basis` ×3 (`HNF:372–373`, `CyclicSublattice:45–46`, `Classification:100–101`). Saved ≈ 20 lines. Action: add (iff form) to HNF.lean; upstream.

### L35. `IsImaginaryQuadratic` characterisation + `SL₂` invariance (not compiled)
```lean
theorem isImaginaryQuadratic_iff_minpoly_natDegree (τ : ℍ) : IsImaginaryQuadratic τ ↔ IsIntegral ℚ (τ : ℂ) ∧ (minpoly ℚ (τ : ℂ)).natDegree = 2
theorem isImaginaryQuadratic_smul (γ : SL(2, ℤ)) (τ : ℍ) : IsImaginaryQuadratic (γ • τ) ↔ IsImaginaryQuadratic τ
theorem PrimitiveQuadraticEquation.fixingMatrix_smul_eq (q) (n) : (q.fixingMatrix n as GL-action) • τ = τ   -- the content of `q.equation`, currently inlined in `coxMatrix_act_eq_smul_aux`
```
- No current sites (API completeness for `SingularModuli.lean:25–43`); needed to state Cox 11.1 fully. Mathlib pieces: `discrim` (`Algebra/QuadraticDiscriminant.lean:48`), `Polynomial.IsPrimitive` (`RingTheory/Polynomial/Content.lean:45`), `minpoly`. Action: add as companions.

### L36. `exists_positive_nonsquare_det` — one lemma instead of two 28-line twins
- `SingularModuli.lean:74–101` ≡ `:103–130` (`k`, `D := k² + c`, `N := D.toNat`, three `nlinarith`). Factor: `exists_nonsquare_det_of_sq_add {k c : ℤ} (hk : 0 < k) (hc : 0 < c) (hc' : c ≤ 2 * k) (n) (hdet : (q.fixingMatrix n).det = k ^ 2 + c) : ∃ N : ℕ+, det = N ∧ ¬ IsSquare (N : ℕ)` (≈ 12 lines), then the two parity cases are 4 lines each; or avoid parity via `4 * det (M n) = (2n + B)² + (4AC − B²)`. Saved ≈ 30 lines. Action: refactor.

### L37. `Nat.not_isSquare_of_lt_of_lt` (corollary of mathlib `Nat.not_exists_sq'`)
```lean
theorem Nat.not_isSquare_of_lt_of_lt {k N : ℕ} (hl : k ^ 2 < N) (hr : N < (k + 1) ^ 2) : ¬ IsSquare N :=
  fun ⟨t, ht⟩ ↦ Nat.not_exists_sq' hl hr ⟨t, by rw [sq]; exact ht.symm⟩
```
- Site: `SingularModuli.lean:59–72` (`not_isSquare_of_between_sq_aux`, 14 lines, ℤ-cast form). Mathlib: `Nat.not_exists_sq'` (`Data/Nat/Sqrt.lean:213`). Saved ≈ 10 lines. Action: replace (lift `k : ℤ`, `0 ≤ k` to ℕ at the 2 call sites).

### L38. `formalCoxPolynomial_monic` / `_natDegree` / `_map` public
```lean
theorem formalCoxPolynomial_monic (m) (ζ) : (formalCoxPolynomial m ζ).Monic        -- `Polynomial.monic_prod_X_sub_C` (Algebra/Polynomial/Roots.lean:775)
theorem formalCoxPolynomial_natDegree (m) (ζ) : (formalCoxPolynomial m ζ).natDegree = Fintype.card (CoxMatrix m)   -- `natDegree_prod_of_monic` (BigOperators.lean:216)
theorem formalCoxPolynomial_map (φ : K →+* L) : (formalCoxPolynomial m ζ).map (HahnSeries.mapRingHom φ) = formalCoxPolynomial m (φ ζ)   -- today private `FormalCoxProduct.lean:39`
theorem formalCoxPolynomial_coeff_eq_int … (generic cyclotomic K)                     -- today private `:163`, only the ℂ corollary `:211` public
```
- Consumers that would use them: `KF.lean:41–64` (degree p+1 factorisation), `DiagonalLaurent.lean:189` (degree matching), `Kronecker.lean:651–666` (the `_map` twins). Action: publish.

### L39. LevelThree: one `decide +kernel` certificate + `TriangularCoeffsVanish`
Target statements (replace `LevelThree.lean:349–502` (35 private decls, 154 lines) and `:518–557` (40-line conjunction)):
```lean
private def observedIndices : Finset ℕ := {0, 3, 6, 9, 12, 15, 18, 24, 27, 36}
private theorem explicitCandidateClearedJetThree_observed :
    ∀ n ∈ observedIndices, explicitCandidateClearedJetThree n = 0 := by decide +kernel      -- measured 6.7 s (batch M)
/-- the ten triangular exponents, as a predicate shared by SCL and LevelThree -/
def TriangularCoeffsVanish (E : LaurentSeries K) : Prop := ∀ n ∈ observedIndices, E.coeff ((n : ℤ) - 36) = 0
theorem TriangularCoeffsVanish.map (f : K →+* L) : TriangularCoeffsVanish E → TriangularCoeffsVanish (E.map f)
theorem TriangularCoeffsVanish.neg : TriangularCoeffsVanish E → TriangularCoeffsVanish (-E)
```
and restate `symmetric_bidegree_three_eq_zero_of_laurent_coeff` (`SymmetricCubicLaurent.lean:368–389`, 10-fold `∧` under a `let`) with `hcoeff : TriangularCoeffsVanish (P.eval₂ … T)`; then `LevelThree.lean:518–557`, `:675–687`, `:806–819` (three copies of the 10-conjunction transported along `Int.cast`/`neg`) become `.map`/`.neg`. If in-context kernel time exceeds budget keep only the 10 per-coefficient `decide +kernel` lemmas (not the per-term/per-chunk split `:380–458`). Saved ≈ 220 lines. Also: hard-coded window `37`/shift `36` in `:249–283`, `:168` → parameters; `jetMul/jetPow/jetShift/jetExpand` (`:94–105`) duplicate `qExpansion_tactic/Qj.lean` computable layer (`convArrayUpTo`, `qjCoeffInt`) → shared kernel-evaluable jet API. Action: do the collapse; measure.

### L40. `zeta_ne_zero` (6 re-derivations) + `zeta_pow_eq_one`, `zeta_zpow_mul_natCast`
```lean
theorem zeta_ne_zero (m : ℕ+) : zeta m ≠ 0 := (zeta_isPrimitiveRoot m).ne_zero (PNat.ne_zero m)
theorem zeta_pow_eq_one (m) : zeta m ^ (m : ℕ) = 1
```
- Sites: `DiagonalLaurent.lean:97`, `UHPFF.lean:152`, `:186`, `LevelThree.lean:705`, `:712`, `Kronecker.lean:557`. Saved ≈ 6 lines. Action: add to `LaurentExpansion.lean:26`.

### L41 (extra). `CuspData.apply_smul` — the Γ₀-lift + `SL_slash_apply` idiom
```lean
theorem CuspData.apply_smul {N} {f} (hf : CuspData N f) (γ : CongruenceSubgroup.Gamma0 (N : ℕ)) (τ : ℍ) : f ((γ : SL(2, ℤ)) • τ) = f τ
```
- Sites: `Basic.lean:617–623`, `CuspData.lean:104–107, 144–146`, `Interpolation.lean:283–286`, `ModularFunction.lean:46–49, 344–349`, `Congruence.lean:75`. Saved ≈ 20 lines. Home: `CuspData.lean` (analytic agent; algebraic consumers).

---

## 2. Missing simp lemmas / simp families

`@[simp]` counts in scope: HNF 1, CyclicSublattice 8 (4 on private, 3 unused), Classification 4, Basic 6 (2 on privates), Cardinality 1 (private), LaurentExpansion 0, FormalCoxProduct 0, AnalyticSupport 0, Construction 2, IntegralDescent 0, Interpolation 0, Irreducibility 0, LPE 1, DiagonalLaurent 0, SCL 2 (private), Kronecker 11, KF 1 (private), LevelThree 1 (private, dead), Arithmetic 0, SingularModuli 1, UHPFF 4, MFF 2. Total 45 for ≈ 8,150 lines.

| Definition (file:line) | Existing simp/API | Missing | Manual `simp only [def]`/`unfold`/`change` sites |
|---|---|---|---|
| `CoxMatrix` fields (Basic:24) | none needed (projections) | `@[ext]` (L8) | — |
| `sigmaZero` (Basic:113) | none | `@[simp] sigmaZero_a/_b/_d` | 9: `Kronecker:79, 94, 101`, `LevelThree:616, 706, 713`, `KF:113`, `Basic:475, 789` |
| `primeLowerCoxMatrix` (Kronecker:32) | none | `_a/_b/_d` | `Kronecker:68, 89, 94, 101`, `KF:32` |
| `inclusionMatrix` (Basic:56) | `_det`, `_isColumnHNF`, `_content_eq_one` (none simp) | `@[simp] inclusionMatrix_apply_{00,01,10,11}` (rfl, VERIFIED), `inclusionMatrix_eq : = !![d,b;0,a]` | 8: `Basic:294, 382–385, 475, 518, 521`, `Classification:74, 218` |
| `mobiusMatrix` (Basic:52) | none | entry lemmas, `mobiusMatrix_det : = m` (never stated; `coxInput_det` used instead), `matrixStar_mobiusMatrix` public | `Basic:751`, `SingularModuli:164` |
| `matrixStar` (Basic:154, private) | none | `matrixStar_apply` / redefinition (L13) | `Basic:161, 168, 172, 178, 202, 806` |
| `act` (Basic:80) | `@[simp] coe_act` | `act_sigmaZero : (sigmaZero m).act τ = ⟨m*τ,_⟩` (`j_act_sigmaZero` :784 is the funext form), GL-action bridge (L12) | `Basic:789`, `Arithmetic:284`, `LevelJ:270` |
| `coxRepresentative` (Basic:413, private) | `_one` (:477), `_normalization` | fine (private) | — |
| `reindex` (LaurentExpansion:311) | none | `reindex_a/_b/_d` (L11), `reindex_one`, `reindex_mul` | 4 (see L11) |
| `zeta` (LaurentExpansion:24) | `zeta_isPrimitiveRoot` | `zeta_ne_zero`, `zeta_pow_eq_one` (L40) | 6 |
| `jIntCoeff` (LaurentExpansion:31) | `jIntCoeff_spec` (10 uses), `jIntCoeff_neg_one` (not simp), `jIntCoeff_eq_zero_of_lt` (Kronecker:149, misplaced) | `@[simp] jIntCoeff_neg_one`, `jIntCoeff_of_lt_neg_one` beside it, public `jIntCoeff_eq_qjCoeffInt` (LevelThree:122 private) | `LevelThree:122–130`, `Kronecker:154–157` |
| `transformedJSeries` (LaurentExpansion:50) | `_coeff` (rfl, NOT simp; 17 uses/7 files), `_order`, `_leadingCoeff` (DiagonalLaurent:65/80) | `@[simp]` on `_coeff`; `_map` public (FormalCoxProduct:29 private); `_sigmaZero` (L20); `_coeff_mul_sq`/`_coeff_of_not_dvd`; `transformedJSeries_coeff_order` (DiagonalLaurent:56 private) ≡ `transformed_leading` (UHPFF:140 private) — DUPLICATE, publish once | `LaurentExpansion:267`, `DiagonalLaurent:60, 74`, `FormalCoxProduct:33, 79, 112`, `Kronecker:614, 633`, `KF:31, 112`, `UHPFF:143, 163`, `LevelThree:615` |
| `BivariatePolynomial.{eval,map,swap,diagonal,specializeY}` (Construction:26–54) | `diagonal_swap` @[simp]; `specializeY_eval`, `eval_swap`, `coeff_coeff_swap`, `map_swap`, `diagonal_eval/_map/_eval₂` (none simp) | `@[simp]` on the six; `eval_add/_mul/_sub/_neg/_C/_X/_varX/_varY`; `map_add/_sub/_neg/_mul/_one/_pow/_map/_id`, `map_monic`, `natDegree_map` (LevelThree:740–751 hand-rolled), `map_intCast` (LevelThree:311); `specializeY_coeff : (specializeY y Φ).coeff n = (Φ.coeff n).eval y` (re-derived at `Construction:83, 311`, `Irreducibility:43`, `IntegralDescent:272`); `specializeY_add/_mul/_map`; `varX/varY` lemmas (zero exist) | 12 `simp only [BivariatePolynomial.map]`/`change` sites (L25) + 4 `specializeY` + `LevelThree:76, 82, 89, 336` `unfold varX varY` |
| `coxPhiAtJ`/`coxPhiFunction` (Construction:59/63) | `_monic`, `_natDegree`, `_eq_rightCosetProduct`, `_sl2_smul`, `coxPhiFunction_map_eval/_coeff_apply/_coeff_slashInvariant/_coeff_mdifferentiable/_coeff_widthM…` | `coxPhiAtJ_eval_eq_zero_iff : (coxPhiAtJ m τ).eval u = 0 ↔ ∃ σ, u = j (σ.act τ)`; note `coxPhiAtJ = Lagrange.nodal univ _` (`LinearAlgebra/Lagrange.lean:543`), `_monic`/`_natDegree` = `nodal_monic`/`natDegree_nodal` (:568/:554) | `rw [coxPhiAtJ]` at `Construction:365`, `Classification:331`, `SingularModuli:214`, `Interpolation:328`; `simp [coxPhiAtJ]` at `Construction:161, 168, 174, 188` |
| `modularPolynomialC` (Construction:343) | `_monic`, `_specializeY`, `_rightCosetProduct`, `_eval_levelJ_j`, `_natDegree`, `_coeff_polynomialIn` (IntegralDescent:265), `_irreducibleInX`, `_diagonal_series`, `_diagonal_leadingCoeff_pow` | `_eval_act_j` (L26), `_swap` (L25), `_natDegree_prime : = p + 1`, `_coeff_natDegree = 1` | `LevelThree:733–738` |
| `modularPolynomial` (IntegralDescent:287) | `_map_complex`, `_monic`, swap (`theorem_11_18_iii`), `_three` | `_natDegree`, `_degree`, `_map_complex_swap` (L25), `_coeff_polynomialIn` ℤ-form, `modularPolynomial_one : = X - C X` (asserted in `Arithmetic` docstring, never proved) | `Arithmetic:128–131, 193–198, 341–344` |
| `levelJ` (LevelJ:25) | `levelJ_mdifferentiable`, `levelJ_cuspData`, `@[simp] coe_levelJModularFunction`, `j_act_sigmaZero` | `@[simp] levelJ_apply : levelJ N τ = j ⟨N * τ, _⟩` (via `posRealAction`), `levelJ_one : levelJ 1 = j`, `levelJ_slash`, `levelJ_eq_j_at_fixedPoint` (Arithmetic:258–294 private block) | `Arithmetic:284` `unfold levelJ jN`, `Basic:725–729`, `LevelJ:270` |
| `CyclicSublattice.{map,ofLatticeEq,scale,dual,toPeriodPair,j}` (CyclicSublattice:142/156/190/506/100/122) | `map_carrier`, `ofLatticeEq_carrier`, `scale_carrier` (simp), `toPeriodPair_lattice`, `ofLatticeEq/scale/dual_toPeriodPair_lattice`, `j_ofLatticeEq`, `j_scale`, `dual_sub_j`, `dual_base_j` (rfl, misnamed) | `map_id`, `map_map`, `ofLatticeEq_rfl`, `scale_one`, `scale_mul`, `dual_dual`, `toPeriodPair_ω₁/ω₂` (publish `hnfPeriod_eq` :62), `j_map` general, `dual_j : S.dual.j = L.j` (rename of `dual_sub_j`) | `CyclicSublattice:216, 529` `change …toPeriodPair.j` |
| `toCoxMatrix` (Classification:28) | `@[simp] toCoxMatrix_inclusionMatrix`, round trips `:146, :155` (simp) | `toCoxMatrix_a/_b/_d` (free from L10) | `Classification:74` |
| `hermiteNormalForm` (HNF:403, CyclicSublattice:55) | `@[simp] repr_apply` (HNF:205); private dup `hermite_repr_apply` (CyclicSublattice:294) | `matrix_eq_fin_two`, `det_eq`, `det_pos` (L4/L5), `hnf_det_eq : S.hermiteNormalForm.matrix.det = m` | 45 field-access sites in CyclicSublattice/Classification |
| `rankTwoContent` (HNF:44) | `_dvd_mul_right`; private `_dvd_mul_left`, `_dvd_entry`, `dvd_rankTwoContent` | `_fin_two_of` (rfl), `_upperTriangular`, `_transpose`, `_sl_mul`, `_mul_sl`, `_eq_finset_gcd` (L6/L2) | 11 (L6) |
| `jLaurentSeriesMod` (Kronecker:300) | `_coeff` (rfl, NOT simp), `_order`, `_leadingCoeff`, `jIntegralLaurentSeriesWidth_map_zmod` | `@[simp]` on `_coeff`; `_coeff_mul`, `_coeff_of_not_dvd` (or `embDomain_coeff`/`_notin_range` under L20/L21) | `Kronecker:325–327, 332, 352, 430, 449` |
| `cyclotomicTransformedJSeries` (Kronecker:572) | `_coeff` (rfl, not simp), `_map_complex`, `_map_mod` | `@[simp]`, generic `_map` (L21) | `Kronecker:613, 632` |
| `evalJ` (UHPFF:55) | `@[simp] evalJ_apply`, `evalJ_injective` | `evalJ_C`, `evalJ_X : evalJ X = jElement`, `evaluation_comp_evalJ` (L29); with `Subalgebra` (§3) `evalJ = Polynomial.aeval jElement` and `evalJ_apply = aeval_fn_apply` | `UHPFF:65–66`, `MFF:39` |
| `ratFuncEvalJ` (UHPFF:95) | `@[simp] ratFuncEvalJ_algebraMap`, `@[simp] algebraMap_ratFunc`; `_injective` unused | `ratFuncEvalJ_C`, `ratFuncEvalJ_X`, `IsScalarTower` (§3) | `MFF:115–118` |
| `levelJElement`/`evalJLevelHol`/`evalJLevel`/`levelJFieldElement` (MFF:28–52) | `@[simp] evalJLevelHol_apply`, `@[simp] toMeromorphicField_levelJModularFunction` | `coe_levelJElement` (rfl), `levelJElement_one = jElement`, `evalJLevel_eq_aeval_map` (L30); three names for `j_N` (`levelJFieldElement N`, `(levelJModularFunction N).toMeromorphicField`, `rightCosetRoot N (baseRightCoset N)`) — only two related; `Arithmetic:57–63` re-derives the third | `Arithmetic:58–63`, `MFF:137–141` |
| `laurentSeriesMapRingHom` (LPE:22) | `@[simp] _coeff` | `@[simp] _apply : = F.map f` (L24) | `Kronecker:503, 521` (`exact` by defeq), `LevelThree:650–654` |

Misplaced / dead `@[simp]`:
- `LevelThree.lean:311` private `bivariateLaurentEval_intCastThree` — only ever used explicitly in `simpa only [...]` at `:345`; drop the attribute or make it a public `BivariatePolynomial.map_intCast`-style lemma.
- `CyclicSublattice.lean:251` `carrierEquiv_apply_coe`, `:268` `transportedBasis_apply_coe` — private, simp, never used anywhere; `:149` `map_carrier` simp, unused project-wide.
- `Basic.lean:236` `coe_slStar`, `:605` `coxMatrixEquivRightCosets_coxRepresentative` — `@[simp]` on private lemmas consumed only by explicit `simpa`/`rw`.
- `Cardinality.lean:208` `@[simp]` `rfl` on a private def.
- Siblings inconsistently marked: `jIntegralLaurentSeries_coeff` (Kronecker:171), `jIntegralLaurentSeriesWidth_coeff` (:197), `jUnitLaurentSeriesMod_coeff` (:247) are simp; `jLaurentSeriesMod_coeff` (:313), `cyclotomicTransformedJSeries_coeff` (:589), `transformedJSeries_coeff` (LaurentExpansion:66) are not.

---

## 3. Missing instances / structure

1. **`CuspData` → structure** (`CuspData.lean:30`, anonymous 3-conjunction). 27 `.1/.2.1/.2.2` projection sites in `Cox/` (`DiagonalLaurent:30, 161, 179`, `IntegralDescent:33, 47`, `AnalyticSupport:30`, `Interpolation:220`, `CuspData:64, 106–111, 146`, `ModularFunction:49, 85–91, 209, 249, 349`, `Basic:621`). Fields: `meromorphicOnH`, `gamma0_invariant`, `cusp_meromorphicAt`; keep `LevelOneCuspData` as `abbrev`. Plus closure API `CuspData.add/sub/neg/const/pow/smul` (only `.mul`, `.polynomialIn` exist) and `CuspData.apply_smul` (L41). Analytic-agent file; algebraic consumers.
2. **`@[ext] CoxMatrix.ext`** — VERIFIED (L8).
3. **`Fintype (CyclicSublattice L m)`** + `Nat.card_cyclicSublattice : Nat.card (CyclicSublattice L m) = Fintype.card (CoxMatrix m)` via `Fintype.ofEquiv _ (cyclicSublatticeEquivCoxMatrixOfPeriodPair L m).symm` (`Classification.lean:169`); never stated.
4. **`Subalgebra ℂ` for `holomorphicFunctions`** (`ModularFunctions/FieldAction.lean:26`, currently `Subring (ℍ → ℂ)`; `Algebra ℂ HolomorphicFunction` fails to synthesize per Batch D scratch). Then `constant` (`UHPFF.lean:36–41`) = `algebraMap`, `evalJ` (`:55`) = `Polynomial.aeval jElement`, `evalJ_apply` (`:62–73`, 12 lines) = `Polynomial.aeval_fn_apply`-style one-liner, `evalJLevelHol` = `aevalAeval`. Enables L29/L30.
5. **`IsScalarTower ℂ (RatFunc ℂ) FunctionField`**, **`IsScalarTower ℂ HolomorphicFunction FunctionField`**, and `algebraMap_ratFunc_C : algebraMap (RatFunc ℂ) FunctionField (RatFunc.C c) = algebraMap ℂ FunctionField c` — none exist (grep `IsScalarTower` in UHPFF/MFF: 0); three `Algebra _ FunctionField` structures (`FieldAction:64`, `UHPFF:104`, `MeromorphicField`) with no compatibility lemma.
6. **`CharP (HahnSeries Γ R) p` instance** — VERIFIED generic (`charP_of_injective_ringHom HahnSeries.C_injective`); replaces `letI` at `KF.lean:195–197`; mathlib has none (grep `CharP` in `RingTheory/HahnSeries`: none) → upstream.
7. **`MulAction (ZMod m)ˣ (CoxMatrix m)`** for `reindex` (`LaurentExpansion.lean:311` takes `(k : ℕ) (hk : k.Coprime m)`; `FormalCoxProduct.lean:150–153` already builds `u : (ZMod m)ˣ` and extracts `r := u.val.val` with `ZMod.val_coe_unit_coprime` (`Data/ZMod/Basic.lean:799`)). Gives `reindex_one`, `reindex_mul` (absent) and makes `formalCoxPolynomial_pow_eq` (`FormalCoxProduct:133–141`) an orbit statement.
8. **`DecidableEq (Gamma0RightCosets m)`** (decidable via `Gamma0_mem` ↔ `ZMod` cast) — would remove the three tactic-mode `by classical; exact ∑/∏ …` defs at `Interpolation.lean:32–38, 96–103, 404–407` and 15 `classical` calls in Interpolation, 9 in Construction.
9. **Term-mode vs tactic-mode defs** (10): `Classification.lean:28` (`toCoxMatrix`: `by let … exact {…}`), `:117` (`inclusionHermiteNormalForm`), `:133` (`toCyclicSublatticeOfPeriodPair`), `CyclicSublattice.lean:142` (`map`), `LaurentExpansion.lean:311` (`reindex`), `Cardinality.lean:54, 66`, `Interpolation.lean:32, 96, 404`. Each blocks `rfl`-lemmas (`toCoxMatrix_a`, `reindex_a`, …). Action: structure literals with `by` only inside proof fields.
10. **`Matrix.rankTwoContent` as `Finset.gcd`** (L6) would give `GCDMonoid`-style lemmas for free.

---

## 4. API completeness gaps per definition

- `CyclicSublattice` (CyclicSublattice.lean:24): has `ext`, `carrier_finrank`, `hermiteNormalForm`, `toPeriodPair(_lattice)`, `j`, `map(_carrier)`, `ofLatticeEq(_carrier, _carrier_map_subtype, _toPeriodPair_lattice)`, `scale(_carrier, _carrier_map_subtype, _toPeriodPair_lattice)`, `j_ofLatticeEq`, `j_scale`, `dual(_carrier_map_subtype, _toPeriodPair_lattice, _sub_j)`, `dual_base_j`. Missing: `map_id`, `map_map`, `ofLatticeEq_rfl`, `scale_one`, `scale_mul`/`scale_scale`, `dual_dual` (`= (S.scale (PNat.complexUnit m)).ofLatticeEq _`), `toPeriodPair_ω₁/ω₂`, `hnf_det_eq`, `Fintype`, `card`; `dualMatrix` (`:353`) is `Matrix.adjugate` (`adjugate_fin_two_of`, `Adjugate.lean:380`; with `adjugate_mul`/`det_adjugate` the 110-line block `:356–468` collapses); `carrierEquiv` (`:222–249`, 28 lines) = `(Submodule.equivSubtypeMap L.lattice S.carrier).trans (LinearEquiv.ofEq _ _ S.toPeriodPair_lattice.symm)` (HNF-batch scratch-verified); `hermite_repr_apply` (`:294`) dup of HNF `repr_apply`; `:24–147` are ℂ-free (any ℤ-module).
- `BivariatePolynomial.map` (Construction:48): has `map_swap`, `diagonal_map`. Missing: `map_neg/_sub/_add/_mul/_one/_pow`, `map_map`, `map_id`, `map_monic`, `natDegree_map`, `map_intCast`, `map_C`, `map_X` (L25).
- `BivariatePolynomial.eval` (Construction:40): has `specializeY_eval`, `eval_swap`, `diagonal_eval`. Missing all `eval_add/…`; and the two-conventions issue (§6).
- `modularPolynomial` / `modularPolynomialC`: see §2 rows; `monic`/`natDegree` exist for ℂ, `monic` for ℤ; missing `natDegree`/`degree`/`coeff` family for ℤ, `_swap` for ℂ, `_eval_act_j`, `modularPolynomial_one`.
- `formalCoxPolynomial` (FormalCoxProduct:24): has `_coeff_isInteger` (ℂ). Missing `_monic`, `_natDegree`, public `_map`, generic `_coeff_eq_int`, `_eval_transformedJSeries` (L38/L26).
- `PrimitiveQuadraticEquation` (SingularModuli:25): has `fixingMatrix(_det, _content_eq_one)`, `exists_positive_nonsquare_det`, `exists_nonsquare_coxMatrix_j_eq`. Missing: `fixingMatrix_smul_eq τ`, `discriminant` as `discrim`, `IsImaginaryQuadratic` iff/`smul` (L35), `IsSingularModulus` closure under `Gal`.
- `transformedJSeries`: has `_coeff`, `_order`, `_leadingCoeff`, `laurentqExpansion_coxAction`, `_pow_eq_reindex` (private). Missing `_map` public, `_sigmaZero`, `_injective` public (`conjugate_injective`/`transformed_injective` `UHPFF:203–219` private), phase generalisation (L21).
- `rightCosetTranslate/rightCosetEval/rightCosetMul/baseRightCoset` (Basic:615–697): generic `Subgroup` right-coset API stated for `Γ₀(m)`; missing `rightCosetMul_one`, `rightCosetMul_mul`, `rightCosetEval_baseRightCoset : rightCosetEval m (baseRightCoset m) = levelJ m` (hand-derived at `Interpolation:414–415`, `Arithmetic:59–63`).
- `HermiteNormalForm` (HNF:189): has `repr_apply`, `range_toLin_matrix_eq`, `matrix_eq`, `bN_eq` (unused), `index_eq_natAbs_det`, cyclicity iff. Missing `ext`, `matrix_det_pos`, `det_eq`, `matrix_eq_fin_two`; `Submodule.hermiteNormalForm` uniqueness simp lemmas.

---

## 5. Long-proof collapse map (every proof ≥ 30 lines in scope, awk-measured decl-to-decl)

| Proof (file:line, lines) | Collapsing helper(s) | Expected residual |
|---|---|---|
| `HermiteNormalForm.lean:123` `exists_hnf_transform` (49) | build `B` from `IsCoprime.exists_SL2_col` (used at LevelJ:186) on `(cg, dg)`; L17 `mul_fin_two` for `hnf_transform_mul_aux` | ≈ 30 |
| `HermiteNormalForm.lean:241` `matrix_eq` (39) | L3 (`eq_of_mul_isUnit_det` + `Basis.toMatrix_mul_toMatrix_flip`) | 5 |
| `HermiteNormalForm.lean:303` `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` (48) | `rankTwoContent_eq_of_unimodular_equiv` (from L2 `_sl_mul/_mul_sl`) for `:327–340`; `rankTwoContent_diagonal` for `hcontentD` | ≈ 28 |
| `HermiteNormalForm.lean:369` `exists_hermiteNormalForm` (33) | L34 (`toLin_injective ↔ det ≠ 0`) + `LinearMap.toMatrix_comp` bookkeeping lemma | ≈ 20 |
| `Classification.lean:28` `toCoxMatrix` (30) | L10 `ofColumnHNF` + L5 `hnf_det_eq` | 4 |
| `CoxMatrices/Basic.lean:247` `columnHNF_eq_of_mul` (40) | mathematical core (keep, move to HNF); extract `diag_eq_of_mutual_dvd` (used at `:273–274`, `:276–277`) | ≈ 30, and it replaces `matrix_eq` |
| `CoxMatrices/Basic.lean:509` `coxMatrix_smith_normalization` (52) | `SL2_inv_expl`-entry lemma for the two 7-line blocks `:526–541`; L17 for `:517–521`, `:557–560` | ≈ 35 |
| `CoxMatrices/Basic.lean:719` `levelJ_smul_eq_j_act_of_normalization` (43) + `:699` `complex_mobius_scale_eq_affine` (19) | L12 `act_eq_sl2_smul_of_mul` (+ `levelJ_apply`) | ≈ 8 |
| `CoxMatrices/LaurentExpansion.lean:143` `poleOrder_coxAction_aux` (42) | `analyticOrderAt_const_mul_pow` (`:151–160`) + `meromorphicOrderAt_comp_const_mul_pow` corollary (analytic agent) | ≈ 15 |
| `CoxMatrices/LaurentExpansion.lean:196` `to_qExpansion_coxAction_aux` (46) | L21 `substMonomial` + analytic bridge `laurentqExpansion_comp_of_qParam_eq` | deleted |
| `CoxMatrices/LaurentExpansion.lean:258` `laurentqExpansion_coxAction_coeff_aux` (45) | same; else `coeff_substMonomial` + `jIntCoeff_spec` | deleted / ≈ 12 |
| `IntegralDescent.lean:195` `coxPhiFunction_coeff_laurentqExpansion_widthM` (38) | `laurentqExpansionRingHom h : cuspMeromorphicSubring h →+* LaurentSeries ℂ` (analytic) then `Polynomial.map_prod` naturality + `laurentqExpansion_coxAction` | ≈ 8 |
| `Interpolation.lean:351` `exists_commonDenominator_polynomialEval_of_natDegree_lt` (45) | generic over any field `K` and index type (no Cox content); `Finset.mul_prod_erase` already used | ≈ 35, moved out of Cox |
| `DiagonalLaurent.lean:89` `cox_diagonal_factor_leadingCoeff` (48) | `HahnSeries.leadingCoeff_sub_of_order_lt` (order form of `leadingCoeff_sub`; kills `:105–112` + two `norm_cast; omega`) | ≈ 25 |
| `Kronecker.lean:705` `cyclotomicDescent_polynomialLaurentSeries` (31) | `Polynomial.ext_iff` ∘ `HahnSeries.ext_iff` coefficient-transport lemma; L24 `_apply` | ≈ 20 |
| `Kronecker.lean:737` `specializeJMod_modularPolynomial_eq_formal` (33) | the two `change` blocks vanish once `phaseEvalComplex`/`phaseEvalMod` have `rfl` simp lemmas | ≈ 20 |
| `KroneckerFrobenius.lean:104` `transformedJSeries_one_sigmaZero_eq_expand` (36) | L19 + L20 (`transformedJSeries_sigmaZero` + `jLaurentSeriesWidth_eq_single_mul_expand`) | 3 |
| `LevelThree.lean:518` `explicitCandidateLaurentEvalThree_observed_coefficients` (40) + `:349–502` (154) | L39 | 2 + 1 |
| `Arithmetic.lean:53` `aeval_base_eq_zero_of_forall_eval_eq_zero` (41) | L29 (`HolomorphicFunction.ext`, `evaluation_comp_evalJ`, `algebraMap_ratFunc_comp_algebraMap`) + `Polynomial.aeval_map_algebraMap` | ≈ 12 |
| `Arithmetic.lean:95` `modularPolynomial_dvd_swap` (38) | L25 `modularPolynomial_map_complex_swap` kills `:124–132`; `minpoly.eq_of_irreducible_of_monic` fine | ≈ 22 |
| `Arithmetic.lean:297` `theorem_11_18_iv_degree` (40) | split: `modularPolynomialDiagonal_ne_zero`, `_natDegree_pos` (fixed-point root, no nonsquare hyp), `_coeff_one_even` (`diagonal_coeff_one` + symmetry) | 3 × ≤ 12 |
| `SingularModuli.lean:155` `coxMatrix_act_eq_smul_aux` (33) | L12 | 4 |
| `ModularFunctionField.lean:56` `toMeromorphicField_eq_div_of` (32) | `MeromorphicField.eq_div_of_forall` generic (analytic agent; uses only `toFun_ofMeromorphic`) | ≈ 10 |
| (July-listed, now < 30) `Basic.lean:387` `exists_coxMatrix_reduction` 11, `UHPFF.lean:179` `cox_b_eq` 23 | done / fine | — |

---

## 6. Naming / namespace hygiene

- **Theorem-number names** (10): `theorem_11_18_i` (`Arithmetic.lean:22`, 0-line alias, no consumer), `theorem_11_18_ii` (`:28`, alias, no consumer), `theorem_11_18_iii` (`:178`; consumers `:323`, `:342`, LevelThree's `hsymm`), `theorem_11_18_iv_leadingCoeff` (`:230`; consumer `SingularModuli:222`), `theorem_11_18_iv_degree` (`:297`), `theorem_11_18_v` (`KF.lean:221`), `theorem_11_23` (`Classification.lean:345`; consumer `Arithmetic:42–43`), `theorem_11_9_ii_pointwise` (`Interpolation.lean:488`), `theorem_11_9_ii` (`MFF.lean:176`), `theorem_11_9_i` (`ModularFunction.lean:431`). Proposed: delete i/ii; `modularPolynomial_swap` (iii), `modularPolynomialDiagonal_leadingCoeff_eq_one_or_neg_one` (iv-lc), `one_lt_natDegree_modularPolynomialDiagonal` (iv-deg), `modularPolynomial_map_zmod_prime` / `kronecker_congruence` (v), `modularPolynomial_eval_eq_zero_iff_exists_cyclicSublattice` (11.23), `rationalInTwo_j_levelJ` (11.9ii pointwise), `gamma0ModularFunctionField_eq_jLevelFunctionField` (11.9ii), `rationalIn_j` (11.9i). Keep the Cox numbers in docstrings.
- **`levelJ` vs `jN`**: `levelJ N := @jN N ⟨_⟩` (`LevelJ.lean:25`); 80 `levelJ` sites in `Cox/` vs 17 `jN` (`jLevelN` 15, `Arithmetic:284` `unfold levelJ jN`, `LevelJ:26`). Action: one name (make `jN` take `ℕ+` or make `levelJ` the definition and `jN` the alias), `@[simp] levelJ_apply`, replace private `natScaleUpperHalfPlane` (`LevelJ:29`) by mathlib `posRealAction` (`UpperHalfPlane/Basic.lean:197`).
- **`varX`/`varY` inverted vs mathlib** (`Construction.lean:33/36`; 25 uses: LevelThree 9, KF 8, Kronecker 6, Construction 2): Cox's outer/root `X` is mathlib's `Y` (`Polynomial.X (R := R[X])`, `Bivariate.lean:26`), Cox's `Y` is `C X`. Action: drop `varX/varY`, write `(Y : R[X][Y])` and `C X` under `open scoped Polynomial.Bivariate` (so `Bivariate.swap_X/swap_Y`, `evalEval_X`, `aevalAeval_X/_Y` apply), document the dictionary once in `Construction.lean`'s module docstring.
- **`BivariatePolynomial.eval Φ x y := Φ.evalEval y x`** (argument order swapped vs mathlib `evalEval x y`, `Bivariate.lean:44`): ≈ 20 `BivariatePolynomial.eval` sites (Construction 7, Arithmetic 5, ModularFunction 5, Classification 3, DiagonalLaurent 2, IntegralDescent 2, SingularModuli 1, UHPFF 1) vs ≈ 21 raw `evalEval` sites (Interpolation 11, MFF 4, CuspData 3, Construction 3); sole bridge private `modularPolynomialC_derivative_evalEval` (`Interpolation.lean:397`). Action: delete `BivariatePolynomial.eval`, state everything as `Φ.evalEval (j τ) (levelJ m τ)` (mathlib order), or make it an `abbrev` with `@[simp] eval_eq_evalEval`.
- **`_aux` public names**: none in scope (all `_aux` are private) — clean.
- **Private lemmas that are general** (should be public, often in another file): `LevelThree.lean:559` `int_dvd_iff_dvd_add_natAbs` (≡ `KF:98`, ≡ `LevelThree:569/573`; all subsumed by L19), `:638` `bivariateLaurentEval_map` (generic `[CommRing R] [CommRing S]` → LPE, next to `bivariateSpecializeLaurent_map_apply`), `:689` `modularPolynomialC_three_laurent_root` (holds ∀ m σ → L26), `:122` `jIntCoeff_eq_qjCoeffInt_three` (not level-specific), `:147–198` `shiftedPowerSeries_pow/_mul`, `clearTwoShiftedPowerSeries`, `C_mul_single_one` (any `CommSemiring`; = `HahnSeries.single_pow`/`single_mul_single`/`C_mul_eq_smul`); `FormalCoxProduct.lean:29` `transformedJSeries_map`, `:163` `formalCoxPolynomial_coeff_eq_int` (generic `K`), `:51` `integralLaurentSeries`; `UHPFF.lean:214` `conjugate_injective` (headline distinctness result of Cox §11B → `LaurentExpansion.lean`), `:221` `rightCosetEval_mdifferentiable` (≡ `Construction:215–218` `hcoset` → `CoxMatrices/Basic.lean`), `:140` `transformed_leading` (≡ `DiagonalLaurent:56`); `Basic.lean:225, 247, 343` (L2/L3), `:154` `matrixStar`, `:699` `complex_mobius_scale_eq_affine`; `HNF.lean:76`, `:232`; `CyclicSublattice.lean:62` `hnfPeriod_eq`, `:300` `originalMatrix_eq`, `:306` `d_mul_a_eq_m`, `:470` `dual_content_eq_one`, `:485` `indexUnit`; `Interpolation.lean:211` `rightCosetTranslate_cuspMeromorphicAt_aux` (⊇ `AnalyticSupport:23`), `:301` `eval_interpolation_sum_at` (PR candidate, `Lagrange` namespace), `:351`; `Irreducibility.lean` private `modularPolynomialRatFunc_irreducible` re-exported as `modularPolynomialC_irreducibleInX` (`:134`) → merge; `Arithmetic.lean:164` `eq_or_eq_neg_of_associated_int_bivariate` (general `Polynomial.associated_iff_eq_or_eq_neg`; mathlib has only scalar `Int.associated_iff`, `Algebra/GCDMonoid/Nat.lean:168`), `:239` `diagonal_coeff_one`, `:258–294` fixed-point block (→ `levelJ_eq_j_at_I_div_sqrt`); `Kronecker.lean:282` `powerSeries_pow_prime_eq_expand` (→ `PowerSeries.pow_prime_pow_eq_expand`, typechecked; mathlib has only `MvPowerSeries.map_frobenius_expand`/`map_iterateFrobenius_expand`, `MvPowerSeries/Expand.lean:232/247`, and `Polynomial.map_frobenius_expand`, `Algebra/Polynomial/Expand.lean:262`).
- **Namespaces**: generic material inside `Cox`: `laurentSeriesMapRingHom`, `bivariateSpecializeLaurent`, `polynomial_eval₂_laurentSeries_*`, `laurentSeries_pow_*` (LPE), `symmetric_bidegree_three_eq_zero_of_laurent_coeff` + triangular kernel (SCL:285–342), `BivariatePolynomial.*` lemmas (should be `Polynomial.Bivariate.*` or upstreamed: `coeff_coeff_swap`, `map_swap`, `diagonal_swap`, `specializeY_ext` are not in `Bivariate.lean`); `Construction.lean:88–156` declares `theorem BivariatePolynomial.eval_swap` etc. outside the `namespace BivariatePolynomial` block. `Matrix.*`/`Module.Basis.HermiteNormalForm`/`Submodule.*` in HNF are correctly placed. `link.lean` root-level lemmas: out of scope (Batch C).
- **File hygiene**: `DiagonalLaurent.lean:1–10` duplicated copyright header; `LevelThree.lean:7` unused `import Mathlib.RingTheory.PowerSeries.Trunc`; `Kronecker.lean:9` redundant import; `LaurentExpansion.lean:6` `Mathlib.NumberTheory.Cyclotomic.Basic` unused (only `Complex.isPrimitiveRoot_exp`); `Kronecker.lean:172–181` `jIntegralLaurentSeries_coeff`/`_map_complex` unused project-wide; `KF.lean:168` `transformedJSeries_one_sigmaZero_eq_primeLower_pow` unused; `Classification.lean:189, 288` unused; `HNF.lean:281` `bN_eq` unused; `UHPFF.lean:48, 100` unused.

---

## 7. Ranking — top 12 missing lemmas by impact (lines saved / proofs simplified)

1. L19+L20 `coeff_single_neg_mul_coe_expand` + `jLaurentSeriesWidth` (+ correct `transformedJSeries_sigmaZero`) — ≈ 340 lines across Kronecker/KF/LevelThree; corrects a false identity in the inventory.
2. L39 LevelThree single `decide +kernel` + `TriangularCoeffsVanish` — ≈ 220 lines.
3. L21 `substMonomial` (+ analytic bridge) — ≈ 60 algebraic + 180 analytic lines; unifies 2 series defs and 4 `_map` twins.
4. L28 `LevelOneCuspData.of_widthM` + `prod_X_sub_C_coeff_mem` — ≈ 130 lines (A15 pipeline ×2–3).
5. L1+L2+L3 SL₂ triangularisation public + HNF-uniqueness dedupe — ≈ 150 lines (LevelJ 99, `matrix_eq`≡`columnHNF_eq_of_mul` 40).
6. L12 `act_eq_sl2_smul_of_mul` — ≈ 80 lines (3 copies of the Möbius field_simp).
7. L18 `laurentqExpansion_polynomialIn/_pow` (analytic) — ≈ 60 lines (IntegralDescent ≡ DiagonalLaurent).
8. L24 `HahnSeries.coeffSubring` + `mapRingHom` + `_apply` — ≈ 50 lines, 2 subrings + 2 homs + defeq reliance.
9. L10 `CoxMatrix.ofColumnHNF` (+ L4/L5/L6 HNF field lemmas) — ≈ 90 lines over 3 construction copies + 7 quadruples + 5 `det_fin_two` hacks + 11 gcd idioms.
10. L22+L23 Hahn order helper + LPE siblings + `leadingCoeff_pow` — ≈ 85 lines; 3 PR candidates.
11. L25+L26 `map_complex_swap`, `modularPolynomialC_swap`, `_eval_act_j` + `map` ring-hom lemmas — ≈ 45 lines; supplies the missing named ℂ-symmetry theorem.
12. L8+L9+L7+L14+L40 `CoxMatrix.ext`, `d_dvd/div_d`, `coprime_gcd_b`, SL₂-cancel, `zeta_ne_zero` — ≈ 50 lines over 26 sites, all VERIFIED one-liners.
