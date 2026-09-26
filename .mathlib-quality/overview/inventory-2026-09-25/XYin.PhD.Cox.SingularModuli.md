# Inventory: XYin/PhD/Cox/SingularModuli.lean  (238 lines)

Report Theorem 5.9 (the integrality half of Cox Theorem 11.1): if `τ ∈ ℍ` satisfies a primitive integral
quadratic equation `Aτ² + Bτ + C = 0` with `B² − 4AC < 0`, then `j(τ)` is an algebraic integer. Method: the
integer matrix `M_n = [[n, −C],[A, n+B]]` fixes `τ`, has `det M_n = n² + Bn + AC` and content 1; choose `n`
so that `det M_n = N` is a positive nonsquare, reduce `M_n` to a Cox representative `σ ∈ C(N)` by an
`SL₂(ℤ)` factor (`exists_sl2_mul_eq_coxMatrix`), so `j(σ·τ) = j(τ)`; hence `Φ_N(j τ, j τ) = 0` and, since
`Φ_N(X,X)` has leading coefficient `±1` (Theorem 11.18(iv)), `j(τ)` is integral over `ℤ`.

## Declarations

### `structure Cox.PrimitiveQuadraticEquation`
- **Type**: `(τ : ℍ) → Type` with fields `A B C : ℤ`, `equation : (A:ℂ) τ² + B τ + C = 0`, `discriminant_neg : B² − 4AC < 0`, `primitive : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1`
- **What**: A primitive integral quadratic equation of negative discriminant satisfied by the point `τ`.
- **How**: Data structure (no constructor lemmas).
- **Hypotheses**: n/a.
- **Uses from project**: []
- **Used by**: `IsImaginaryQuadratic`, `PrimitiveQuadraticEquation.fixingMatrix`, `fixingMatrix_det`, `exists_positive_nonsquare_det_of_even_aux`, `_odd_aux`, `exists_positive_nonsquare_det`, `fixingMatrix_content_eq_one`, `coxMatrix_act_eq_smul_aux`, `exists_nonsquare_coxMatrix_j_eq`
- **Visibility**: public
- **Lines**: 24–34
- **Notes**: `primitive` is a nested `Nat.gcd` of `natAbs` (mathlib idiom would be `Int.gcd (Int.gcd A B) C = 1` or `Polynomial.IsPrimitive`). `discriminant_neg` is `discrim A B C < 0` in mathlib terms (`discrim`, Algebra/QuadraticDiscriminant.lean:48). No `ext`/`mk` simp lemmas; not needed.

### `def Cox.IsImaginaryQuadratic`
- **Type**: `(τ : ℍ) → Prop`
- **What**: `τ` admits some primitive negative-discriminant integral quadratic equation.
- **How**: `Nonempty (PrimitiveQuadraticEquation τ)`.
- **Hypotheses**: none.
- **Uses from project**: [`PrimitiveQuadraticEquation`]
- **Used by**: `IsSingularModulus`, `exists_nonsquare_modularPolynomialDiagonal_root`, `isIntegral_j_of_isImaginaryQuadratic`
- **Visibility**: public
- **Lines**: 36–39
- **Notes**: No companion lemma relating it to `minpoly ℚ (τ:ℂ)` having degree 2 / `IsAlgebraic ℚ`.

### `def Cox.IsSingularModulus`
- **Type**: `(z : ℂ) → Prop`
- **What**: `z` is a `j`-value at an imaginary-quadratic point.
- **How**: `∃ τ, IsImaginaryQuadratic τ ∧ z = j τ`.
- **Hypotheses**: none.
- **Uses from project**: [`IsImaginaryQuadratic`, `j`]
- **Used by**: `singularModulus_isIntegral`
- **Visibility**: public
- **Lines**: 41–43

### `def Cox.PrimitiveQuadraticEquation.fixingMatrix`
- **Type**: `(q : PrimitiveQuadraticEquation τ) (n : ℤ) → Matrix (Fin 2) (Fin 2) ℤ`
- **What**: `M_n = !![n, −C; A, n+B]`, the family of integer matrices fixing `τ`.
- **How**: Matrix literal.
- **Hypotheses**: none.
- **Uses from project**: [`PrimitiveQuadraticEquation`]
- **Used by**: `fixingMatrix_det`, `fixingMatrix_content_eq_one`, `coxMatrix_act_eq_smul_aux`, `exists_positive_nonsquare_det_of_even_aux`, `_odd_aux`, `exists_positive_nonsquare_det`, `exists_nonsquare_coxMatrix_j_eq`
- **Visibility**: public
- **Lines**: 49–51
- **Notes**: The fact "`M_n` fixes `τ`" is never stated on its own; it is buried in `coxMatrix_act_eq_smul_aux` (L180–184).

### `theorem Cox.PrimitiveQuadraticEquation.fixingMatrix_det` (`@[simp]`)
- **Type**: `(n : ℤ) → (q.fixingMatrix n).det = n ^ 2 + q.B * n + q.A * q.C`
- **What**: Determinant of `M_n`.
- **How**: `Matrix.det_fin_two_of` (LinearAlgebra/Matrix/Determinant/Basic.lean:812) + `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`fixingMatrix`]
- **Used by**: `exists_positive_nonsquare_det_of_even_aux`, `exists_positive_nonsquare_det_of_odd_aux`
- **Visibility**: public
- **Lines**: 53–57, body ≈ 2

### `lemma Cox.PrimitiveQuadraticEquation.not_isSquare_of_between_sq_aux` (private)
- **Type**: `{k : ℤ} {N : ℕ} (hk : 0 ≤ k) (hlo : k ^ 2 < (N : ℤ)) (hhi : (N : ℤ) < (k + 1) ^ 2) → ¬ IsSquare N`
- **What**: A natural number strictly between consecutive squares `k²` and `(k+1)²` (with `k ≥ 0` an integer) is not a perfect square.
- **How**: From `IsSquare.exists_sq` (alias at Algebra/Group/Even.lean:134) get `N = r²`, then `sq_lt_sq₀` (Algebra/Order/GroupWithZero/Unbundled/Basic.lean:701) gives `k < r < k+1` in `ℤ`, contradiction by `omega`.
- **Hypotheses**: `0 ≤ k`, `k² < N < (k+1)²`.
- **Uses from project**: []
- **Used by**: `exists_positive_nonsquare_det_of_even_aux`, `exists_positive_nonsquare_det_of_odd_aux`
- **Visibility**: private
- **Lines**: 59–72, body ≈ 11
- **Notes**: **Still present** (the July report's flag stands). It is the `ℤ`-indexed, `IsSquare`-phrased variant of mathlib's `Nat.not_exists_sq (hl : m * m < n) (hr : n < (m + 1) * (m + 1)) : ¬∃ t, t * t = n` (Data/Nat/Sqrt.lean:207) / `Nat.not_exists_sq'` (`^2` form, :213). Not a verbatim duplicate: the caller supplies `k : ℤ` (`k = AC − b²`) and the conclusion is `¬IsSquare N` (`IsSquare N ↔ ∃ r, N = r * r`, definitionally the negation of `Nat.not_exists_sq`'s target up to `eq_comm`). Replacement: `lift k to ℕ using hk` then `fun ⟨r, hr⟩ ↦ Nat.not_exists_sq (by exact_mod_cast hlo) (by exact_mod_cast hhi) ⟨r, hr.symm⟩` — 3 lines, so the private lemma can become a 3-line bridge or be inlined at its 2 call sites.

### `lemma Cox.PrimitiveQuadraticEquation.exists_positive_nonsquare_det_of_even_aux` (private)
- **Type**: `{b : ℤ} (hB : q.B = 2 * b) → ∃ (n : ℤ) (N : ℕ+), (q.fixingMatrix n).det = N ∧ ¬ IsSquare (N : ℕ)`
- **What**: When `B` is even, some `M_n` has positive nonsquare determinant.
- **How**: With `k := AC − b² > 0` (from `discriminant_neg` by `nlinarith`) and `n := k − b`, `det M_n = k² + k` (`fixingMatrix_det`, `ring`), which lies strictly between `k²` and `(k+1)²`, so `not_isSquare_of_between_sq_aux`; `N := (k²+k).toNat` via `Int.lt_toNat`, `Int.toNat_of_nonneg`.
- **Hypotheses**: `B = 2b`.
- **Uses from project**: [`PrimitiveQuadraticEquation`, `fixingMatrix`, `fixingMatrix_det`, `not_isSquare_of_between_sq_aux`]
- **Used by**: `exists_positive_nonsquare_det`
- **Visibility**: private
- **Lines**: 74–101, body ≈ 25

### `lemma Cox.PrimitiveQuadraticEquation.exists_positive_nonsquare_det_of_odd_aux` (private)
- **Type**: `{b : ℤ} (hB : q.B = 2 * b + 1) → ∃ (n : ℤ) (N : ℕ+), (q.fixingMatrix n).det = N ∧ ¬ IsSquare (N : ℕ)`
- **What**: When `B` is odd, some `M_n` has positive nonsquare determinant.
- **How**: Same as the even case with `k := AC − b(b+1) > 0`, `n := k − b`, `det M_n = k² + 2k ∈ (k², (k+1)²)`.
- **Hypotheses**: `B = 2b + 1`.
- **Uses from project**: [`PrimitiveQuadraticEquation`, `fixingMatrix`, `fixingMatrix_det`, `not_isSquare_of_between_sq_aux`]
- **Used by**: `exists_positive_nonsquare_det`
- **Visibility**: private
- **Lines**: 103–130, body ≈ 25
- **Notes**: Line-for-line copy of the even case with different `k`, `D`.

### `theorem Cox.PrimitiveQuadraticEquation.exists_positive_nonsquare_det`
- **Type**: `∃ (n : ℤ) (N : ℕ+), (q.fixingMatrix n).det = N ∧ ¬ IsSquare (N : ℕ)`
- **What**: Some `M_n` has positive nonsquare determinant.
- **How**: `Int.even_or_odd'` (Algebra/Ring/Int/Parity.lean:42) on `B`, dispatch to the two aux lemmas.
- **Hypotheses**: none (beyond `q`).
- **Uses from project**: [`fixingMatrix`, `exists_positive_nonsquare_det_of_even_aux`, `exists_positive_nonsquare_det_of_odd_aux`]
- **Used by**: `exists_nonsquare_coxMatrix_j_eq`
- **Visibility**: public
- **Lines**: 132–138, body ≈ 3

### `theorem Cox.PrimitiveQuadraticEquation.fixingMatrix_content_eq_one`
- **Type**: `(n : ℤ) → Matrix.rankTwoContent (q.fixingMatrix n) = 1`
- **What**: Every `M_n` is primitive (gcd of entries `1`).
- **How**: `gcd(n, n+B, A, C) = gcd(n, gcd(A, B, C)) = gcd(n, 1) = 1` using `Int.gcd_add_self_right` (core Init/Data/Int/Gcd.lean:251), `ac_rfl` on `Nat.gcd`, and `q.primitive`.
- **Hypotheses**: none.
- **Uses from project**: [`Matrix.rankTwoContent`, `fixingMatrix`, `PrimitiveQuadraticEquation.primitive`]
- **Used by**: `exists_nonsquare_coxMatrix_j_eq`
- **Visibility**: public
- **Lines**: 140–153, body ≈ 11

### `lemma Cox.PrimitiveQuadraticEquation.coxMatrix_act_eq_smul_aux` (private)
- **Type**: `{n : ℤ} {N : ℕ+} {γ : SL(2, ℤ)} {σ : CoxMatrix N} (hmat : γ.1 * q.fixingMatrix n = σ.mobiusMatrix) → σ.act τ = γ • τ`
- **What**: If `γ M_n = σ` (as matrices) then the Cox action of `σ` on `τ` equals the modular action of `γ`, because `M_n` fixes `τ`.
- **How**: Extract the four entry equations from `hmat` (`Matrix.mul_apply`, `Fin.sum_univ_two`), cast to `ℂ`; unfold `CoxMatrix.coe_act`, `UpperHalfPlane.coe_specialLinearGroup_apply`; nonvanishing denominators from `UpperHalfPlane.denom_ne_zero` and `σ.d_pos`; `field_simp` then a `linear_combination` whose coefficients multiply `q.equation` (the fixed-point identity) and the `(1,0)` entry equation.
- **Hypotheses**: `γ · M_n = mobiusMatrix σ`.
- **Uses from project**: [`fixingMatrix`, `PrimitiveQuadraticEquation.equation`, `CoxMatrix`, `CoxMatrix.mobiusMatrix`, `CoxMatrix.act`, `CoxMatrix.coe_act`, `CoxMatrix.d_pos`]
- **Used by**: `exists_nonsquare_coxMatrix_j_eq`
- **Visibility**: private
- **Lines**: 155–186, body ≈ 29
- **Notes**: Conflates two facts: (a) `M_n` fixes `τ` as a Möbius transformation, (b) the Möbius action is multiplicative (`(γM)·τ = γ·(M·τ)`). Neither is stated separately; (b) is generic and (a) is the only place `q.equation` is used.

### `theorem Cox.PrimitiveQuadraticEquation.exists_nonsquare_coxMatrix_j_eq`
- **Type**: `∃ N : ℕ+, ¬ IsSquare (N : ℕ) ∧ ∃ σ : CoxMatrix N, j (σ.act τ) = j τ`
- **What**: At some positive nonsquare level `N`, a Cox representative moves `τ` to a point with the same `j`-value.
- **How**: `exists_positive_nonsquare_det`, `exists_sl2_mul_eq_coxMatrix` (CoxMatrices/Basic.lean:793, Report Lemma 5.8) with `fixingMatrix_content_eq_one`, then `coxMatrix_act_eq_smul_aux` and `j_modularGroup_smul`.
- **Hypotheses**: none (uses `include q`).
- **Uses from project**: [`CoxMatrix`, `CoxMatrix.act`, `j`, `exists_positive_nonsquare_det`, `exists_sl2_mul_eq_coxMatrix`, `fixingMatrix`, `fixingMatrix_content_eq_one`, `coxMatrix_act_eq_smul_aux`, `j_modularGroup_smul`]
- **Used by**: `exists_nonsquare_modularPolynomialDiagonal_root` (as `q.exists_nonsquare_coxMatrix_j_eq`)
- **Visibility**: public
- **Lines**: 187–196, body ≈ 7

### `theorem Cox.exists_nonsquare_modularPolynomialDiagonal_root`
- **Type**: `{τ : ℍ} (hτ : IsImaginaryQuadratic τ) → ∃ N : ℕ+, ¬ IsSquare (N : ℕ) ∧ (modularPolynomialDiagonal N).eval₂ (Int.castRingHom ℂ) (j τ) = 0`
- **What**: `j(τ)` is a root of the integral diagonal polynomial `Φ_N(X,X)` for some nonsquare `N`.
- **How**: Take `σ` from `exists_nonsquare_coxMatrix_j_eq`; unfold `modularPolynomialDiagonal` with `BivariatePolynomial.diagonal_eval₂` and `Polynomial.eval₂_eval₂RingHom_apply` (Algebra/Polynomial/Bivariate.lean:194); pass to `Φ_Nᶜ` via `modularPolynomial_map_complex`, specialize `Y = j τ` (`specializeY_eval`, `modularPolynomialC_specializeY`, `coxPhiAtJ`), and kill the product with the factor `X − j(σ·τ)` (`Polynomial.eval_prod`, `Finset.prod_eq_zero`).
- **Hypotheses**: `τ` imaginary quadratic.
- **Uses from project**: [`IsImaginaryQuadratic`, `PrimitiveQuadraticEquation.exists_nonsquare_coxMatrix_j_eq`, `modularPolynomialDiagonal`, `BivariatePolynomial.diagonal_eval₂`, `BivariatePolynomial.map`, `BivariatePolynomial.eval`, `modularPolynomial`, `modularPolynomial_map_complex`, `BivariatePolynomial.specializeY_eval`, `modularPolynomialC_specializeY`, `coxPhiAtJ`, `j`]
- **Used by**: `isIntegral_j_of_isImaginaryQuadratic`
- **Visibility**: public
- **Lines**: 200–216, body ≈ 11

### `theorem Cox.isIntegral_j_of_isImaginaryQuadratic`
- **Type**: `{τ : ℍ} (hτ : IsImaginaryQuadratic τ) → IsIntegral ℤ (j τ)`
- **What**: Report Theorem 5.9: `j(τ)` is an algebraic integer for imaginary-quadratic `τ`.
- **How**: With `N` from the previous theorem, `theorem_11_18_iv_leadingCoeff` gives leading coefficient `1` (use `D`) or `−1` (use `−D`, `Polynomial.leadingCoeff_neg`, `Polynomial.eval₂_neg`); either is a monic integer polynomial with root `j τ`, i.e. `IsIntegral` by definition (`Polynomial.Monic.def`, `Polynomial.aeval_def`).
- **Hypotheses**: `τ` imaginary quadratic.
- **Uses from project**: [`IsImaginaryQuadratic`, `j`, `exists_nonsquare_modularPolynomialDiagonal_root`, `theorem_11_18_iv_leadingCoeff`, `modularPolynomialDiagonal`]
- **Used by**: `singularModulus_isIntegral`
- **Visibility**: public
- **Lines**: 218–230, body ≈ 10

### `theorem Cox.singularModulus_isIntegral`
- **Type**: `{z : ℂ} (hz : IsSingularModulus z) → IsIntegral ℤ z`
- **What**: Every singular modulus is an algebraic integer.
- **How**: Destructure and apply `isIntegral_j_of_isImaginaryQuadratic`.
- **Hypotheses**: `z` singular modulus.
- **Uses from project**: [`IsSingularModulus`, `isIntegral_j_of_isImaginaryQuadratic`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 232–236, body ≈ 2
- **Notes**: Terminal; not referenced by any other XYin `.lean` file.

## File Summary
- Total declarations: 15 (4 defs [1 structure, 3 defs], 11 lemmas/theorems, 0 instances, 0 other); 11 public, 4 private.
- Key API (used by 3+ others in the file): `PrimitiveQuadraticEquation` (9), `fixingMatrix` (7), `IsImaginaryQuadratic` (3).
- Unused declarations (not used by anything in this file): `singularModulus_isIntegral` (terminal; no external users either).
- Declarations with sorry: none.
- Declarations with set_option: none.
- Proofs >30 lines: none (longest: `coxMatrix_act_eq_smul_aux` ≈ 29, L155–186; the two `_aux` parity lemmas ≈ 25 each).

## Observations (evidence for the analysis phases)

### Mathlib API candidates
- `not_isSquare_of_between_sq_aux` (L59–72) ↔ `Nat.not_exists_sq` / `Nat.not_exists_sq'` (Data/Nat/Sqrt.lean:207/213). Verified present in the pinned mathlib. Modulo `lift k to ℕ` and `IsSquare` ↔ `∃ t, t*t = N`, the private lemma is a 3-line corollary; recommend replacing.
- `PrimitiveQuadraticEquation` (L25–34): no `BinaryQuadraticForm` structure exists in the pinned mathlib (only a section title at NumberTheory/LegendreSymbol/Basic.lean:208); `Mathlib/NumberTheory/Zsqrtd/` (`Zsqrtd`, Basic.lean:33) models `ℤ[√d]` as a ring, not quadratic equations of points of `ℍ`. Mathlib pieces the project could ride on: `discrim` (Algebra/QuadraticDiscriminant.lean:48; `discriminant_neg` is `discrim A B C < 0`), `Polynomial.IsPrimitive` (RingTheory/Polynomial/Content.lean:45; the `primitive` field is `IsPrimitive (C A * X^2 + C B * X + C C)`), `IsIntegral`/`minpoly` (used for the conclusion). A mathlib-native reformulation `IsImaginaryQuadratic τ ↔ (minpoly ℚ (τ:ℂ)).natDegree = 2` is a missing companion lemma; the data-carrying structure is nevertheless the right choice here since `fixingMatrix` needs `(A,B,C)`.
- `fixingMatrix_content_eq_one` relies on the project's `Matrix.rankTwoContent` (HermiteNormalForm.lean:44); no mathlib 2×2 content function found (searched `Matrix.*content`, `Finset.gcd` over matrix entries).
- `isIntegral_j_of_isImaginaryQuadratic` (L219–230): mathlib has no "root of an integer polynomial with unit leading coefficient is integral" lemma; `isIntegral_leadingCoeff_smul` (RingTheory/Algebraic/Integral.lean) gives integrality of `lc • x`, which with `lc = ±1` plus `IsIntegral.neg` is an alternative of similar length. The explicit `D`/`−D` split is fine.
- `Polynomial.eval₂_eval₂RingHom_apply` (Algebra/Polynomial/Bivariate.lean:194) and `Matrix.det_fin_two_of` are used correctly.
- Hand-rolled: the `ℂ`-level Möbius computation in `coxMatrix_act_eq_smul_aux` (L164–184) re-derives "`(γ M)·τ = γ·(M·τ)`" by hand; mathlib has the `GL(2,ℝ)⁺`-action on `ℍ` (`UpperHalfPlane` `MulAction` instances in Analysis/Complex/UpperHalfPlane/MoebiusAction.lean) but the project's `CoxMatrix.act` is not connected to it, so no drop-in exists.

### Missing API / repeated patterns
- `exists_positive_nonsquare_det_of_even_aux` / `_odd_aux` (L74–101 / L103–130): identical 25-line skeletons (`let k`, `nlinarith`, `let D`, `⟨D.toNat, _⟩`, `Int.toNat_of_nonneg`, `refine ⟨k − b, N, ?_, not_isSquare… hk.le ?_ ?_⟩`, three `nlinarith`/`ring` goals). Collapse via one lemma
  `exists_nonsquare_det_of_between (n k : ℤ) (hk : 0 ≤ k) (hlo : k^2 < det (fixingMatrix n)) (hhi : det (fixingMatrix n) < (k+1)^2) : ∃ N : ℕ+, det = N ∧ ¬IsSquare (N:ℕ)`
  and then two 4-line instantiations; or avoid the parity split altogether using `4·det M_n = (2n+B)² + (4AC − B²)` and choosing `n` with `2n + B ∈ {2k, 2k+1}`.
- Missing statement `fixingMatrix_smul_fixed : (M_n as Möbius map) τ = τ` (the actual mathematical content of `q.equation`), and a generic `CoxMatrix.act_of_sl2_mul (hmat : γ.1 * M = σ.mobiusMatrix) : σ.act τ = γ • (M · τ)` in CoxMatrices/Basic.lean; `coxMatrix_act_eq_smul_aux` would then be 2 lines.
- `IsImaginaryQuadratic`/`IsSingularModulus` lack any characterization lemmas (`isImaginaryQuadratic_iff_minpoly_natDegree_eq_two`, closure under `SL₂(ℤ)`: `IsImaginaryQuadratic (γ • τ) ↔ IsImaginaryQuadratic τ`) — the latter would be needed to state Cox 11.1 in full.

### Junk candidates
- `not_isSquare_of_between_sq_aux` (L59): replaceable by `Nat.not_exists_sq` (see above).
- No dead `#check`/`example`, no commented-out code, no TODO/FIXME. Docstring L11–14 accurately describes the file.

### Moral duplicates within this batch
- `exists_positive_nonsquare_det_of_even_aux` ↔ `_odd_aux` (same skeleton, see above).
- `not_isSquare_of_between_sq_aux` ↔ mathlib `Nat.not_exists_sq'`.
- `exists_nonsquare_modularPolynomialDiagonal_root` (L202–216) re-plays the `specializeY`/`coxPhiAtJ`/`Finset.prod_eq_zero` steps of `modularPolynomialC_eval_levelJ_j` (Construction.lean:362–369) and of `modularPolynomialC_three_laurent_root` (LevelThree.lean:689–700): a general `modularPolynomialC_eval_act_j (σ : CoxMatrix m) (τ) : (modularPolynomialC m).eval (j (σ.act τ)) (j τ) = 0` in Construction.lean would serve all three.

### Generalization notes
- `not_isSquare_of_between_sq_aux`: `k : ℤ` with `0 ≤ k` is just `k : ℕ`; state over `ℕ` (then it *is* `Nat.not_exists_sq'`).
- `fixingMatrix_det`, `fixingMatrix_content_eq_one`: hold for any `A B C : ℤ` (only `primitive` is used, not `equation`/`discriminant_neg`); the structure could be split into "integer triple with gcd 1" + the analytic equation.
- `coxMatrix_act_eq_smul_aux`: the SL₂-part is independent of `q` (see Missing API).
- `isIntegral_j_of_isImaginaryQuadratic` gives `IsIntegral ℤ`; the finer statement (degree of `j(τ)` = class number) is out of scope for this file.
