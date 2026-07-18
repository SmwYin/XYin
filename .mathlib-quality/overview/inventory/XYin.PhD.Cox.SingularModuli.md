# XYin/PhD/Cox/SingularModuli.lean — project imports: `XYin.PhD.Cox.Arithmetic`

### `structure Cox.PrimitiveQuadraticEquation`
- **Type**: `structure PrimitiveQuadraticEquation (τ : ℍ)` with fields `A B C : ℤ`, `equation : (A:ℂ)*τ^2 + B*τ + C = 0`, `discriminant_neg : B^2 - 4*A*C < 0`, `primitive : Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs = 1`
- **What**: Packages a primitive integral quadratic equation `Aτ² + Bτ + C = 0` of negative discriminant satisfied by a point `τ` of the upper half-plane — the witness that `τ` is a CM (imaginary quadratic) point.
- **How**: Plain structure definition; no proof content. Primitivity is stated as gcd of the three coefficients' absolute values being 1.
- **Hypotheses**: `τ : ℍ`; the fields themselves carry the equation, negativity of discriminant, and primitivity.
- **Uses from project**: []
- **Used by**: `IsImaginaryQuadratic`, `fixingMatrix`, `fixingMatrix_det`, `exists_positive_nonsquare_det_of_even_aux`, `exists_positive_nonsquare_det_of_odd_aux`, `exists_positive_nonsquare_det`, `fixingMatrix_content_eq_one`, `coxMatrix_act_eq_smul_aux`, `exists_nonsquare_coxMatrix_j_eq`, `exists_nonsquare_modularPolynomialDiagonal_root`
- **Visibility**: public
- **Lines**: 25–34 (definition, no proof)
- **Notes**: none

### `def Cox.IsImaginaryQuadratic`
- **Type**: `def IsImaginaryQuadratic (τ : ℍ) : Prop := Nonempty (PrimitiveQuadraticEquation τ)`
- **What**: A point of the upper half-plane is imaginary quadratic when some primitive negative-discriminant integral quadratic equation vanishes at it.
- **How**: Definition as `Nonempty` of the structure type; no proof.
- **Hypotheses**: none beyond `τ : ℍ`.
- **Uses from project**: [`PrimitiveQuadraticEquation`]
- **Used by**: `IsSingularModulus`, `exists_nonsquare_modularPolynomialDiagonal_root`, `isIntegral_j_of_isImaginaryQuadratic`
- **Visibility**: public
- **Lines**: 38–39
- **Notes**: none

### `def Cox.IsSingularModulus`
- **Type**: `def IsSingularModulus (z : ℂ) : Prop := ∃ τ : ℍ, IsImaginaryQuadratic τ ∧ z = j τ`
- **What**: A complex number is a singular modulus when it is the value of the analytic `j`-function at an imaginary-quadratic point.
- **How**: Existential definition; no proof.
- **Hypotheses**: none beyond `z : ℂ`.
- **Uses from project**: [`IsImaginaryQuadratic`, `j` (XYin.PhD.jFunction.jfunction)]
- **Used by**: `singularModulus_isIntegral`
- **Visibility**: public
- **Lines**: 42–43
- **Notes**: none

### `def Cox.PrimitiveQuadraticEquation.fixingMatrix`
- **Type**: `def fixingMatrix (n : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![n, -q.C; q.A, n + q.B]`
- **What**: The one-parameter family of integer matrices `Mₙ = [[n, −C], [A, n+B]]` from the proof of Report Theorem 5.9; each member fixes `τ` under the Möbius action because `Aτ² + Bτ + C = 0`.
- **How**: Explicit matrix literal; no proof.
- **Hypotheses**: `q` a primitive quadratic equation for `τ`; `n : ℤ` free.
- **Uses from project**: [`PrimitiveQuadraticEquation`]
- **Used by**: `fixingMatrix_det`, `exists_positive_nonsquare_det_of_even_aux`, `exists_positive_nonsquare_det_of_odd_aux`, `exists_positive_nonsquare_det`, `fixingMatrix_content_eq_one`, `coxMatrix_act_eq_smul_aux`, `exists_nonsquare_coxMatrix_j_eq`
- **Visibility**: public
- **Lines**: 50–51
- **Notes**: none

### `theorem Cox.PrimitiveQuadraticEquation.fixingMatrix_det`
- **Type**: `(q.fixingMatrix n).det = n ^ 2 + q.B * n + q.A * q.C`
- **What**: Computes the determinant of `Mₙ` as the quadratic `n² + Bn + AC` in the parameter `n`.
- **How**: Expand the 2×2 determinant via `Matrix.det_fin_two_of` and close with `ring`.
- **Hypotheses**: none beyond the structure `q`.
- **Uses from project**: [`fixingMatrix`, `PrimitiveQuadraticEquation`]
- **Used by**: `exists_positive_nonsquare_det_of_even_aux`, `exists_positive_nonsquare_det_of_odd_aux`
- **Visibility**: public
- **Lines**: 53–57 (proof 2 lines)
- **Notes**: @[simp]

### `lemma Cox.PrimitiveQuadraticEquation.not_isSquare_of_between_sq_aux`
- **Type**: `{k : ℤ} {N : ℕ} (hk : 0 ≤ k) (hlo : k ^ 2 < (N : ℤ)) (hhi : (N : ℤ) < (k + 1) ^ 2) : ¬ IsSquare N`
- **What**: A natural number strictly between two consecutive integer squares `k²` and `(k+1)²` is not a perfect square.
- **How**: If `N = r²`, monotonicity of squaring on nonnegatives (`sq_lt_sq₀`) forces `k < r < k + 1`, contradicting integrality via `omega`.
- **Hypotheses**: `0 ≤ k`, `k² < N < (k+1)²`.
- **Uses from project**: []
- **Used by**: `exists_positive_nonsquare_det_of_even_aux`, `exists_positive_nonsquare_det_of_odd_aux`
- **Visibility**: private
- **Lines**: 59–72 (proof 12 lines)
- **Notes**: none

### `lemma Cox.PrimitiveQuadraticEquation.exists_positive_nonsquare_det_of_even_aux`
- **Type**: `{b : ℤ} (hB : q.B = 2 * b) : ∃ (n : ℤ) (N : ℕ+), (q.fixingMatrix n).det = (N : ℤ) ∧ ¬ IsSquare (N : ℕ)`
- **What**: Even case of the nonsquare-determinant selection: when `B = 2b`, an explicit choice of `n` makes `det Mₙ` a positive nonsquare integer.
- **How**: Set `k = AC − b² > 0` (positivity from the negative discriminant `4b² − 4AC < 0` via `nlinarith`) and take `n = k − b`; then `det Mₙ = (k−b)² + 2b(k−b) + AC = k² + k`, which lies strictly between `k²` and `(k+1)²`, so `not_isSquare_of_between_sq_aux` applies.
- **Hypotheses**: `q.B` is even with half `b`.
- **Uses from project**: [`fixingMatrix`, `fixingMatrix_det`, `not_isSquare_of_between_sq_aux`, `PrimitiveQuadraticEquation` (field `discriminant_neg`)]
- **Used by**: `exists_positive_nonsquare_det`
- **Visibility**: private
- **Lines**: 74–101 (proof 26 lines)
- **Notes**: none

### `lemma Cox.PrimitiveQuadraticEquation.exists_positive_nonsquare_det_of_odd_aux`
- **Type**: `{b : ℤ} (hB : q.B = 2 * b + 1) : ∃ (n : ℤ) (N : ℕ+), (q.fixingMatrix n).det = (N : ℤ) ∧ ¬ IsSquare (N : ℕ)`
- **What**: Odd case of the nonsquare-determinant selection: when `B = 2b + 1`, an explicit choice of `n` makes `det Mₙ` a positive nonsquare integer.
- **How**: Set `k = AC − b(b+1) > 0` (from `(2b+1)² − 4AC < 0` via `nlinarith`) and take `n = k − b`; then `det Mₙ = k² + 2k`, strictly between `k²` and `(k+1)² = k² + 2k + 1`, and conclude by `not_isSquare_of_between_sq_aux`.
- **Hypotheses**: `q.B` is odd with `B = 2b + 1`.
- **Uses from project**: [`fixingMatrix`, `fixingMatrix_det`, `not_isSquare_of_between_sq_aux`, `PrimitiveQuadraticEquation` (field `discriminant_neg`)]
- **Used by**: `exists_positive_nonsquare_det`
- **Visibility**: private
- **Lines**: 103–130 (proof 26 lines)
- **Notes**: none

### `theorem Cox.PrimitiveQuadraticEquation.exists_positive_nonsquare_det`
- **Type**: `∃ (n : ℤ) (N : ℕ+), (q.fixingMatrix n).det = (N : ℤ) ∧ ¬ IsSquare (N : ℕ)`
- **What**: Some member of the fixing family `Mₙ` has positive nonsquare determinant — the key arithmetic input to Theorem 5.9 (nonsquare level ensures leading coefficient ±1 of the diagonal modular polynomial).
- **How**: Case split on the parity of `B` via `Int.even_or_odd'` and dispatch to the two parity-specific auxiliary lemmas.
- **Hypotheses**: none beyond the structure `q`.
- **Uses from project**: [`exists_positive_nonsquare_det_of_even_aux`, `exists_positive_nonsquare_det_of_odd_aux`, `fixingMatrix`]
- **Used by**: `exists_nonsquare_coxMatrix_j_eq`
- **Visibility**: public
- **Lines**: 133–138 (proof 4 lines)
- **Notes**: none

### `theorem Cox.PrimitiveQuadraticEquation.fixingMatrix_content_eq_one`
- **Type**: `(n : ℤ) : Matrix.rankTwoContent (q.fixingMatrix n) = 1`
- **What**: Every matrix in the fixing family is primitive: the gcd of its four entries is 1.
- **How**: The content `k` divides the entries `n`, `−C`, `A`, `n+B`, hence divides `B = (n+B) − n` (difference of divisibilities over ℤ, `Int.natCast_dvd`); then `k ∣ gcd(gcd(A,B),C) = 1` by the primitivity field, closed with `Nat.eq_one_of_dvd_one` and `Nat.dvd_gcd`.
- **Hypotheses**: primitivity of `q` (field `primitive`).
- **Uses from project**: [`fixingMatrix`, `Matrix.rankTwoContent` (XYin.PhD.Cox.HermiteNormalForm), `PrimitiveQuadraticEquation` (field `primitive`)]
- **Used by**: `exists_nonsquare_coxMatrix_j_eq`
- **Visibility**: public
- **Lines**: 141–165 (proof 24 lines)
- **Notes**: none

### `lemma Cox.PrimitiveQuadraticEquation.coxMatrix_act_eq_smul_aux`
- **Type**: `{n : ℤ} {N : ℕ+} {γ : SL(2, ℤ)} {σ : CoxMatrix N} (hmat : γ.1 * q.fixingMatrix n = σ.mobiusMatrix) : σ.act τ = γ • τ`
- **What**: If a Cox representative `σ` equals `γ · Mₙ` as an integer matrix, then the action of `σ` on the fixed point `τ` agrees with the `SL₂(ℤ)`-Möbius action of `γ` on `τ`. This is where the quadratic equation is used: `Mₙ` fixes `τ`, so `στ = γMₙτ = γτ`.
- **How**: Compare Möbius quotients after clearing denominators (`field_simp` with `UpperHalfPlane.denom_ne_zero` and `σ.d_pos`); entrywise identities `h00…h11` from `hmat` reduce the claim to a polynomial identity closed by `linear_combination` in terms of the quadratic relation `q.equation` and the entry identity `h10`.
- **Hypotheses**: `γ.1 * Mₙ = σ.mobiusMatrix` as matrices over ℤ; `q.equation` for `τ`.
- **Uses from project**: [`fixingMatrix`, `CoxMatrix`, `CoxMatrix.mobiusMatrix`, `CoxMatrix.act`, `CoxMatrix.coe_act`, `CoxMatrix.d_pos`, `PrimitiveQuadraticEquation` (field `equation`)]
- **Used by**: `exists_nonsquare_coxMatrix_j_eq`
- **Visibility**: private
- **Lines**: 167–196 (proof 29 lines)
- **Notes**: proof just under 30 lines; the `linear_combination` certificate is the mathematical heart of the fixing argument

### `theorem Cox.PrimitiveQuadraticEquation.exists_nonsquare_coxMatrix_j_eq`
- **Type**: `∃ N : ℕ+, ¬ IsSquare (N : ℕ) ∧ ∃ σ : CoxMatrix N, j (σ.act τ) = j τ`
- **What**: At some positive nonsquare level `N` there is a Cox representative whose transform of `τ` has the same `j`-value as `τ` itself — i.e., `j(τ)` is a root of one factor of the level-`N` modular polynomial specialization.
- **How**: Choose `n, N` by `exists_positive_nonsquare_det`, reduce `Mₙ` to Cox form `γ·Mₙ = σ` via `exists_sl2_mul_eq_coxMatrix` (using primitivity `fixingMatrix_content_eq_one`), and conclude `j(στ) = j(γ•τ) = j(τ)` by `coxMatrix_act_eq_smul_aux` and `SL₂(ℤ)`-invariance `j_modularGroup_smul`.
- **Hypotheses**: `q` a primitive quadratic equation for `τ` (`include q`).
- **Uses from project**: [`exists_positive_nonsquare_det`, `exists_sl2_mul_eq_coxMatrix` (XYin.PhD.Cox.CoxMatrices.Basic), `fixingMatrix_content_eq_one`, `coxMatrix_act_eq_smul_aux`, `fixingMatrix`, `j`, `j_modularGroup_smul` (XYin.PhD.jFunction.jfunction), `CoxMatrix`, `CoxMatrix.act`]
- **Used by**: `exists_nonsquare_modularPolynomialDiagonal_root`
- **Visibility**: public
- **Lines**: 201–208 (proof 6 lines)
- **Notes**: none

### `theorem Cox.exists_nonsquare_modularPolynomialDiagonal_root`
- **Type**: `{τ : ℍ} (hτ : IsImaginaryQuadratic τ) : ∃ N : ℕ+, ¬ IsSquare (N : ℕ) ∧ (modularPolynomialDiagonal N).eval₂ (Int.castRingHom ℂ) (j τ) = 0`
- **What**: For an imaginary-quadratic `τ`, the diagonal integral modular polynomial `Φ_N(X, X)` at some nonsquare level `N` vanishes at `j(τ)`.
- **How**: Rewrite the diagonal evaluation into a specialization of the bivariate modular polynomial over ℂ (`BivariatePolynomial.diagonal_eval₂`, `modularPolynomial_map_complex`, `modularPolynomialC_specializeY`), which identifies it with `coxPhiAtJ N τ = ∏_σ (X − j(στ))` evaluated at `j τ`; the factor from `exists_nonsquare_coxMatrix_j_eq` vanishes, so `Finset.prod_eq_zero` closes the goal.
- **Hypotheses**: `τ` is imaginary quadratic.
- **Uses from project**: [`IsImaginaryQuadratic`, `PrimitiveQuadraticEquation.exists_nonsquare_coxMatrix_j_eq`, `modularPolynomialDiagonal` (XYin.PhD.Cox.Arithmetic), `BivariatePolynomial.diagonal_eval₂`, `BivariatePolynomial.map`, `modularPolynomial` (XYin.PhD.Cox.ModularPolynomial.IntegralDescent), `modularPolynomial_map_complex`, `BivariatePolynomial.specializeY_eval`, `modularPolynomialC_specializeY`, `coxPhiAtJ` (XYin.PhD.Cox.ModularPolynomial.Construction), `j`]
- **Used by**: `isIntegral_j_of_isImaginaryQuadratic`
- **Visibility**: public
- **Lines**: 214–228 (proof 13 lines)
- **Notes**: none

### `theorem Cox.isIntegral_j_of_isImaginaryQuadratic`
- **Type**: `{τ : ℍ} (hτ : IsImaginaryQuadratic τ) : IsIntegral ℤ (j τ)`
- **What**: Report Theorem 5.9: the `j`-value of an imaginary-quadratic point of the upper half-plane is an algebraic integer.
- **How**: Take the nonsquare level `N` from `exists_nonsquare_modularPolynomialDiagonal_root`; by `theorem_11_18_iv_leadingCoeff` (Cox Theorem 11.18(iv)) the diagonal polynomial has leading coefficient `±1`, so either it or its negation is monic (`Polynomial.leadingCoeff_neg`), giving a monic integer polynomial vanishing at `j τ`.
- **Hypotheses**: `τ` is imaginary quadratic.
- **Uses from project**: [`IsImaginaryQuadratic`, `exists_nonsquare_modularPolynomialDiagonal_root`, `modularPolynomialDiagonal`, `theorem_11_18_iv_leadingCoeff` (XYin.PhD.Cox.Arithmetic), `j`]
- **Used by**: `singularModulus_isIntegral`
- **Visibility**: public
- **Lines**: 231–242 (proof 11 lines)
- **Notes**: none

### `theorem Cox.singularModulus_isIntegral`
- **Type**: `{z : ℂ} (hz : IsSingularModulus z) : IsIntegral ℤ z`
- **What**: Every singular modulus is an algebraic integer — the headline corollary of the file.
- **How**: Unpack the witness `z = j τ` and apply `isIntegral_j_of_isImaginaryQuadratic`.
- **Hypotheses**: `z` is a singular modulus.
- **Uses from project**: [`IsSingularModulus`, `isIntegral_j_of_isImaginaryQuadratic`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 245–248 (proof 3 lines)
- **Notes**: none

### File Summary
- Total declarations: 15 (4 defs [1 structure + 3 defs], 11 lemmas/theorems, 0 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `PrimitiveQuadraticEquation` (10 users), `fixingMatrix` (7 users), `fixingMatrix_det` (2 direct users but foundational), `not_isSquare_of_between_sq_aux` (2 users); by strict 3+ count: `PrimitiveQuadraticEquation`, `fixingMatrix`, `IsImaginaryQuadratic` (3 users)
- Unused declarations (not used by anything in this file): `singularModulus_isIntegral` (terminal result)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [] (longest: `coxMatrix_act_eq_smul_aux` at 29 proof lines)
