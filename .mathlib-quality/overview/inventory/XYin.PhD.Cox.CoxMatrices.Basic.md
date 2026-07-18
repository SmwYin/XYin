# Inventory: `XYin/PhD/Cox/CoxMatrices/Basic.lean`

Source: `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Cox/CoxMatrices/Basic.lean`
Project-internal imports: `XYin.PhD.Cox.HermiteNormalForm`, `XYin.PhD.Cox.ModularFunction`

File theme: defines Cox's set `C(m)` of primitive upper-triangular determinant-`m` matrices, proves it is in bijection with the right cosets of `Γ₀(m)` in `SL₂(ℤ)` (Cox Lemma 11.11) via rank-two Hermite normal form, and develops the induced coset action on `Γ₀(m)`-modular functions, culminating in Cox equation (11.12): the coset conjugate `j(mγτ)` equals `j(σ·τ)` for the matching Cox representative.

All declarations live in namespace `Cox` (some in `Cox.CoxMatrix`); the whole file is inside `noncomputable section`.

---

### `structure CoxMatrix`
- **Type**: `CoxMatrix (m : ℕ+) : Type` with fields `a b d : ℕ`, `a_pos : 0 < a`, `determinant : a * d = m`, `b_lt : b < d`, `primitive : Nat.gcd (Nat.gcd a b) d = 1`
- **What**: Cox's finite set `C(m)`: primitive upper-triangular integer matrices `[[a, b], [0, d]]` with determinant `ad = m`, `0 ≤ b < d`, and gcd of the entries 1. These are the standard coset representatives for `Γ₀(m)\SL₂(ℤ)` in the theory of the modular equation.
- **How**: Data structure; the mathematical content is the choice of normalization (upper triangular, `b` reduced mod `d`, content 1).
- **Hypotheses**: `m` a positive natural.
- **Uses from project**: []
- **Used by**: essentially every declaration in the file (d_pos, a_le, d_le, mobiusMatrix, inclusionMatrix, act, toFin, sigmaZero, one_lt_card_coxMatrix, exists_coxMatrix_reduction, coxRepresentative, coxMatrixEquivRightCosets, rightCosetEval_equiv, exists_sl2_mul_eq_coxMatrix, ...)
- **Visibility**: public
- **Lines**: 23–31
- **Notes**: none

### `theorem CoxMatrix.d_pos`
- **Type**: `(σ : CoxMatrix m) : 0 < σ.d`
- **What**: The lower-right entry `d` of a Cox matrix is positive.
- **How**: Since `a * d = m > 0`, positivity of the product forces `d > 0` (`pos_of_mul_pos_right` with `PNat.pos`).
- **Hypotheses**: none beyond the structure fields.
- **Uses from project**: [`CoxMatrix.determinant`]
- **Used by**: `a_le`, `inclusionMatrix_isColumnHermiteNormalForm`, `act`, `levelJ_smul_eq_j_act_of_normalization`
- **Visibility**: public
- **Lines**: 37–41, 5-line proof
- **Notes**: none

### `theorem CoxMatrix.a_le`
- **Type**: `(σ : CoxMatrix m) : σ.a ≤ (m : ℕ)`
- **What**: The entry `a` is bounded by the level `m`.
- **How**: `a ≤ a * d = m` since `d ≥ 1` (`Nat.le_mul_of_pos_right` with `d_pos`).
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.determinant`, `CoxMatrix.d_pos`]
- **Used by**: `toFin`
- **Visibility**: public
- **Lines**: 43–45, 3-line proof
- **Notes**: none

### `theorem CoxMatrix.d_le`
- **Type**: `(σ : CoxMatrix m) : σ.d ≤ (m : ℕ)`
- **What**: The entry `d` is bounded by the level `m`.
- **How**: `d ≤ a * d = m` since `a ≥ 1` (`Nat.le_mul_of_pos_left` with `a_pos`).
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.determinant`]
- **Used by**: `toFin`
- **Visibility**: public
- **Lines**: 47–49, 3-line proof
- **Notes**: none

### `def CoxMatrix.mobiusMatrix`
- **Type**: `(σ : CoxMatrix m) : Matrix (Fin 2) (Fin 2) ℤ`
- **What**: The integer matrix `[[a, b], [0, d]]` through which `σ` acts on the upper half-plane by Möbius transformation.
- **How**: Direct `!![...]` literal casting the ℕ fields into ℤ.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `matrixStar_mobiusMatrix`, `matrixStar_inclusionMatrix`, `coxRepresentative_normalization`, `levelJ_smul_eq_j_act_of_normalization`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: public
- **Lines**: 51–53
- **Notes**: none

### `def CoxMatrix.inclusionMatrix`
- **Type**: `(σ : CoxMatrix m) : Matrix (Fin 2) (Fin 2) ℤ`
- **What**: The column-HNF inclusion matrix `[[d, b], [0, a]]` of the index-`m` sublattice `[d, aτ+b]` of `[1, τ]` attached to `σ`. It is the "star" (anti-transpose) of `mobiusMatrix`.
- **How**: Direct `!![...]` literal; the entry swap relative to `mobiusMatrix` matches the HNF convention used in `XYin.PhD.Cox.HermiteNormalForm`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `inclusionMatrix_isColumnHermiteNormalForm`, `inclusionMatrix_det`, `inclusionMatrix_content_eq_one`, `matrixStar_mobiusMatrix`, `inclusionMatrix_injective`, `exists_coxMatrix_reduction`, `coxMatrix_reduction_unique`, `coxReduction_spec`, `matrixStar_inclusionMatrix`, `coxInput_one`, `coxMatrix_smith_normalization`, `coxRepresentative_surjective`, `exists_coxMatrix_of_isColumnHermiteNormalForm_aux`
- **Visibility**: public
- **Lines**: 55–57
- **Notes**: none

### `theorem CoxMatrix.inclusionMatrix_isColumnHermiteNormalForm`
- **Type**: `(σ : CoxMatrix m) : σ.inclusionMatrix.IsColumnHermiteNormalForm`
- **What**: The inclusion matrix of a Cox representative is in column Hermite normal form (positive diagonal, zero below diagonal, off-diagonal entry reduced).
- **How**: Applies the project criterion `Matrix.isColumnHermiteNormalForm_fin_two` (from `HermiteNormalForm.lean`), discharging the four conditions `0 < d`, `0 < a`, `0 ≤ b`, `b < d` from the structure fields by casting.
- **Hypotheses**: none.
- **Uses from project**: [`Matrix.isColumnHermiteNormalForm_fin_two` (HermiteNormalForm), `CoxMatrix.inclusionMatrix`, `CoxMatrix.d_pos`, `CoxMatrix.b_lt`, `CoxMatrix.a_pos`]
- **Used by**: `coxMatrix_reduction_unique`
- **Visibility**: public
- **Lines**: 59–65, 6-line proof
- **Notes**: none

### `theorem CoxMatrix.inclusionMatrix_det`
- **Type**: `(σ : CoxMatrix m) : σ.inclusionMatrix.det = (m : ℕ)`
- **What**: The inclusion matrix has determinant `m`, i.e. the associated sublattice has index `m`.
- **How**: `det [[d,b],[0,a]] = d·a`, then commutativity and the structure field `determinant : a·d = m` (via `Matrix.det_fin_two_of`).
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.inclusionMatrix`, `CoxMatrix.determinant`]
- **Used by**: `coxMatrix_smith_normalization`
- **Visibility**: public
- **Lines**: 67–72, 4-line proof
- **Notes**: none

### `theorem CoxMatrix.inclusionMatrix_content_eq_one`
- **Type**: `(σ : CoxMatrix m) : Matrix.rankTwoContent σ.inclusionMatrix = 1`
- **What**: The inclusion matrix is primitive: the gcd of its four entries is 1.
- **How**: Unfolds `Matrix.rankTwoContent` (from `HermiteNormalForm.lean`) and rearranges the nested gcd with `Nat.gcd_comm`/`Nat.gcd_left_comm`/`Nat.gcd_assoc` to match the `primitive` field.
- **Hypotheses**: none.
- **Uses from project**: [`Matrix.rankTwoContent` (HermiteNormalForm), `CoxMatrix.inclusionMatrix`, `CoxMatrix.primitive`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 74–77, 3-line proof
- **Notes**: none

### `def CoxMatrix.act`
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : ℍ`
- **What**: The Möbius action of `σ` on the upper half-plane: `τ ↦ (aτ + b)/d`. This lands in ℍ because `a, d > 0`.
- **How**: Constructs the point with an embedded positivity proof: the imaginary part of `(aτ+b)/d` is computed as `a·Im(τ)/d` via `Complex.div_im` and `Complex.normSq_natCast`, then `div_pos`/`mul_pos` with `a_pos`, `d_pos`, `τ.im_pos`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.d_pos`, `CoxMatrix.a_pos`]
- **Used by**: `coe_act`, `levelJ_smul_eq_j_act_of_normalization`, `rightCosetEval_equiv`, `j_act_sigmaZero`
- **Visibility**: public
- **Lines**: 79–92 (14 lines including membership proof)
- **Notes**: none

### `theorem CoxMatrix.coe_act`
- **Type**: `(σ : CoxMatrix m) (τ : ℍ) : ((σ.act τ : ℍ) : ℂ) = ((σ.a : ℂ) * τ + σ.b) / σ.d`
- **What**: The complex coordinate of `σ.act τ` is the expected fraction `(aτ+b)/d`.
- **How**: `rfl` — definitional unfolding.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.act`]
- **Used by**: `levelJ_smul_eq_j_act_of_normalization`
- **Visibility**: public
- **Lines**: 94–96, rfl proof
- **Notes**: @[simp]

### `def CoxMatrix.toFin`
- **Type**: `(σ : CoxMatrix m) : Fin (m+1) × Fin (m+1) × Fin (m+1)`
- **What**: A bounded encoding of a Cox matrix as a triple of naturals below `m+1`, used to derive finiteness of `C(m)`.
- **How**: Packages `(a, b, d)` with bound proofs from `a_le`, `b_lt` (chained with `d_le`), and `d_le`, discharged by `omega`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.a_le`, `CoxMatrix.b_lt`, `CoxMatrix.d_le`]
- **Used by**: `toFin_injective`, `instance DecidableEq`, `instance Fintype`
- **Visibility**: public
- **Lines**: 98–103
- **Notes**: none

### `theorem CoxMatrix.toFin_injective`
- **Type**: `Function.Injective (toFin (m := m))`
- **What**: The bounded encoding is injective, i.e. a Cox matrix is determined by `(a, b, d)`.
- **How**: Extracts equalities of components via `congrArg` on the projections; the proof fields are propositions, so `cases`+`simp_all` closes structure equality (proof irrelevance).
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.toFin`]
- **Used by**: `instance DecidableEq`, `instance Fintype`
- **Visibility**: public
- **Lines**: 105–112, 8-line proof
- **Notes**: none

### `instance : DecidableEq (CoxMatrix m)`
- **Type**: `DecidableEq (CoxMatrix m)`
- **What**: Equality of Cox matrices is decidable.
- **How**: Transfers decidability along the injective encoding: `decidable_of_iff` on `toFin_injective.eq_iff`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.toFin`, `CoxMatrix.toFin_injective`]
- **Used by**: unused in file
- **Visibility**: public (anonymous instance)
- **Lines**: 114–115
- **Notes**: none

### `instance : Fintype (CoxMatrix m)`
- **Type**: `Fintype (CoxMatrix m)`
- **What**: Cox's set `C(m)` is finite.
- **How**: `Fintype.ofInjective` with the injective bounded encoding `toFin` into a finite product of `Fin` types.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.toFin`, `CoxMatrix.toFin_injective`]
- **Used by**: `one_lt_card_coxMatrix` (through `Fintype.card`)
- **Visibility**: public (anonymous instance)
- **Lines**: 117
- **Notes**: none

### `def sigmaZero`
- **Type**: `(m : ℕ+) : CoxMatrix m`
- **What**: Cox's distinguished representative `σ₀ = diag(m, 1)` (i.e. `a = m`, `b = 0`, `d = 1`), corresponding to the identity coset and to the sublattice giving `j(mτ)`.
- **How**: Direct construction; primitivity is `gcd(gcd(m,0),1) = 1` by `simp`.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`]
- **Used by**: `one_lt_card_coxMatrix`, `coxInput_one`, `coxRepresentative_one`, `coxMatrixEquivRightCosets_sigmaZero`, `rightCosetTranslate_sigmaZero`, `j_act_sigmaZero`
- **Visibility**: public
- **Lines**: 121–129
- **Notes**: none

### `theorem one_lt_card_coxMatrix`
- **Type**: `(m : ℕ+) (hm : 1 < (m : ℕ)) : 1 < Fintype.card (CoxMatrix m)`
- **What**: For level `m > 1` the set `C(m)` has at least two elements (so `Γ₀(m)` has index > 1). Exhibits the two diagonal representatives `diag(1,m)` and `diag(m,1)`.
- **How**: Builds the second representative `a=1, b=0, d=m` explicitly and applies `Fintype.one_lt_card_iff`; the two differ in the `a` entry since `1 ≠ m` by `omega`.
- **Hypotheses**: `m > 1`.
- **Uses from project**: [`CoxMatrix`, `sigmaZero`, `instance Fintype (CoxMatrix m)`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 132–147, 16-line proof
- **Notes**: none

### `abbrev Gamma0RightCosets`
- **Type**: `(m : ℕ+) : Type := Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 m))`
- **What**: The set of right cosets `Γ₀(m)γ` of the congruence subgroup `Γ₀(m)` in `SL₂(ℤ)`.
- **How**: Abbreviation for the quotient by mathlib's `QuotientGroup.rightRel`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `gamma0RightCosetsFintype`, `rightCosetToCoxMatrix`, `coxMatrixEquivRightCosets`, `rightCosetTranslate`, `rightCosetEval`, `rightCosetMul`, `baseRightCoset`, `exists_rightCosetMul_baseRightCoset_eq`, `rightCosetTranslate_smul`, `rightCosetEval_smul`, `rightCosetEval_equiv`
- **Visibility**: public
- **Lines**: 150–151
- **Notes**: none

### `instance gamma0RightCosetsFintype`
- **Type**: `(m : ℕ+) : Fintype (Gamma0RightCosets m)`
- **What**: The set of right cosets of `Γ₀(m)` is finite (since `Γ₀(m)` has finite index in `SL₂(ℤ)`).
- **How**: Instantiates `NeZero m`, infers `(Gamma0 m).FiniteIndex` from mathlib, obtains a `Fintype` on the left-coset quotient via `Subgroup.fintypeQuotientOfFiniteIndex`, and transfers it along mathlib's `QuotientGroup.quotientRightRelEquivQuotientLeftRel`.
- **Hypotheses**: none (finite index is automatic for `m ≠ 0`).
- **Uses from project**: [`Gamma0RightCosets`]
- **Used by**: unused in file
- **Visibility**: public (named instance)
- **Lines**: 153–161, 9-line proof
- **Notes**: noncomputable instance

### `def matrixStar` (private)
- **Type**: `(A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ`
- **What**: The "star" involution `[[a,b],[c,d]] ↦ [[d,b],[c,a]]` (swap the diagonal, keep the antidiagonal). It is the adjugate composed with rotation; concretely it exchanges the Möbius-matrix and inclusion-matrix conventions and is an anti-homomorphism for multiplication.
- **How**: Direct entry-level definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `matrixStar_involutive`, `matrixStar_mul`, `matrixStar_det`, `matrixStar_mobiusMatrix`, `matrixStar_determinantScale`, `coxInput`, `slStar`, `coe_slStar`, `matrixStar_inclusionMatrix`, `coxRepresentative_normalization`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 163–165
- **Notes**: none

### `theorem matrixStar_involutive` (private)
- **Type**: `(A) : matrixStar (matrixStar A) = A`
- **What**: The star operation is an involution.
- **How**: Entry-by-entry `rfl` after `fin_cases`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`]
- **Used by**: `matrixStar_inclusionMatrix`, `coxRepresentative_normalization`, `coxRepresentative_surjective`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 167–170, 4-line proof
- **Notes**: none

### `theorem matrixStar_mul` (private)
- **Type**: `(A B) : matrixStar (A * B) = matrixStar B * matrixStar A`
- **What**: Star is an anti-homomorphism: it reverses matrix products. This is the key algebraic fact letting right-multiplication statements (column HNF) be converted to left-multiplication statements (Cox's normalization).
- **How**: Entry-by-entry computation with `Matrix.mul_apply`, `Fin.sum_univ_two`, and `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`]
- **Used by**: `coxRepresentative_normalization`, `coxRepresentative_surjective`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 172–177, 6-line proof
- **Notes**: none

### `theorem matrixStar_det` (private)
- **Type**: `(A) : (matrixStar A).det = A.det`
- **What**: Star preserves the determinant (it swaps the two diagonal entries, leaving `ad − bc` unchanged).
- **How**: `Matrix.det_fin_two` expansion plus `ring`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`]
- **Used by**: `coxInput_det`, `slStar`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 179–182, 4-line proof
- **Notes**: none

### `theorem matrixStar_mobiusMatrix` (private)
- **Type**: `{m : ℕ+} (σ : CoxMatrix m) : matrixStar σ.mobiusMatrix = σ.inclusionMatrix`
- **What**: The star of a Cox Möbius matrix `[[a,b],[0,d]]` is its inclusion matrix `[[d,b],[0,a]]`.
- **How**: Entry-by-entry `rfl` after `fin_cases`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`, `CoxMatrix.mobiusMatrix`, `CoxMatrix.inclusionMatrix`]
- **Used by**: `matrixStar_inclusionMatrix`
- **Visibility**: private
- **Lines**: 184–187, 4-line proof
- **Notes**: none

### `def determinantScale` (private)
- **Type**: `(m : ℕ+) : Matrix (Fin 2) (Fin 2) ℤ`
- **What**: The scaling matrix `diag(m, 1)`; left-multiplying a `γ ∈ SL₂(ℤ)` by it produces the determinant-`m` matrix whose Möbius action is `τ ↦ m·(γτ)`.
- **How**: Direct `!![...]` literal.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `matrixStar_determinantScale`, `determinantScale_det`, `coxInput`, `coxRepresentative_normalization`
- **Visibility**: private
- **Lines**: 189–190
- **Notes**: none

### `def determinantScaleDual` (private)
- **Type**: `(m : ℕ+) : Matrix (Fin 2) (Fin 2) ℤ`
- **What**: The dual scaling matrix `diag(1, m)` — the star of `determinantScale`, and the Smith-normal-form target for primitive determinant-`m` matrices.
- **How**: Direct `!![...]` literal.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `matrixStar_determinantScale`, `coxMatrix_smith_normalization`, `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 192–193
- **Notes**: none

### `theorem matrixStar_determinantScale` (private)
- **Type**: `(m : ℕ+) : matrixStar (determinantScale m) = determinantScaleDual m`
- **What**: The star of `diag(m,1)` is `diag(1,m)`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`, `determinantScale`, `determinantScaleDual`]
- **Used by**: `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 195–197, rfl proof
- **Notes**: none

### `theorem determinantScale_det` (private)
- **Type**: `(m : ℕ+) : (determinantScale m).det = (m : ℤ)`
- **What**: `diag(m,1)` has determinant `m`.
- **How**: `Matrix.det_fin_two_of` and `simp`.
- **Hypotheses**: none.
- **Uses from project**: [`determinantScale`]
- **Used by**: `coxInput_det`
- **Visibility**: private
- **Lines**: 199–201, 2-line proof
- **Notes**: none

### `def coxInput` (private)
- **Type**: `(m : ℕ+) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ`
- **What**: The star of `diag(m,1)·γ` — the determinant-`m` primitive matrix whose column-HNF reduction produces the Cox representative of the right coset `Γ₀(m)γ`. Concretely `[[γ₁₁, m·γ₀₁], [γ₁₀, m·γ₀₀]]`.
- **How**: `matrixStar (determinantScale m * γ.1)`; the star converts the left `SL₂(ℤ)`-normalization problem into a right-multiplication (column-operation) problem so the project's HNF machinery applies.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`, `determinantScale`]
- **Used by**: `coxInput_eq`, `coxInput_det`, `coxInput_content_eq_one`, `rightRel_of_coxInput_eq_mul`, `exists_coxInput_eq_mul_of_rightRel`, `exists_coxMatrix_reduction`, `coxMatrix_reduction_unique`, `coxReduction_spec`, `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_normalization`, `coxInput_one`, `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 203–204
- **Notes**: none

### `theorem coxInput_eq` (private)
- **Type**: `(m γ) : coxInput m γ = !![γ 1 1, m * γ 0 1; γ 1 0, m * γ 0 0]`
- **What**: Explicit entry formula for `coxInput`.
- **How**: Entry-by-entry computation unfolding `matrixStar`, `determinantScale`, and `Matrix.mul_apply` with `Fin.sum_univ_two`.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `matrixStar`, `determinantScale`]
- **Used by**: `coxInput_content_eq_one`, `rightRel_of_coxInput_eq_mul`, `exists_coxInput_eq_mul_of_rightRel`, `coxInput_one`
- **Visibility**: private
- **Lines**: 206–211, 5-line proof
- **Notes**: none

### `theorem coxInput_det` (private)
- **Type**: `(m γ) : (coxInput m γ).det = (m : ℤ)`
- **What**: The Cox input matrix has determinant `m`.
- **How**: Star preserves determinant (`matrixStar_det`), `det(diag(m,1)) = m` (`determinantScale_det`), and `det γ = 1` (`Matrix.SpecialLinearGroup.det_coe`), combined via `Matrix.det_mul`.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `matrixStar_det`, `determinantScale_det`]
- **Used by**: `exists_coxMatrix_reduction`
- **Visibility**: private
- **Lines**: 213–216, 3-line proof
- **Notes**: none

### `theorem coxInput_content_eq_one` (private)
- **Type**: `(m γ) : Matrix.rankTwoContent (coxInput m γ) = 1`
- **What**: The Cox input matrix is primitive: since the bottom row of `γ ∈ SL₂(ℤ)` is coprime and appears (unscaled) as the first column of `coxInput`, the gcd of all four entries is 1.
- **How**: Uses mathlib's `ModularGroup.bottom_row_coprime` and `Int.isCoprime_iff_gcd_eq_one` to get `gcd(γ₁₀, γ₁₁) = 1`, then reassociates the nested `Nat.gcd` with `ac_rfl` so the coprime pair absorbs the rest.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `coxInput_eq`, `Matrix.rankTwoContent` (HermiteNormalForm)]
- **Used by**: `exists_coxMatrix_reduction`
- **Visibility**: private
- **Lines**: 218–232, 15-line proof
- **Notes**: none

### `theorem rankTwoContent_dvd_entry_aux` (private)
- **Type**: `(A : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) : A.rankTwoContent ∣ (A i j).natAbs`
- **What**: The content (gcd of the four entries) of a 2×2 integer matrix divides each entry's absolute value.
- **How**: Case split on `(i, j)` and chains of `Nat.gcd_dvd_left`/`Nat.gcd_dvd_right` through the nested gcd.
- **Hypotheses**: none.
- **Uses from project**: [`Matrix.rankTwoContent` (HermiteNormalForm)]
- **Used by**: `rankTwoContent_dvd_mul_right_aux`
- **Visibility**: private
- **Lines**: 234–242, 9-line proof
- **Notes**: none

### `theorem dvd_rankTwoContent_aux` (private)
- **Type**: `{A} {k : ℕ} (h : ∀ i j, k ∣ (A i j).natAbs) : k ∣ A.rankTwoContent`
- **What**: A common divisor of all four entries divides the content — the universal property of the gcd of the entries.
- **How**: Term-mode nesting of `Nat.dvd_gcd`.
- **Hypotheses**: `k` divides every entry (in absolute value).
- **Uses from project**: [`Matrix.rankTwoContent` (HermiteNormalForm)]
- **Used by**: `rankTwoContent_dvd_mul_right_aux`
- **Visibility**: private
- **Lines**: 244–246, term proof
- **Notes**: none

### `theorem rankTwoContent_dvd_mul_right_aux` (private)
- **Type**: `(A B) : A.rankTwoContent ∣ (A * B).rankTwoContent`
- **What**: The content of `A` divides the content of `A·B`: each entry of the product is a ℤ-linear combination of entries of `A`.
- **How**: Reduces to entrywise divisibility via `dvd_rankTwoContent_aux`; each product entry `Σ A i k · B k j` is handled with `dvd_add`, `dvd_mul_of_dvd_left`, and `rankTwoContent_dvd_entry_aux` transported to ℤ by `Int.natCast_dvd`.
- **Hypotheses**: none.
- **Uses from project**: [`dvd_rankTwoContent_aux`, `rankTwoContent_dvd_entry_aux`, `Matrix.rankTwoContent` (HermiteNormalForm)]
- **Used by**: `rankTwoContent_mul_sl`
- **Visibility**: private
- **Lines**: 248–258, 10-line proof
- **Notes**: none

### `theorem rankTwoContent_mul_sl` (private)
- **Type**: `(A) (U : SL(2, ℤ)) : (A * U.1).rankTwoContent = A.rankTwoContent`
- **What**: The content of a 2×2 integer matrix is invariant under right multiplication by `SL₂(ℤ)` — primitivity is a coset invariant.
- **How**: Antisymmetry of divisibility (`Nat.dvd_antisymm`): both directions come from `rankTwoContent_dvd_mul_right_aux`, the reverse one after cancelling `U` by `U⁻¹` via `Matrix.SpecialLinearGroup.coe_mul`.
- **Hypotheses**: none.
- **Uses from project**: [`rankTwoContent_dvd_mul_right_aux`, `Matrix.rankTwoContent` (HermiteNormalForm)]
- **Used by**: `exists_coxMatrix_reduction`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 260–269, 9-line proof
- **Notes**: none

### `def slStar` (private)
- **Type**: `(γ : SL(2, ℤ)) : SL(2, ℤ)`
- **What**: The star involution lifted to `SL₂(ℤ)`: since star preserves the determinant, `matrixStar γ` is again in `SL₂(ℤ)`.
- **How**: Subtype constructor with `matrixStar_det` and `γ.prop`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`, `matrixStar_det`]
- **Used by**: `coe_slStar`, `coxRepresentative_normalization`, `coxRepresentative_surjective`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 271–272
- **Notes**: none

### `theorem coe_slStar` (private)
- **Type**: `(γ : SL(2, ℤ)) : (slStar γ).1 = matrixStar γ.1`
- **What**: The underlying matrix of `slStar γ` is `matrixStar γ`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`slStar`, `matrixStar`]
- **Used by**: `coxRepresentative_normalization`, `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 274–275, rfl proof
- **Notes**: @[simp] (private simp lemma)

### `theorem reduced_eq_of_eq_add_mul_aux` (private)
- **Type**: `{d r r' q : ℤ} (hr : r ∈ Set.Ico 0 d) (hr' : r' ∈ Set.Ico 0 d) (e : d * q + r = r') : r = r'`
- **What**: Two residues in `[0, d)` differing by a multiple of `d` are equal — the uniqueness of the reduced representative mod `d`.
- **How**: Both equal their residue class mod `d`: `Int.emod_eq_of_lt` on each side and `Int.add_emod` to kill the `d·q` term.
- **Hypotheses**: `0 ≤ r, r' < d`; `d·q + r = r'`.
- **Uses from project**: []
- **Used by**: `columnHNF_eq_of_mul`
- **Visibility**: private
- **Lines**: 277–283, 5-line proof
- **Notes**: none

### `theorem columnHNF_eq_of_mul` (private)
- **Type**: `{A B U} (hA : A.IsColumnHermiteNormalForm) (hB : B.IsColumnHermiteNormalForm) (hU : IsUnit U.det) (hmul : A * U = B) : A = B`
- **What**: Uniqueness of column Hermite normal form in the 2×2 case: two HNF matrices in the same right `GL₂(ℤ)`-orbit are equal. This is the heart of the well-definedness of the Cox representative.
- **How**: Standard HNF uniqueness argument. From `A·U = B` and `B·U⁻¹ = A` with zero below-diagonal entries (`IsColumnHermiteNormalForm.belowDiagonal_eq_zero`), forces `U 1 0 = 0`; mutual divisibility of positive diagonal entries (`Int.le_of_dvd` both ways using `IsColumnHermiteNormalForm.diagonal_pos`) gives `A 1 1 = B 1 1` and `A 0 0 = B 0 0`, whence `U 1 1 = 1`; finally the reduced off-diagonal entries (`IsColumnHermiteNormalForm.reduced`) agree by `reduced_eq_of_eq_add_mul_aux`.
- **Hypotheses**: both matrices in column HNF, `U` invertible over ℤ, `A·U = B`.
- **Uses from project**: [`reduced_eq_of_eq_add_mul_aux`, `Matrix.IsColumnHermiteNormalForm` and its fields `belowDiagonal_eq_zero`, `diagonal_pos`, `reduced` (HermiteNormalForm)]
- **Used by**: `coxMatrix_reduction_unique`
- **Visibility**: private
- **Lines**: 285–345, 61-line proof
- **Notes**: proof >30 lines (61)

### `theorem CoxMatrix.inclusionMatrix_injective`
- **Type**: `{m : ℕ+} : Function.Injective (CoxMatrix.inclusionMatrix (m := m))`
- **What**: A Cox representative is determined by its sublattice inclusion matrix: distinct elements of `C(m)` have distinct inclusion matrices.
- **How**: Reads off `d`, `b`, `a` from the matrix entries via `congrFun` and `Int.ofNat_inj`, then structure eta with `cases`/`simp_all` (proof fields are propositional).
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix.inclusionMatrix`]
- **Used by**: `coxMatrix_reduction_unique`
- **Visibility**: public
- **Lines**: 348–358, 11-line proof
- **Notes**: none

### `theorem rightRel_of_coxInput_eq_mul` (private)
- **Type**: `(m γ δ U) (h : coxInput m δ = coxInput m γ * U.1) : QuotientGroup.rightRel (Gamma0 m) γ δ`
- **What**: If the Cox inputs of `γ` and `δ` differ by right multiplication by some `U ∈ SL₂(ℤ)`, then `γ` and `δ` lie in the same right coset of `Γ₀(m)`, i.e. `δγ⁻¹ ∈ Γ₀(m)`.
- **How**: Reduces membership to `(δγ⁻¹)₁₀ ≡ 0 (mod m)` via `CongruenceSubgroup.Gamma0_mem`; computes `(δγ⁻¹)₁₀ = m·U₁₀` by expanding `Matrix.SpecialLinearGroup.SL2_inv_expl` and eliminating with `linear_combination` against the entry equations and `det γ = 1`.
- **Hypotheses**: `coxInput m δ = coxInput m γ · U`.
- **Uses from project**: [`coxInput`, `coxInput_eq`]
- **Used by**: `rightRel_iff_coxRepresentative_eq`
- **Visibility**: private
- **Lines**: 360–379, 19-line proof
- **Notes**: none

### `theorem exists_coxInput_eq_mul_of_rightRel` (private)
- **Type**: `(m γ δ) (hrel : rightRel (Gamma0 m) γ δ) : ∃ U : SL(2, ℤ), coxInput m δ = coxInput m γ * U.1`
- **What**: Converse direction: right-coset-equivalent `γ, δ` have Cox inputs related by right `SL₂(ℤ)`-multiplication. Together with the previous lemma, the `SL₂(ℤ)`-column-orbit of `coxInput` is a complete right-coset invariant.
- **How**: Writes `h = δγ⁻¹ ∈ Γ₀(m)`, extracts `m ∣ h₁₀` via `CongruenceSubgroup.Gamma0_mem` and `ZMod.intCast_zmod_eq_zero_iff_dvd`, and constructs the explicit conjugated matrix `U = [[h₁₁, m·h₀₁],[k, h₀₀]]` (where `h₁₀ = m·k`) whose determinant is 1 by `linear_combination` against `det h = 1`; the product identity is checked entrywise.
- **Hypotheses**: `γ`, `δ` in the same right coset of `Γ₀(m)`.
- **Uses from project**: [`coxInput`, `coxInput_eq`]
- **Used by**: `rightRel_iff_coxRepresentative_eq`
- **Visibility**: private
- **Lines**: 381–401, 20-line proof
- **Notes**: none

### `theorem exists_coxMatrix_reduction` (private)
- **Type**: `(m γ) : ∃ (σ : CoxMatrix m) (U : SL(2, ℤ)), coxInput m γ * U.1 = σ.inclusionMatrix`
- **What**: Existence of the Cox representative: every Cox input matrix can be brought to the inclusion matrix of some `σ ∈ C(m)` by column operations in `SL₂(ℤ)`. This is the existence half of Cox Lemma 11.11.
- **How**: Applies the project's HNF existence theorem `Matrix.exists_right_mul_isColumnHermiteNormalForm`; the reducing unit matrix has determinant `+1` because the HNF has positive determinant (product of positive diagonal entries) while `det(coxInput) = m > 0`. The HNF entries `(H₁₁, H₀₁, H₀₀)` are repackaged as a `CoxMatrix` via `natAbs`: determinant from `det H = m`, reducedness from `IsColumnHermiteNormalForm.reduced`, primitivity from `rankTwoContent_mul_sl` and `coxInput_content_eq_one`.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `coxInput_det`, `coxInput_content_eq_one`, `rankTwoContent_mul_sl`, `CoxMatrix`, `CoxMatrix.inclusionMatrix`, `Matrix.exists_right_mul_isColumnHermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm.belowDiagonal_eq_zero`, `.diagonal_pos`, `.reduced`, `Matrix.rankTwoContent` (all HermiteNormalForm)]
- **Used by**: `coxRepresentative`, `coxReductionMatrix`, `coxReduction_spec`
- **Visibility**: private
- **Lines**: 403–461, 59-line proof
- **Notes**: proof >30 lines (59); substantial overlap with `exists_coxMatrix_of_isColumnHermiteNormalForm_aux` (lines 904–938) — the σ-construction block is duplicated

### `theorem coxMatrix_reduction_unique` (private)
- **Type**: `(m γ) {σ τ : CoxMatrix m} {U V : SL(2, ℤ)} (hσ : coxInput m γ * U.1 = σ.inclusionMatrix) (hτ : ... = τ.inclusionMatrix) : σ = τ`
- **What**: Uniqueness of the Cox representative of a given `γ`: two HNF reductions of the same Cox input yield the same element of `C(m)`.
- **How**: `σ.inclusionMatrix · (U⁻¹V) = τ.inclusionMatrix`, so by HNF uniqueness (`columnHNF_eq_of_mul`, with both sides in HNF by `inclusionMatrix_isColumnHermiteNormalForm`) the inclusion matrices agree, and `inclusionMatrix_injective` finishes.
- **Hypotheses**: both `U`, `V` reduce `coxInput m γ` to inclusion matrices.
- **Uses from project**: [`coxInput`, `CoxMatrix.inclusionMatrix`, `columnHNF_eq_of_mul`, `CoxMatrix.inclusionMatrix_isColumnHermiteNormalForm`, `CoxMatrix.inclusionMatrix_injective`]
- **Used by**: `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_one`, `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 463–480, 17-line proof
- **Notes**: none

### `def coxRepresentative` (private)
- **Type**: `(m : ℕ+) (γ : SL(2, ℤ)) : CoxMatrix m`
- **What**: The Cox representative of `γ`: the unique `σ ∈ C(m)` whose inclusion matrix is the column HNF of `coxInput m γ`.
- **How**: Choice from `exists_coxMatrix_reduction`.
- **Hypotheses**: none.
- **Uses from project**: [`exists_coxMatrix_reduction`, `CoxMatrix`]
- **Used by**: `coxReductionMatrix` (spec), `coxReduction_spec`, `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_normalization`, `coxRepresentative_one`, `coxRepresentative_surjective`, `rightCosetToCoxMatrix`, `coxMatrixEquivRightCosets_coxRepresentative`, `rightCosetEval_equiv`
- **Visibility**: private
- **Lines**: 482–483
- **Notes**: noncomputable (uses choice)

### `def coxReductionMatrix` (private)
- **Type**: `(m : ℕ+) (γ : SL(2, ℤ)) : SL(2, ℤ)`
- **What**: The chosen unimodular column-operation matrix `U` witnessing the HNF reduction of `coxInput m γ`.
- **How**: Choice from the inner existential of `exists_coxMatrix_reduction`.
- **Hypotheses**: none.
- **Uses from project**: [`exists_coxMatrix_reduction`]
- **Used by**: `coxReduction_spec`, `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_normalization`
- **Visibility**: private
- **Lines**: 485–486
- **Notes**: noncomputable (uses choice)

### `theorem coxReduction_spec` (private)
- **Type**: `(m γ) : coxInput m γ * (coxReductionMatrix m γ).1 = (coxRepresentative m γ).inclusionMatrix`
- **What**: The defining property of the two choices: the reduction matrix carries the Cox input to the representative's inclusion matrix.
- **How**: `choose_spec.choose_spec` of `exists_coxMatrix_reduction`.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `coxReductionMatrix`, `coxRepresentative`, `CoxMatrix.inclusionMatrix`, `exists_coxMatrix_reduction`]
- **Used by**: `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_normalization`, `coxRepresentative_one`, `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 488–491, term proof
- **Notes**: none

### `theorem rightRel_iff_coxRepresentative_eq` (private)
- **Type**: `(m γ δ) : rightRel (Gamma0 m) γ δ ↔ coxRepresentative m γ = coxRepresentative m δ`
- **What**: The Cox representative is a complete invariant of the right coset: `γ` and `δ` are right-`Γ₀(m)`-equivalent iff they reduce to the same element of `C(m)`. This is the crux of the bijection `C(m) ≃ Γ₀(m)\SL₂(ℤ)`.
- **How**: Forward: `exists_coxInput_eq_mul_of_rightRel` gives `coxInput δ = coxInput γ · W`, so composing with δ's reduction reduces γ's input to δ's representative; conclude by `coxMatrix_reduction_unique`. Backward: equal representatives give `coxInput δ · Vδ = coxInput γ · Vγ` (both `coxReduction_spec`s), hence `coxInput δ = coxInput γ · (Vγ Vδ⁻¹)`, and `rightRel_of_coxInput_eq_mul` concludes.
- **Hypotheses**: none.
- **Uses from project**: [`coxRepresentative`, `coxReductionMatrix`, `coxReduction_spec`, `coxMatrix_reduction_unique`, `exists_coxInput_eq_mul_of_rightRel`, `rightRel_of_coxInput_eq_mul`, `coxInput`]
- **Used by**: `rightCosetToCoxMatrix`, `rightCosetToCoxMatrix_bijective`
- **Visibility**: private
- **Lines**: 493–526, 34-line proof
- **Notes**: proof >30 lines (34)

### `theorem matrixStar_inclusionMatrix` (private)
- **Type**: `{m} (σ : CoxMatrix m) : matrixStar σ.inclusionMatrix = σ.mobiusMatrix`
- **What**: Star carries the inclusion matrix back to the Möbius matrix (inverse direction of `matrixStar_mobiusMatrix`).
- **How**: Rewrite by `matrixStar_mobiusMatrix` and the involutivity `matrixStar_involutive`.
- **Hypotheses**: none.
- **Uses from project**: [`matrixStar`, `matrixStar_mobiusMatrix`, `matrixStar_involutive`, `CoxMatrix.inclusionMatrix`, `CoxMatrix.mobiusMatrix`]
- **Used by**: `coxRepresentative_normalization`, `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 528–530, 2-line proof
- **Notes**: none

### `theorem coxRepresentative_normalization` (private)
- **Type**: `(m γ) : ∃ δ : SL(2, ℤ), (δ⁻¹).1 * !![m*γ00, m*γ01; γ10, γ11] = (coxRepresentative m γ).mobiusMatrix`
- **What**: Left-normalization form of the reduction: the scaled matrix `diag(m,1)·γ` equals `δ · σ.mobiusMatrix` for some `δ ∈ SL₂(ℤ)` and `σ` the Cox representative — i.e. Cox's decomposition `mγ = δσ` used to compute `j(mγτ)`.
- **How**: Applies `matrixStar` to `coxReduction_spec` and uses the anti-homomorphism property `matrixStar_mul` together with `matrixStar_inclusionMatrix` and involutivity to convert the right-multiplication HNF identity into left multiplication by `(slStar U)⁻¹`.
- **Hypotheses**: none.
- **Uses from project**: [`coxReductionMatrix`, `coxReduction_spec`, `coxRepresentative`, `slStar`, `coe_slStar`, `matrixStar`, `matrixStar_mul`, `matrixStar_inclusionMatrix`, `matrixStar_involutive`, `coxInput`, `determinantScale`, `CoxMatrix.mobiusMatrix`]
- **Used by**: `rightCosetEval_equiv`
- **Visibility**: private
- **Lines**: 532–549, 17-line proof
- **Notes**: none

### `theorem coxInput_one` (private)
- **Type**: `(m : ℕ+) : coxInput m (1 : SL(2, ℤ)) = (sigmaZero m).inclusionMatrix`
- **What**: The Cox input of the identity is already in HNF and equals the inclusion matrix `[[1,0],[0,m]]` of `σ₀`.
- **How**: Entrywise check from `coxInput_eq` and the definition of `sigmaZero`.
- **Hypotheses**: none.
- **Uses from project**: [`coxInput`, `coxInput_eq`, `sigmaZero`, `CoxMatrix.inclusionMatrix`]
- **Used by**: `coxRepresentative_one`
- **Visibility**: private
- **Lines**: 551–555, 4-line proof
- **Notes**: none

### `theorem coxRepresentative_one` (private)
- **Type**: `(m : ℕ+) : coxRepresentative m 1 = sigmaZero m`
- **What**: The Cox representative of the identity coset is the distinguished matrix `σ₀ = diag(m,1)`.
- **How**: Uniqueness of reduction (`coxMatrix_reduction_unique` with `V = 1`) against the trivial reduction `coxInput_one`.
- **Hypotheses**: none.
- **Uses from project**: [`coxRepresentative`, `sigmaZero`, `coxMatrix_reduction_unique`, `coxReduction_spec`, `coxInput_one`]
- **Used by**: `coxMatrixEquivRightCosets_sigmaZero`
- **Visibility**: private
- **Lines**: 557–562, 5-line proof
- **Notes**: none

### `theorem exists_coprime_add_mul_of_gcd_gcd_eq_one` (private)
- **Type**: `(a b d : ℕ) (ha : a ≠ 0) (h : Nat.gcd (Nat.gcd a b) d = 1) : ∃ x : ℕ, Nat.Coprime a (b + x * d)`
- **What**: Number-theoretic key to the Smith normalization: if `gcd(a,b,d) = 1` then some shift `b + xd` of `b` by a multiple of `d` is coprime to `a`. (A constructive stand-in for Dirichlet-style coprime selection.)
- **How**: Takes `x` to be the product of those prime factors of `a` not dividing `b`. For a prime `p ∣ a` dividing `b + xd`: if `p ∣ b` then `p ∤ x` (by `Nat.Prime.dvd_finsetProd_iff` and construction) forces `p ∣ d`, contradicting `gcd(a,b,d)=1`; if `p ∤ b` then `p ∣ x` gives `p ∣ b`, contradiction. Uses `Nat.coprime_of_dvd`, `Nat.mem_primeFactors`, `Finset.dvd_prod_of_mem`.
- **Hypotheses**: `a ≠ 0`, `gcd(gcd(a,b),d) = 1`.
- **Uses from project**: []
- **Used by**: `coxMatrix_smith_normalization`
- **Visibility**: private
- **Lines**: 564–587, 23-line proof
- **Notes**: none

### `theorem coxMatrix_smith_normalization` (private)
- **Type**: `{m} (σ : CoxMatrix m) : ∃ L R : SL(2, ℤ), (L⁻¹).1 * σ.inclusionMatrix * R.1 = determinantScaleDual m`
- **What**: Smith normal form for Cox inclusion matrices: every `σ.inclusionMatrix` is `SL₂(ℤ)`-equivalent (two-sided) to `diag(1, m)`. Reflects that the sublattice quotient is cyclic of order `m` exactly when the matrix is primitive.
- **How**: Uses `exists_coprime_add_mul_of_gcd_gcd_eq_one` to make the first column entries `(b + xd, a)` coprime after a column move `R₁ = [[x,−1],[1,0]]`; mathlib's `IsCoprime.exists_SL2_col` produces `L` with that column, so `N = L⁻¹·M` has `N₀₀ = 1`, `N₁₀ = 0` (via `SL2_inv_expl` and `linear_combination` with `det L = 1`); `det N = m` (from `inclusionMatrix_det`) forces `N₁₁ = m`, and a final column shear `R₂ = [[1, −N₀₁],[0,1]]` clears the last off-diagonal entry.
- **Hypotheses**: none (primitivity comes from the `CoxMatrix` structure).
- **Uses from project**: [`exists_coprime_add_mul_of_gcd_gcd_eq_one`, `CoxMatrix.inclusionMatrix`, `CoxMatrix.inclusionMatrix_det`, `determinantScaleDual`, `CoxMatrix.primitive`, `CoxMatrix.a_pos`]
- **Used by**: `coxRepresentative_surjective`
- **Visibility**: private
- **Lines**: 589–642, 54-line proof
- **Notes**: proof >30 lines (54)

### `theorem coxRepresentative_surjective` (private)
- **Type**: `(m : ℕ+) : Function.Surjective (coxRepresentative m)`
- **What**: Every element of `C(m)` is the Cox representative of some `γ ∈ SL₂(ℤ)` — surjectivity half of the bijection with right cosets.
- **How**: Given `σ`, the Smith normalization `L⁻¹ · σ.inclusionMatrix · R = diag(1,m)` rearranges to `coxInput m (slStar L) · R⁻¹ = σ.inclusionMatrix` (using `matrixStar_mul`, `matrixStar_involutive`, `matrixStar_determinantScale` to unstar), so `γ = slStar L` reduces to `σ` by `coxMatrix_reduction_unique`.
- **Hypotheses**: none.
- **Uses from project**: [`coxMatrix_smith_normalization`, `slStar`, `coe_slStar`, `coxMatrix_reduction_unique`, `coxReduction_spec`, `coxInput`, `matrixStar_mul`, `matrixStar_involutive`, `matrixStar_determinantScale`, `determinantScaleDual`, `CoxMatrix.inclusionMatrix`, `coxRepresentative`]
- **Used by**: `rightCosetToCoxMatrix_bijective`, `rightCosetEval_equiv`
- **Visibility**: private
- **Lines**: 644–664, 21-line proof
- **Notes**: none

### `def rightCosetToCoxMatrix` (private)
- **Type**: `(m : ℕ+) : Gamma0RightCosets m → CoxMatrix m`
- **What**: The map from right cosets to Cox representatives, well defined by the coset invariance of the representative.
- **How**: `Quotient.lift` of `coxRepresentative`, with well-definedness from the forward direction of `rightRel_iff_coxRepresentative_eq`.
- **Hypotheses**: none.
- **Uses from project**: [`Gamma0RightCosets`, `coxRepresentative`, `rightRel_iff_coxRepresentative_eq`]
- **Used by**: `rightCosetToCoxMatrix_bijective`, `coxMatrixEquivRightCosets`, `coxMatrixEquivRightCosets_coxRepresentative`
- **Visibility**: private
- **Lines**: 666–669
- **Notes**: noncomputable

### `theorem rightCosetToCoxMatrix_bijective` (private)
- **Type**: `(m : ℕ+) : Function.Bijective (rightCosetToCoxMatrix m)`
- **What**: The coset-to-representative map is a bijection: injective because equal representatives force coset equality, surjective because every `σ` is some `γ`'s representative.
- **How**: Injectivity from the backward direction of `rightRel_iff_coxRepresentative_eq` after choosing representatives with `Quotient.exists_rep`; surjectivity from `coxRepresentative_surjective`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetToCoxMatrix`, `rightRel_iff_coxRepresentative_eq`, `coxRepresentative_surjective`]
- **Used by**: `coxMatrixEquivRightCosets`, `coxMatrixEquivRightCosets_coxRepresentative`
- **Visibility**: private
- **Lines**: 671–681, 10-line proof
- **Notes**: none

### `def coxMatrixEquivRightCosets`
- **Type**: `(m : ℕ+) : CoxMatrix m ≃ Gamma0RightCosets m`
- **What**: Cox Lemma 11.11: the finite set `C(m)` of primitive upper-triangular determinant-`m` matrices is in bijection with the right cosets of `Γ₀(m)` in `SL₂(ℤ)`.
- **How**: Inverse of `Equiv.ofBijective` applied to `rightCosetToCoxMatrix` with `rightCosetToCoxMatrix_bijective` — i.e. the rank-two HNF classification packaged as an equivalence.
- **Hypotheses**: none.
- **Uses from project**: [`CoxMatrix`, `Gamma0RightCosets`, `rightCosetToCoxMatrix`, `rightCosetToCoxMatrix_bijective`]
- **Used by**: `coxMatrixEquivRightCosets_coxRepresentative`, `coxMatrixEquivRightCosets_sigmaZero`, `rightCosetEval_equiv`, `rightCosetTranslate_sigmaZero`
- **Visibility**: public
- **Lines**: 685–688
- **Notes**: noncomputable; this is the file's headline classification result

### `theorem coxMatrixEquivRightCosets_coxRepresentative` (private)
- **Type**: `(m γ) : coxMatrixEquivRightCosets m (coxRepresentative m γ) = Quotient.mk'' γ`
- **What**: The equivalence sends the representative of `γ` to the coset of `γ` — the compatibility of the equivalence with the underlying reduction map.
- **How**: `Equiv.symm_apply_eq` reduces to `rightCosetToCoxMatrix (mk γ) = coxRepresentative m γ`, which is `rfl` by the `Quotient.lift` computation rule.
- **Hypotheses**: none.
- **Uses from project**: [`coxMatrixEquivRightCosets`, `coxRepresentative`, `rightCosetToCoxMatrix`, `rightCosetToCoxMatrix_bijective`]
- **Used by**: `coxMatrixEquivRightCosets_sigmaZero`, `rightCosetEval_equiv`
- **Visibility**: private
- **Lines**: 690–696, 4-line proof
- **Notes**: @[simp] (private simp lemma)

### `def rightCosetTranslate`
- **Type**: `(m : ℕ+) {f : ℍ → ℂ} (hf : IsGamma0ModularFunction m f) (c : Gamma0RightCosets m) (τ : ℍ) : ℂ`
- **What**: The translate `f|_c(τ) = f(γ·τ)` of a `Γ₀(m)`-modular function by a right coset `c = Γ₀(m)γ`; the `Γ₀(m)`-invariance of `f` (weight 0) makes this independent of the representative. This is the coset action underlying the modular polynomial's conjugate functions.
- **How**: `Quotient.liftOn`; for well-definedness, if `δγ⁻¹ = g₀ ∈ Γ₀(m)` then `f(δτ) = f(g₀·(γτ)) = f(γτ)` by the slash-invariance component of `IsGamma0ModularFunction` (unpacked via `ModularForm.SL_slash_apply` at weight 0) and `mul_smul`.
- **Hypotheses**: `f` is a `Γ₀(m)`-modular function (meromorphic, weight-0 invariant, meromorphic at cusps).
- **Uses from project**: [`Gamma0RightCosets`, `IsGamma0ModularFunction` (ModularFunction)]
- **Used by**: `rightCosetTranslate_mk`, `rightCosetEval`, `rightCosetTranslate_smul`, `rightCosetTranslate_sigmaZero`
- **Visibility**: public
- **Lines**: 700–715, 16-line well-definedness proof
- **Notes**: noncomputable

### `theorem rightCosetTranslate_mk`
- **Type**: `(m) (hf) (γ : SL(2, ℤ)) (τ : ℍ) : rightCosetTranslate m hf (Quotient.mk'' γ) τ = f (γ • τ)`
- **What**: Computation rule: the translate at the coset of `γ` evaluates `f` at `γ·τ`.
- **How**: `rfl` — `Quotient.liftOn` computation.
- **Hypotheses**: `f` a `Γ₀(m)`-modular function.
- **Uses from project**: [`rightCosetTranslate`, `IsGamma0ModularFunction` (ModularFunction)]
- **Used by**: `rightCosetTranslate_sigmaZero`
- **Visibility**: public
- **Lines**: 717–721, rfl proof
- **Notes**: @[simp]

### `def rightCosetEval`
- **Type**: `(m : ℕ+) (c : Gamma0RightCosets m) (τ : ℍ) : ℂ`
- **What**: The conjugate `j(mγτ)` attached to a right coset: the coset translate of the level-`m` function `levelJ m = j(m·)`. These are precisely the conjugate roots of the modular equation `Φ_m(·, j)`.
- **How**: Specializes `rightCosetTranslate` at `levelJ m`, using the project theorem `levelJ_isGamma0ModularFunction` for the required modularity.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetTranslate`, `levelJ` (ModularFunction), `levelJ_isGamma0ModularFunction` (ModularFunction), `Gamma0RightCosets`]
- **Used by**: `rightCosetEval_mk`, `rightCosetEval_smul`, `rightCosetEval_equiv`
- **Visibility**: public
- **Lines**: 723–725
- **Notes**: noncomputable

### `theorem rightCosetEval_mk`
- **Type**: `(m) (γ) (τ) : rightCosetEval m (Quotient.mk'' γ) τ = levelJ m (γ • τ)`
- **What**: Computation rule: the coset conjugate at `Γ₀(m)γ` is `j(m·(γτ))`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetEval`, `levelJ` (ModularFunction)]
- **Used by**: `rightCosetEval_equiv`
- **Visibility**: public
- **Lines**: 727–730, rfl proof
- **Notes**: @[simp]

### `def rightCosetMul`
- **Type**: `(m : ℕ+) (δ : SL(2, ℤ)) : Gamma0RightCosets m ≃ Gamma0RightCosets m`
- **What**: Right multiplication by `δ ∈ SL₂(ℤ)` permutes the right cosets of `Γ₀(m)`: `Γ₀(m)γ ↦ Γ₀(m)γδ`. This is the (right) action of `SL₂(ℤ)` on the coset space, which will permute the conjugate functions.
- **How**: `Quotient.map'` for `·δ` and `·δ⁻¹`; well-definedness because `(γ'δ)(γδ)⁻¹ = γ'γ⁻¹` (via `QuotientGroup.rightRel_apply` and `mul_assoc`), inverse laws by `Quotient.inductionOn` and cancellation.
- **Hypotheses**: none.
- **Uses from project**: [`Gamma0RightCosets`]
- **Used by**: `rightCosetMul_mk`, `exists_rightCosetMul_baseRightCoset_eq`, `rightCosetTranslate_smul`, `rightCosetEval_smul`
- **Visibility**: public
- **Lines**: 733–760 (28 lines)
- **Notes**: none

### `theorem rightCosetMul_mk`
- **Type**: `(m) (δ γ) : rightCosetMul m δ (Quotient.mk'' γ) = Quotient.mk'' (γ * δ)`
- **What**: Computation rule: right multiplication sends the class of `γ` to the class of `γδ`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetMul`]
- **Used by**: `exists_rightCosetMul_baseRightCoset_eq` (via `simp`)
- **Visibility**: public
- **Lines**: 763–766, rfl proof
- **Notes**: @[simp]

### `def baseRightCoset`
- **Type**: `(m : ℕ+) : Gamma0RightCosets m`
- **What**: The identity right coset `Γ₀(m)·1`.
- **How**: `Quotient.mk''` of the identity.
- **Hypotheses**: none.
- **Uses from project**: [`Gamma0RightCosets`]
- **Used by**: `exists_rightCosetMul_baseRightCoset_eq`
- **Visibility**: public
- **Lines**: 768–770
- **Notes**: none

### `theorem exists_rightCosetMul_baseRightCoset_eq`
- **Type**: `(m) (c : Gamma0RightCosets m) : ∃ δ : SL(2, ℤ), rightCosetMul m δ (baseRightCoset m) = c`
- **What**: The right-multiplication action is transitive from the identity coset: every coset is `(Γ₀(m)·1)·δ` for some `δ`.
- **How**: Pick a representative `δ` with `Quotient.exists_rep`; then `rightCosetMul m δ (mk 1) = mk (1·δ) = mk δ` by `simp` (using `rightCosetMul_mk`).
- **Hypotheses**: none.
- **Uses from project**: [`Gamma0RightCosets`, `rightCosetMul`, `baseRightCoset`, `rightCosetMul_mk` (via simp)]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 773–776, 3-line proof
- **Notes**: none

### `theorem rightCosetTranslate_smul`
- **Type**: `(m) (hf : IsGamma0ModularFunction m f) (δ : SL(2, ℤ)) (c) (τ) : rightCosetTranslate m hf c (δ • τ) = rightCosetTranslate m hf (rightCosetMul m δ c) τ`
- **What**: Equivariance: precomposing a coset translate with the Möbius action of `δ` equals translating by the right-multiplied coset. This is how `SL₂(ℤ)` permutes the conjugate functions `{f(γτ)}`.
- **How**: `Quotient.inductionOn` reduces to `f(γ·(δτ)) = f((γδ)·τ)`, which is `mul_smul`.
- **Hypotheses**: `f` a `Γ₀(m)`-modular function.
- **Uses from project**: [`rightCosetTranslate`, `rightCosetMul`, `IsGamma0ModularFunction` (ModularFunction), `Gamma0RightCosets`]
- **Used by**: `rightCosetEval_smul`
- **Visibility**: public
- **Lines**: 780–788, 5-line proof
- **Notes**: none

### `theorem rightCosetEval_smul`
- **Type**: `(m) (δ) (c) (τ) : rightCosetEval m c (δ • τ) = rightCosetEval m (rightCosetMul m δ c) τ`
- **What**: The `j(mγτ)` conjugates are permuted by the `SL₂(ℤ)`-action on τ — specialization of the previous equivariance to `levelJ`. This underlies the invariance of the modular polynomial's coefficients.
- **How**: Direct application of `rightCosetTranslate_smul` with `levelJ_isGamma0ModularFunction`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetEval`, `rightCosetTranslate_smul`, `rightCosetMul`, `levelJ_isGamma0ModularFunction` (ModularFunction)]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 792–795, 2-line proof
- **Notes**: none

### `lemma complex_mobius_scale_eq_affine` (private)
- **Type**: `{n p q u v a b c d g r s z : ℂ} (hD : c*z + d ≠ 0) (hs : s ≠ 0) (h00 : p*(n*a) + q*c = g) (h01 : p*(n*b) + q*d = r) (h10 : u*(n*a) + v*c = 0) (h11 : u*(n*b) + v*d = s) : (p*(n*((a*z+b)/(c*z+d))) + q) / (u*(n*((a*z+b)/(c*z+d))) + v) = r/s + g/s * z`
- **What**: Pure complex-arithmetic identity: composing a Möbius map `[[p,q],[u,v]]` with the scaled Möbius map `n·(az+b)/(cz+d)` yields an affine map `(g z + r)/s` when the matrix product `[[p,q],[u,v]]·[[na, nb],[c, d]]` is upper triangular `[[g, r],[0, s]]`. This is the computational engine turning the decomposition `mγ = δσ` into `j(mγτ) = j(σ·τ)`.
- **How**: Clears denominators (`field_simp` against `cz + d ≠ 0`, `s ≠ 0`) and verifies numerator and denominator identities by `linear_combination` of the four entry equations weighted by `z`.
- **Hypotheses**: denominator `cz+d ≠ 0`, `s ≠ 0`, four entry equations expressing upper-triangularity of the product.
- **Uses from project**: []
- **Used by**: `levelJ_smul_eq_j_act_of_normalization`
- **Visibility**: private
- **Lines**: 797–815, 19-line proof
- **Notes**: none

### `theorem levelJ_smul_eq_j_act_of_normalization` (private)
- **Type**: `(m) (σ : CoxMatrix m) (γ δ : SL(2, ℤ)) (hmat : (δ⁻¹).1 * !![m*γ00, m*γ01; γ10, γ11] = σ.mobiusMatrix) (τ : ℍ) : levelJ m (γ • τ) = j (σ.act τ)`
- **What**: If `diag(m,1)·γ = δ·σ.mobiusMatrix` (Cox's normalization `mγ = δσ`), then `j(m·(γτ)) = j(σ·τ)`: the coset conjugate of `levelJ` is `j` composed with the Cox action.
- **How**: Sets `z_N = m·(γτ) ∈ ℍ` and uses `SL₂(ℤ)`-invariance of `j` (project lemma `j_modularGroup_smul`) to replace `j(z_N)` by `j(δ⁻¹·z_N)`; then `complex_mobius_scale_eq_affine` (fed the four entry equations of `hmat`, denominators nonvanishing by `UpperHalfPlane.denom_ne_zero` and `σ.d ≠ 0`) identifies `δ⁻¹·(m·γτ)` with `(aτ+b)/d = σ.act τ` via `coe_act`.
- **Hypotheses**: the matrix normalization identity `hmat`.
- **Uses from project**: [`levelJ` (ModularFunction), `j` (jfunction), `j_modularGroup_smul` (jfunction), `CoxMatrix.act`, `CoxMatrix.coe_act`, `CoxMatrix.mobiusMatrix`, `CoxMatrix.d_pos`, `complex_mobius_scale_eq_affine`]
- **Used by**: `rightCosetEval_equiv`
- **Visibility**: private
- **Lines**: 817–859, 43-line proof
- **Notes**: proof >30 lines (43)

### `theorem coxMatrixEquivRightCosets_sigmaZero` (private)
- **Type**: `(m : ℕ+) : coxMatrixEquivRightCosets m (sigmaZero m) = Quotient.mk'' 1`
- **What**: Under the Cox bijection, the distinguished matrix `σ₀` corresponds to the identity coset.
- **How**: Rewrites `σ₀ = coxRepresentative m 1` (`coxRepresentative_one`) and applies the compatibility lemma `coxMatrixEquivRightCosets_coxRepresentative`.
- **Hypotheses**: none.
- **Uses from project**: [`coxMatrixEquivRightCosets`, `sigmaZero`, `coxRepresentative_one`, `coxMatrixEquivRightCosets_coxRepresentative`]
- **Used by**: `rightCosetTranslate_sigmaZero`
- **Visibility**: private
- **Lines**: 861–864, 2-line proof
- **Notes**: none

### `theorem rightCosetEval_equiv`
- **Type**: `(m : ℕ+) (σ : CoxMatrix m) (τ : ℍ) : rightCosetEval m (coxMatrixEquivRightCosets m σ) τ = j (σ.act τ)`
- **What**: Cox equation (11.12): through the HNF/right-coset equivalence, the conjugate `j(mγτ)` attached to the coset of `σ` equals `j((aτ+b)/d)`. This identifies the abstract coset conjugates with the classical explicit conjugate functions used to build the modular polynomial `Φ_m`.
- **How**: Writes `σ = coxRepresentative m γ` by surjectivity (`coxRepresentative_surjective`), computes the equivalence on representatives (`coxMatrixEquivRightCosets_coxRepresentative`, `rightCosetEval_mk`), obtains Cox's normalization `mγ = δσ` from `coxRepresentative_normalization`, and concludes with `levelJ_smul_eq_j_act_of_normalization`.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetEval`, `coxMatrixEquivRightCosets`, `coxRepresentative_surjective`, `coxMatrixEquivRightCosets_coxRepresentative`, `rightCosetEval_mk`, `coxRepresentative_normalization`, `levelJ_smul_eq_j_act_of_normalization`, `CoxMatrix.act`, `j` (jfunction)]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 867–872, 6-line proof
- **Notes**: headline theorem of the file (with `coxMatrixEquivRightCosets`)

### `theorem rightCosetTranslate_sigmaZero`
- **Type**: `(m) (hf : IsGamma0ModularFunction m f) (τ) : rightCosetTranslate m hf (coxMatrixEquivRightCosets m (sigmaZero m)) τ = f τ`
- **What**: Translating a modular function by the coset of the distinguished matrix `σ₀` (the identity coset) leaves it unchanged.
- **How**: `coxMatrixEquivRightCosets_sigmaZero` identifies the coset as `mk 1`, then `rightCosetTranslate_mk` and `simp` (`one_smul`).
- **Hypotheses**: `f` a `Γ₀(m)`-modular function.
- **Uses from project**: [`rightCosetTranslate`, `coxMatrixEquivRightCosets`, `sigmaZero`, `coxMatrixEquivRightCosets_sigmaZero`, `rightCosetTranslate_mk`, `IsGamma0ModularFunction` (ModularFunction)]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 876–880, 3-line proof
- **Notes**: none

### `theorem j_act_sigmaZero`
- **Type**: `(m : ℕ+) : (fun τ ↦ j ((sigmaZero m).act τ)) = levelJ m`
- **What**: The Cox action of `σ₀ = diag(m,1)` realizes the level-`m` function: `j(σ₀·τ) = j(mτ) = levelJ m τ`.
- **How**: Pointwise: `σ₀.act τ = (mτ + 0)/1 = mτ` by unfolding `CoxMatrix.act` and `sigmaZero` with `simp`, then `UpperHalfPlane.ext`.
- **Hypotheses**: none.
- **Uses from project**: [`j` (jfunction), `levelJ` (ModularFunction), `sigmaZero`, `CoxMatrix.act`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 882–888, 6-line proof
- **Notes**: none

### `theorem exists_sl_right_mul_isColumnHermiteNormalForm_aux` (private)
- **Type**: `(A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : 0 < A.det) : ∃ U : SL(2, ℤ), (A * U.1).IsColumnHermiteNormalForm`
- **What**: Refinement of the project's HNF existence theorem: for positive determinant, the reducing unimodular matrix can be taken in `SL₂(ℤ)` (determinant `+1`, not just `±1`).
- **How**: From `Matrix.exists_right_mul_isColumnHermiteNormalForm` (HermiteNormalForm) the unit `B` has `det B = ±1`; the HNF product has positive determinant (product of positive diagonal entries via `IsColumnHermiteNormalForm.diagonal_pos`), which together with `det A > 0` rules out `det B = −1` by `Matrix.det_mul` and `omega`.
- **Hypotheses**: `det A > 0`.
- **Uses from project**: [`Matrix.exists_right_mul_isColumnHermiteNormalForm`, `Matrix.IsColumnHermiteNormalForm.belowDiagonal_eq_zero`, `.diagonal_pos` (HermiteNormalForm)]
- **Used by**: `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 889–902, 13-line proof
- **Notes**: none

### `theorem exists_coxMatrix_of_isColumnHermiteNormalForm_aux` (private)
- **Type**: `{m} (H) (hH : H.IsColumnHermiteNormalForm) (hdet : H.det = m) (hcontent : H.rankTwoContent = 1) : ∃ σ : CoxMatrix m, H = σ.inclusionMatrix`
- **What**: A primitive column-HNF matrix of determinant `m` is the inclusion matrix of a Cox representative — the HNF entries directly furnish `(a, b, d)`.
- **How**: Extracts positivity/reducedness from the `IsColumnHermiteNormalForm` fields (`diagonal_pos`, `reduced`, `belowDiagonal_eq_zero`), reads `a·d = m` off `det H = m` (`Matrix.det_fin_two`), primitivity off the content, and verifies the four entries with `Int.ofNat_natAbs_of_nonneg`.
- **Hypotheses**: `H` in column HNF, `det H = m`, content 1.
- **Uses from project**: [`CoxMatrix`, `CoxMatrix.inclusionMatrix`, `Matrix.IsColumnHermiteNormalForm.belowDiagonal_eq_zero`, `.diagonal_pos`, `.reduced`, `Matrix.rankTwoContent` (HermiteNormalForm)]
- **Used by**: `exists_sl2_mul_eq_coxMatrix`
- **Visibility**: private
- **Lines**: 904–938, 35-line proof
- **Notes**: proof >30 lines (35); the σ-construction duplicates lines 434–461 of `exists_coxMatrix_reduction` — that proof could be refactored to use this lemma

### `theorem exists_sl2_mul_eq_coxMatrix`
- **Type**: `{m} (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = m) (hprimitive : Matrix.rankTwoContent M = 1) : ∃ γ : SL(2, ℤ), ∃ σ : CoxMatrix m, γ.1 * M = σ.mobiusMatrix`
- **What**: Report Lemma 5.8: every primitive integer 2×2 matrix of determinant `m` becomes a Cox upper-triangular representative `[[a,b],[0,d]]` after left multiplication by a suitable element of `SL₂(ℤ)`. This is the classical classification of primitive determinant-`m` matrices up to left `SL₂(ℤ)`-equivalence.
- **How**: Applies the star trick: column-HNF-reduce `matrixStar M` on the right in `SL₂(ℤ)` (`exists_sl_right_mul_isColumnHermiteNormalForm_aux`; determinant and content are preserved by `matrixStar_det`, star-symmetry of content, and `rankTwoContent_mul_sl`), recognize the HNF as an inclusion matrix (`exists_coxMatrix_of_isColumnHermiteNormalForm_aux`), and un-star with `matrixStar_mul`/`matrixStar_involutive`/`matrixStar_inclusionMatrix` to get `slStar U · M = σ.mobiusMatrix`.
- **Hypotheses**: `det M = m`, content of `M` is 1.
- **Uses from project**: [`exists_sl_right_mul_isColumnHermiteNormalForm_aux`, `exists_coxMatrix_of_isColumnHermiteNormalForm_aux`, `matrixStar`, `matrixStar_det`, `matrixStar_mul`, `matrixStar_involutive`, `matrixStar_inclusionMatrix`, `rankTwoContent_mul_sl`, `slStar`, `CoxMatrix.mobiusMatrix`, `Matrix.rankTwoContent`, `Matrix.IsColumnHermiteNormalForm` (HermiteNormalForm)]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 942–969, 28-line proof
- **Notes**: none

---

### File Summary
- Total declarations: 79 (19 defs/abbrevs + 1 structure, 56 lemmas/theorems, 3 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `CoxMatrix` (structure, used everywhere), `CoxMatrix.inclusionMatrix` (13 users), `coxInput` (12), `matrixStar` (11), `Gamma0RightCosets` (11), `CoxMatrix.mobiusMatrix` (5), `sigmaZero` (6), `coxRepresentative` (9), `coxReduction_spec` (4), `matrixStar_involutive` (4), `coxMatrix_reduction_unique` (3), `matrixStar_mul` (3), `matrixStar_det` (3), `slStar` (4), `CoxMatrix.d_pos` (4), `rightCosetTranslate` (4), `coxMatrixEquivRightCosets` (4), `rightCosetMul` (4), `CoxMatrix.toFin` (3), `determinantScale` (4), `determinantScaleDual` (3), `rankTwoContent_mul_sl` (2, near-key)
- Unused declarations (not used by anything in this file): `CoxMatrix.inclusionMatrix_content_eq_one`, `instance DecidableEq (CoxMatrix m)`, `one_lt_card_coxMatrix`, `gamma0RightCosetsFintype`, `exists_rightCosetMul_baseRightCoset_eq`, `rightCosetEval_smul`, `rightCosetEval_equiv`, `rightCosetTranslate_sigmaZero`, `j_act_sigmaZero`, `exists_sl2_mul_eq_coxMatrix` (the last five are the file's exported API, presumably consumed by `ModularPolynomial/*` and other downstream files)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: `columnHNF_eq_of_mul` (61), `exists_coxMatrix_reduction` (59), `coxMatrix_smith_normalization` (54), `levelJ_smul_eq_j_act_of_normalization` (43), `exists_coxMatrix_of_isColumnHermiteNormalForm_aux` (35), `rightRel_iff_coxRepresentative_eq` (34)
