# Inventory: XYin/PhD/Modularforms/Summability/Basic.lean  (206 lines)

Reindexing lemmas for sums over ℤ / ℕ / ℕ+, geometric-type summability of `n^k · exp(2πi e z n)` on the upper half-plane, and the divisor-sum (σ_k) rewriting of double exponential sums. Split out of the old `summable_lems`; feeds `Summability/Reciprocal`, `Summability/QExpansion`, `multipliable_lems`, and `Eisenstein.lean` (only `a33` and `tsum_pnat_coe_mul_geometric` are used outside this batch). Almost every lemma is a thin wrapper over an existing mathlib lemma (ptr: `Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean`, `Mathlib/NumberTheory/TsumDivisorsAntidiagonal.lean`, `Mathlib/NumberTheory/ModularForms/EisensteinSeries/QExpansion.lean`).

## Declarations

### `theorem int_sum_neg`
- **Type**: `{α} [AddCommMonoid α] [TopologicalSpace α] [T2Space α] (f : ℤ → α) : ∑' d : ℤ, f d = ∑' d, f (-d)`
- **What**: A ℤ-indexed tsum is invariant under the substitution d ↦ −d.
- **How**: Transport along the project equivalence `negEquiv : ℤ ≃ ℤ` via `Equiv.tsum_eq`.
- **Hypotheses**: Hausdorff topological additive monoid; no summability needed.
- **Uses from project**: `negEquiv` (equivs.lean:18)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 26–28, proof body ≈ 1 line
- **Notes**: Exact duplicate (symm) of mathlib `tsum_comp_neg` (`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:551`, `@[simp]`, to_additive of `tprod_comp_neg`). Dead project-wide.

### `theorem summable_neg`
- **Type**: `{α} [TopologicalSpace α] [AddCommMonoid α] (f : ℤ → α) (hf : Summable f) : Summable fun d => f (-d)`
- **What**: Summability over ℤ is preserved by negating the index.
- **How**: `negEquiv.summable_iff`.
- **Hypotheses**: Summable f.
- **Uses from project**: `negEquiv` (equivs.lean:18)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 30–32, proof body ≈ 1 line
- **Notes**: Mathlib: `(Equiv.neg ℤ).summable_iff.mpr hf` or `summable_int_iff_summable_nat_and_neg` (`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:508`, to_additive). Dead project-wide.

### `lemma aux33`
- **Type**: `(f : ℕ → ℂ) (hf : Summable f) : ∑' n, f n = limUnder atTop (fun N => ∑ n ∈ Finset.range N, f n)`
- **What**: For a summable complex sequence, the tsum equals the limit of partial sums over `range N`.
- **How**: `hf.hasSum.comp tendsto_finset_range` then `Filter.Tendsto.limUnder_eq`.
- **Hypotheses**: Summable f.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 34–36, proof body ≈ 1 line
- **Notes**: Junk name. Mathlib route: `HasSum.tendsto_sum_nat` (`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:48`, to_additive) + `Filter.Tendsto.limUnder_eq` (`Mathlib/Topology/Separation/Hausdorff.lean:291`); no single mathlib lemma states the `limUnder` form (searched `limUnder` in `Mathlib/Topology/Algebra/InfiniteSum/`). Dead project-wide.

### `lemma tsum_pnat_eq_tsum_succ3`
- **Type**: `{α} [TopologicalSpace α] [AddCommMonoid α] [T2Space α] (f : ℕ → α) : ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f (n + 1)`
- **What**: Sum over ℕ+ equals the shifted sum over ℕ.
- **How**: `apply tsum_pnat_eq_tsum_succ` (mathlib).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 39–41, proof body ≈ 1 line
- **Notes**: Exact wrapper of mathlib `tsum_pnat_eq_tsum_succ` (`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:545`, to_additive of `tprod_pnat_eq_tprod_succ`). Comment at line 38 "this is being Pr'd" is stale — it is already in mathlib. Dead project-wide.

### `theorem nat_pos_tsum2`
- **Type**: `{α} [TopologicalSpace α] [AddCommMonoid α] (f : ℕ → α) (hf : f 0 = 0) : (Summable fun x : ℕ+ => f x) ↔ Summable f`
- **What**: If f vanishes at 0, summability over ℕ+ and over ℕ coincide.
- **How**: `PNat.coe_injective.summable_iff` (Function.Injective.summable_iff) with the support-in-range condition discharged from `f 0 = 0`.
- **Hypotheses**: f 0 = 0; only a topological additive monoid.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 45–52, proof body ≈ 7 lines
- **Notes**: Mathlib `summable_pnat_iff_summable_nat` (`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:540`) gives the same iff with no `f 0 = 0` hypothesis but needs `[AddCommGroup] [IsTopologicalAddGroup]`. Dead project-wide.

### `theorem tsum_pNat`
- **Type**: `{α} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α] [T2Space α] [CompleteSpace α] (f : ℕ → α) (hf : f 0 = 0) : ∑' n : ℕ+, f n = ∑' n, f n`
- **What**: If f 0 = 0 the tsum over ℕ+ equals the tsum over ℕ (no summability needed).
- **How**: `PNat.coe_injective.tsum_eq` with support ⊆ range.
- **Hypotheses**: f 0 = 0.
- **Uses from project**: []
- **Used by**: `tsum_pnat_coe_mul_geometric` (68); also `pos_sum_eq` in Summability/QExpansion.lean:246
- **Visibility**: public
- **Lines**: 54–58, proof body ≈ 3 lines
- **Notes**: Typeclass hypotheses are far stronger than the proof uses (`Function.Injective.tsum_eq` needs only `[AddCommMonoid] [TopologicalSpace]`). Mathlib `tsum_zero_pnat_eq_tsum_nat` (NatInt.lean:549) is the `Summable f` variant (`f 0 + ∑' ℕ+ = ∑' ℕ`).

### `lemma tsum_pnat_eq_tsum_succ4`
- **Type**: `{α} [TopologicalSpace α] [AddCommGroup α] [IsTopologicalAddGroup α] [T2Space α] (f : ℕ → α) (hf : Summable f) : f 0 + ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f n`
- **What**: Splitting off the zeroth term of a summable ℕ-series leaves the ℕ+-sum.
- **How**: `exact tsum_zero_pnat_eq_tsum_nat hf`.
- **Hypotheses**: Summable f.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 60–63, proof body ≈ 1 line
- **Notes**: Exact wrapper of mathlib `tsum_zero_pnat_eq_tsum_nat` (`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:549`) — typechecked in scratch. Dead project-wide.

### `lemma tsum_pnat_coe_mul_geometric`
- **Type**: `{r : ℝ} (hr : ‖r‖ < 1) : (∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ)) = r / (1 - r) ^ 2`
- **What**: Closed form ∑_{n≥1} n rⁿ = r/(1−r)².
- **How**: Reindex to ℕ with `tsum_pNat` (the n = 0 term is 0), then mathlib `tsum_coe_mul_geometric_of_norm_lt_one`.
- **Hypotheses**: ‖r‖ < 1.
- **Uses from project**: `tsum_pNat`
- **Used by**: unused in file; used in Eisenstein.lean:638
- **Visibility**: public
- **Lines**: 66–69, proof body ≈ 2 lines
- **Notes**: Has a docstring. Mathlib has only the ℕ form (`Mathlib/Analysis/SpecificLimits/Normed.lean:536`). Live.

### `theorem nat_pos_tsum2'`
- **Type**: `{α} [TopologicalSpace α] [AddCommMonoid α] (f : ℕ → α) : (Summable fun x : ℕ+ => f x) ↔ Summable fun x : ℕ => f (x + 1)`
- **What**: Summability over ℕ+ ↔ summability of the shifted sequence.
- **How**: `exact summable_pnat_iff_summable_succ`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `summable_pnats` (206)
- **Visibility**: public
- **Lines**: 71–73, proof body ≈ 1 line
- **Notes**: Exact wrapper of mathlib `summable_pnat_iff_summable_succ` (`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:535`).

### `theorem int_nat_sum`
- **Type**: `{α} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α] [CompleteSpace α] (f : ℤ → α) : Summable f → Summable fun x : ℕ => f x`
- **What**: A summable ℤ-series restricts to a summable ℕ-series.
- **How**: `Summable.comp_injective Nat.cast_injective`.
- **Hypotheses**: complete uniform additive group.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 75–78, proof body ≈ 1 line
- **Notes**: Mathlib: `(summable_int_iff_summable_nat_and_neg.mp hf).1` (`NatInt.lean:508`). Dead project-wide.

### `theorem HasSum.nonneg_add_neg`
- **Type**: `{α} [TopologicalSpace α] [AddCommGroup α] [IsTopologicalAddGroup α] [T2Space α] {a b : α} {f : ℤ → α} (hnonneg : HasSum (fun n : ℕ => f n) a) (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + b)`
- **What**: Glue a HasSum over ℕ and one over the negative integers into a HasSum over ℤ.
- **How**: `HasSum.int_rec` (mathlib) with a `Int` case split.
- **Hypotheses**: the two half-sums exist.
- **Uses from project**: []
- **Used by**: `HasSum.pos_add_zero_add_neg` (92)
- **Visibility**: public
- **Lines**: 80–85, proof body ≈ 2 lines
- **Notes**: Exactly mathlib `HasSum.of_nat_of_neg_add_one` (`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:349`, to_additive) — typechecked in scratch (`hnonneg.of_nat_of_neg_add_one hneg`). Dead project-wide.

### `theorem HasSum.pos_add_zero_add_neg`
- **Type**: `… {f : ℤ → α} (hpos : HasSum (fun n : ℕ => f (n + 1)) a) (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + f 0 + b)`
- **What**: Three-way split of a ℤ-sum: positive part, zero term, negative part.
- **How**: `HasSum.nonneg_add_neg` after re-attaching the zero term with `hasSum_nat_add_iff`.
- **Hypotheses**: the two half-sums exist.
- **Uses from project**: `HasSum.nonneg_add_neg`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 88–93, proof body ≈ 2 lines
- **Notes**: Mathlib: `HasSum.of_add_one_of_neg_add_one` / `tsum_of_add_one_of_neg_add_one` (`NatInt.lean:461`, to_additive) — same statement up to `-(n+1)` vs `-n.succ` and summand order. Dead project-wide.

### `theorem sum_int_even`
- **Type**: `{α} [UniformSpace α] [CommRing α] [IsUniformAddGroup α] [CompleteSpace α] [T2Space α] (f : ℤ → α) (hf : ∀ n : ℤ, f n = f (-n)) (hf2 : Summable f) : ∑' n, f n = f 0 + 2 * ∑' n : ℕ+, f n`
- **What**: An even summable ℤ-series is f 0 plus twice its ℕ+ part.
- **How**: mathlib `tsum_int_eq_zero_add_two_mul_tsum_pnat`, converting `2 • _` to `2 * _` with `nsmul_eq_mul`.
- **Hypotheses**: f even, summable.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 95–99, proof body ≈ 2 lines
- **Notes**: Wrapper of `tsum_int_eq_zero_add_two_mul_tsum_pnat` (`NatInt.lean:573`, to_additive of `tprod_int_eq_zero_mul_tprod_pnat_sq`). `CommRing` only needed for `nsmul_eq_mul`. Dead project-wide.

### `theorem sigma_eq_sum_div'`
- **Type**: `(k n : ℕ) : sigma k n = ∑ d ∈ Nat.divisors n, (n / d) ^ k`
- **What**: σ_k(n) as a sum of (n/d)^k over divisors.
- **How**: `sigma` unfold + `Nat.sum_div_divisors`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 101–104, proof body ≈ 2 lines
- **Notes**: Exact duplicate of mathlib `ArithmeticFunction.sigma_eq_sum_div` (`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:175`) — typechecked in scratch. Dead project-wide.

### `theorem a33`
- **Type**: `(k : ℕ) (e : ℕ+) (z : ℍ) : Summable fun c : ℕ+ => (c : ℂ) ^ k * exp (2 * ↑π * Complex.I * e * ↑z * c)`
- **What**: ∑_{c≥1} c^k q_e^c converges where q_e = exp(2πi e z), |q_e| < 1.
- **How**: `summable_pow_mul_geometric_of_norm_lt_one` (`Mathlib/Analysis/SpecificLimits/Normed.lean:488`) restricted to ℕ+ via `.subtype`, the ratio bound from `exp_upperHalfPlane_lt_one_nat` (with `e = e.natPred + 1`), and `Complex.exp_nat_mul` to match the exponent.
- **Hypotheses**: z ∈ ℍ, e ≥ 1.
- **Uses from project**: `exp_upperHalfPlane_lt_one_nat` (exp_lems.lean:18)
- **Used by**: `hsum` (125); used in Eisenstein.lean:508
- **Visibility**: public
- **Lines**: 107–120, proof body ≈ 13 lines
- **Notes**: Mathlib `EisensteinSeries.summable_pow_mul_cexp` (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/QExpansion.lean:192`) is the ℕ-indexed twin `Summable fun c : ℕ ↦ (c:ℂ)^k * cexp (2πI e z)^c`; ℕ+ form follows by `summable_pnat_iff_summable_nat`. Live (Eisenstein.lean).

### `lemma hsum`
- **Type**: `(k : ℕ) (z : ℍ) : Summable fun b : ℕ+ => ∑ _ ∈ (b : ℕ).divisors, b ^ k * ‖exp (2 * ↑π * Complex.I * ↑z * b)‖`
- **What**: ∑_b card(divisors b)·b^k·|q^b| converges (majorant for divisor-sum rearrangements).
- **How**: `Finset.sum_const` turns the inner sum into `card · _`; compare with `a33 (k+1) 1 z` via `Summable.of_nonneg_of_le` using `Nat.card_divisors_le_self` (`Mathlib/NumberTheory/Divisors.lean:226`).
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `a33`
- **Used by**: unused in file (the `hsum` at Summability/QExpansion.lean:130 is a local `have`, not this lemma)
- **Visibility**: public
- **Lines**: 122–136, proof body ≈ 14 lines
- **Notes**: Same estimate as mathlib's private `summable_divisorsAntidiagonal_aux` (`Mathlib/NumberTheory/TsumDivisorsAntidiagonal.lean:77`, uses `Nat.card_divisors_le_self`). Dead project-wide.

### `theorem summable_auxil_1`
- **Type**: `(k : ℕ) (z : ℍ) : Summable fun c : (n : ℕ+) × { x // x ∈ (n : ℕ).divisorsAntidiagonal } ↦ (c.snd.1.1 : ℂ) ^ k * cexp (2πi z · c.snd.1.1 · c.snd.1.2)`
- **What**: Summability of d^k q^{d·e} over the sigma-type of divisor antidiagonals (index for ∑_n ∑_{de=n}).
- **How**: `summable_prod_mul_pow` (`Mathlib/NumberTheory/TsumDivisorsAntidiagonal.lean:99`) with `.prod_symm`, transported through `sigmaAntidiagonalEquivProd.summable_iff`, and `Complex.exp_nat_mul`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `exp_upperHalfPlane_lt_one` (exp_lems.lean:14)
- **Used by**: `a4` (198)
- **Visibility**: public
- **Lines**: 138–145, proof body ≈ 4 lines
- **Notes**: Statement is mathlib's private `summable_divisorsAntidiagonal_aux` with the factors swapped. Dead outside file.

### `lemma sum_range_zero`
- **Type**: `(f : ℤ → ℂ) (n : ℕ) : ∑ m ∈ Finset.range (n+1), f m = f 0 + ∑ m ∈ Finset.range n, f (m+1)`
- **What**: Peel the first term off a finite range sum.
- **How**: `Finset.sum_range_succ'`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 147–149, proof body ≈ 1 line
- **Notes**: Specialisation of mathlib `Finset.sum_range_succ'` (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:534`, to_additive). Dead project-wide.

### `theorem tsum_sigma_eqn2`
- **Type**: `(k : ℕ) (z : ℍ) : ∑' (c : Fin 2 → ℕ+), (c 0 ^ k : ℂ) * exp (2πi z c0 c1) = ∑' e : ℕ+, sigma k e * exp (2πi z e)`
- **What**: Lambert-type rearrangement ∑_{d,e≥1} d^k q^{de} = ∑_n σ_k(n) qⁿ, indexed by `Fin 2 → ℕ+`.
- **How**: `piFinTwoEquiv.symm.tsum_eq`, `Summable.tsum_prod` from `summable_prod_mul_pow`, `Equiv.prodComm`, then mathlib `tsum_prod_pow_eq_tsum_sigma` (`Mathlib/NumberTheory/TsumDivisorsAntidiagonal.lean:106`).
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `exp_upperHalfPlane_lt_one`
- **Used by**: `tsum_sigma_eqn` (167)
- **Visibility**: public
- **Lines**: 151–160, proof body ≈ 7 lines
- **Notes**: Mathlib also has the downstream form `tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow` (`EisensteinSeries/QExpansion.lean:221`). Dead outside file.

### `theorem tsum_sigma_eqn`
- **Type**: `{k : ℕ} (z : ℍ) : ∑' c : ℕ+ × ℕ+, (c.1 ^ k : ℂ) * exp (2πi z c.1 c.2) = ∑' e : ℕ+, sigma k e * exp (2πi e z)`
- **What**: Same as `tsum_sigma_eqn2`, indexed by ℕ+ × ℕ+.
- **How**: `piFinTwoEquiv.tsum_eq` then `grind` against `tsum_sigma_eqn2`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `tsum_sigma_eqn2`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 163–169, proof body ≈ 4 lines
- **Notes**: Comment line 162 "This is proven in the modular forms repo". Mathlib `tsum_prod_pow_eq_tsum_sigma` + `Summable.tsum_prod` gives this directly. Dead project-wide.

### `lemma exp_aux`
- **Type**: `(z : ℍ) (n : ℕ) : cexp (2 * ↑π * Complex.I * n * ↑z) = cexp (2 * ↑π * Complex.I * ↑z) ^ n`
- **What**: q^n = exp(2πi n z).
- **How**: `Complex.exp_nat_mul` + `ring`.
- **Hypotheses**: none (z ∈ ℍ irrelevant).
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 171–175, proof body ≈ 3 lines
- **Notes**: Mathlib `Complex.exp_nat_mul` (`Mathlib/Analysis/Complex/Exponential.lean:153`) / `Complex.exp_nsmul'` (:149). Over-restricted to ℍ. Dead project-wide.

### `theorem summable_exp_pow`
- **Type**: `(z : ℍ) : Summable fun i : ℕ ↦ ‖cexp (2 * ↑π * Complex.I * (↑i + 1) * z)‖`
- **What**: ∑ |q|^{i+1} converges.
- **How**: `summable_geometric_of_norm_lt_one` composed with `Nat.succ_injective`, norm bound from `exp_upperHalfPlane_lt_one`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `exp_upperHalfPlane_lt_one`
- **Used by**: unused in file; used in multipliable_lems.lean:40
- **Visibility**: public
- **Lines**: 177–182, proof body ≈ 4 lines
- **Notes**: Mathlib `ModularForm.summable_eta_q` (`Mathlib/NumberTheory/ModularForms/DedekindEta.lean:102`) is `Summable fun n ↦ ‖-eta_q n z‖` with `eta_q_eq_cexp` (:46) giving exactly this summand. Live (multipliable_lems).

### `theorem a1`
- **Type**: `(k : ℕ) (e : ℕ+) (z : ℍ) : Summable fun c : ℕ => (e : ℂ) ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑z * e * c)`
- **What**: e^{k−1} ∑_c q_e^c converges.
- **How**: `summable_geometric_of_norm_lt_one` + `.mul_left`, ratio bound from `exp_upperHalfPlane_lt_one_nat`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `exp_upperHalfPlane_lt_one_nat`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 185–192, proof body ≈ 6 lines
- **Notes**: Comment line 184 "straight from the mod forms repo". Mathlib `summable_pow_mul_cexp 0 e z` + `.mul_left`. The 5-line `hr` block is copy-pasted from `a33` (107–112). Dead project-wide.

### `theorem a4`
- **Type**: `(k : ℕ) (z : ℍ) : Summable (uncurry fun b c : ℕ+ => ↑b ^ (k - 1) * exp (2 * ↑π * Complex.I * ↑c * ↑z * ↑b))`
- **What**: Double series ∑_{b,c≥1} b^{k−1} q^{bc} converges.
- **How**: Pull back along `sigmaAntidiagonalEquivProd` and apply `summable_auxil_1 (k-1)` with `Summable.congr` + `ring_nf`.
- **Hypotheses**: z ∈ ℍ.
- **Uses from project**: `summable_auxil_1`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 194–203, proof body ≈ 8 lines
- **Notes**: Mathlib `summable_prod_mul_pow (k-1) (norm_exp_two_pi_I_lt_one z)` (+ `.prod_symm`) is the same statement after `Complex.exp_nat_mul`. Dead project-wide.

### `lemma summable_pnats`
- **Type**: `(f : ℕ → ℂ) : Summable (fun n : ℕ+ => f n) ↔ Summable f`
- **What**: Summability over ℕ+ and ℕ agree (ℂ-valued).
- **How**: `nat_pos_tsum2'` then `summable_nat_add_iff`.
- **Hypotheses**: none.
- **Uses from project**: `nat_pos_tsum2'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 205–206, proof body ≈ 1 line
- **Notes**: Exactly mathlib `summable_pnat_iff_summable_nat` (`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:540`) — typechecked in scratch. Dead project-wide.

## File Summary
- Total declarations: 25 (0 defs, 25 lemmas/theorems, 0 instances, 0 other)
- Key API (used by 3+ others in the file): none (max fan-in is 1)
- Unused declarations (not used by anything in this file): `int_sum_neg`, `summable_neg`, `aux33`, `tsum_pnat_eq_tsum_succ3`, `nat_pos_tsum2`, `tsum_pnat_eq_tsum_succ4`, `tsum_pnat_coe_mul_geometric`, `int_nat_sum`, `HasSum.pos_add_zero_add_neg`, `sum_int_even`, `sigma_eq_sum_div'`, `hsum`, `sum_range_zero`, `tsum_sigma_eqn`, `exp_aux`, `summable_exp_pow`, `a1`, `a4`, `summable_pnats` (of these only `tsum_pnat_coe_mul_geometric` [Eisenstein.lean:638], `a33` [Eisenstein.lean:508], `summable_exp_pow` [multipliable_lems.lean:40], `tsum_pNat` [Summability/QExpansion.lean:246] are used anywhere in the project)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `int_sum_neg` (26) = `tsum_comp_neg` (`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:551`, simp).
- `summable_neg` (30) = `(Equiv.neg ℤ).summable_iff` / `summable_int_iff_summable_nat_and_neg` (NatInt.lean:508).
- `tsum_pnat_eq_tsum_succ3` (39) = `tsum_pnat_eq_tsum_succ` (NatInt.lean:545); `nat_pos_tsum2'` (71) = `summable_pnat_iff_summable_succ` (NatInt.lean:535); `summable_pnats` (205) = `summable_pnat_iff_summable_nat` (NatInt.lean:540, verified); `tsum_pnat_eq_tsum_succ4` (60) = `tsum_zero_pnat_eq_tsum_nat` (NatInt.lean:549, verified); `sum_int_even` (95) = `tsum_int_eq_zero_add_two_mul_tsum_pnat` (NatInt.lean:573); `HasSum.nonneg_add_neg` (80) = `HasSum.of_nat_of_neg_add_one` (NatInt.lean:349, verified); `HasSum.pos_add_zero_add_neg` (88) ≈ `HasSum.of_add_one_of_neg_add_one` (NatInt.lean:461 area); `int_nat_sum` (75) = `summable_int_iff_summable_nat_and_neg.mp _ |>.1`.
- `sigma_eq_sum_div'` (101) = `ArithmeticFunction.sigma_eq_sum_div` (`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:175`, verified).
- `a33` (107), `a1` (185) = `EisensteinSeries.summable_pow_mul_cexp` (`Mathlib/NumberTheory/ModularForms/EisensteinSeries/QExpansion.lean:192`) up to ℕ/ℕ+ and `exp_nat_mul`.
- `summable_auxil_1` (138), `a4` (194) = `summable_prod_mul_pow` (`Mathlib/NumberTheory/TsumDivisorsAntidiagonal.lean:99`) ± `sigmaAntidiagonalEquivProd`; `hsum` (122) = its private helper `summable_divisorsAntidiagonal_aux` (:77).
- `tsum_sigma_eqn2`/`tsum_sigma_eqn` (151/163) = `tsum_prod_pow_eq_tsum_sigma` (TsumDivisorsAntidiagonal.lean:106) + `Summable.tsum_prod`.
- `exp_aux` (171) = `Complex.exp_nat_mul` (`Mathlib/Analysis/Complex/Exponential.lean:153`); `sum_range_zero` (147) = `Finset.sum_range_succ'`.
- `summable_exp_pow` (177) = `ModularForm.summable_eta_q` (`Mathlib/NumberTheory/ModularForms/DedekindEta.lean:102`) via `eta_q_eq_cexp`.
- `aux33` (34): no single mathlib lemma; compose `HasSum.tendsto_sum_nat` + `Tendsto.limUnder_eq`.
- `tsum_pnat_coe_mul_geometric` (66): no ℕ+ analogue found (searched `pnat` in `Mathlib/Analysis/SpecificLimits/Normed.lean`); the ℕ form is `tsum_coe_mul_geometric_of_norm_lt_one` (:536).
- Hand-rolled pattern: the "‖exp(2πi e z)‖ < 1 via natPred" block is duplicated verbatim at 109–112 and 187–190; mathlib's `norm_exp_two_pi_I_lt_one` applied to `⟨e * z, _⟩` (as in `summable_pow_mul_cexp`) avoids it.
### Missing API / repeated patterns
- Repeated 4-line fragment: `have h := exp_upperHalfPlane_lt_one_nat z e.natPred; rw [← Nat.cast_add_one, e.natPred_add_one] at h; simpa [mul_assoc, mul_comm, mul_left_comm] using h` at 110–112 and 188–190 → one lemma `norm_exp_two_pi_I_pnat_mul_lt_one (e : ℕ+) (z : ℍ) : ‖cexp (2πI * e * z)‖ < 1`.
- Repeated `simpa [← Complex.exp_nat_mul, mul_comm, mul_left_comm, mul_assoc]` normalisation at 144–145, 156, 179–180, 191 (and throughout Summability/QExpansion.lean) → the project should state everything in mathlib's `cexp (2πI z) ^ n` normal form instead of `cexp (2πI n z)`.
### Junk candidates
- Dead project-wide (grep -rnw over XYin): `int_sum_neg`, `summable_neg`, `aux33`, `tsum_pnat_eq_tsum_succ3`, `nat_pos_tsum2`, `tsum_pnat_eq_tsum_succ4`, `nat_pos_tsum2'`(only feeds dead `summable_pnats`), `int_nat_sum`, `HasSum.nonneg_add_neg`, `HasSum.pos_add_zero_add_neg`, `sum_int_even`, `sigma_eq_sum_div'`, `hsum`, `sum_range_zero`, `tsum_sigma_eqn2`, `tsum_sigma_eqn`, `exp_aux`, `a1`, `a4`, `summable_pnats` — 20 of 25.
- One-line wrappers of a single mathlib call: `int_sum_neg`, `summable_neg`, `aux33`, `tsum_pnat_eq_tsum_succ3`, `tsum_pnat_eq_tsum_succ4`, `nat_pos_tsum2'`, `int_nat_sum`, `sum_int_even`, `sum_range_zero`, `summable_pnats`.
- Stale comments: line 38 "this is being Pr'd" (already merged), line 162 "proven in the modular forms repo", line 184 "straight from the mod forms repo". Bad names: `aux33`, `a33`, `a1`, `a4`, `hsum`, `summable_auxil_1`, `nat_pos_tsum2`/`'`, `tsum_pNat`.
- Blank-line noise at 42–44, 86–87, 105–106.
### Moral duplicates within this batch
- `nat_pos_tsum2` (45) vs `summable_pnats` (205) vs mathlib `summable_pnat_iff_summable_nat`: same iff.
- `tsum_pNat` (54) vs `tsum_pnat_eq_tsum_succ4` (60): both "drop the zero term"; one assumes `f 0 = 0`, the other `Summable f`.
- `a33` (107) vs `a1` (185): identical proof skeleton (natPred trick + geometric), differing only in which factor is constant.
- `tsum_sigma_eqn2` (151) vs `tsum_sigma_eqn` (163): same identity, `Fin 2 → ℕ+` vs `ℕ+ × ℕ+`.
- `summable_auxil_1` (138) vs `a4` (194): same summability through `sigmaAntidiagonalEquivProd` in both directions.
### Generalization notes
- `tsum_pNat` (54): only `Function.Injective.tsum_eq` is used, so `[AddCommMonoid α] [TopologicalSpace α]` suffices; the `UniformSpace/IsUniformAddGroup/CompleteSpace/T2Space` assumptions are dead.
- `sum_int_even` (95): `CommRing` is used only for `nsmul_eq_mul`; state with `2 • _` and it holds for any complete uniform additive group (as mathlib does).
- `exp_aux` (171), `sum_range_zero` (147): `z : ℍ` resp. `f : ℤ → ℂ` are irrelevant — hold for all `z : ℂ` resp. any `AddCommMonoid`.
- `a33`, `a1`, `a4`, `summable_auxil_1`, `tsum_sigma_eqn*`: only `‖q‖ < 1` is used (via `exp_upperHalfPlane_lt_one*`), so they hold for any `q` in the unit disc, as mathlib's `TsumDivisorsAntidiagonal` versions do.
