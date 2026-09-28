# Deferred deeper changes (noted 2026-09-26, not started)

These came out of the 2026-09-25 overview and the 2026-09-26 cleanup. Each one is a real improvement.
Each was deliberately postponed because it is a larger redesign, changes widely used types, or is public work.

## 1. `CuspData` as a structure
- **Now:** `CuspData N f` (`Cox/ModularFunction/CuspData.lean`) is an anonymous conjunction of three conditions: meromorphic
  on ℍ, invariant under Γ₀(N), meromorphic cusp function at 0. Named accessor lemmas were added on 2026-09-26
  (`CuspData.meromorphicOn`, `.slash_eq`, `.apply_smul`, `.meromorphicAt_cuspFunction`, `LevelOneCuspData.periodic`, …),
  so positional `.1/.2.1/.2.2` access is gone from the code.
- **Change:** turn it into a `structure` with named fields, with the accessor lemmas becoming field projections.
- **Why deferred:** the type is used across the Cox files (CoxMatrices/Basic, LevelJ, ModularPolynomial/*, Interpolation);
  every anonymous-constructor proof `⟨_, _, _⟩` would need rewriting.
- **Effort:** small to medium, mechanical.

## 2. Dedekind ψ as an arithmetic function
- **Now:** `Cox/CoxMatrices/Cardinality.lean` proves |C(m)| = m ∏_{p | m} (1 + 1/p) (ℚ-valued `card_coxMatrix`),
  the ℕ product formula `card_coxMatrix_eq_factorization_prod`, and `gamma0_index_eq_card_coxMatrix`.
- **Change:** define `ArithmeticFunction.dedekindPsi` (e.g. `pmul μ μ * id` or via its prime-power values), prove
  `IsMultiplicative`, and state `card_coxMatrix` / `[SL₂(ℤ) : Γ₀(m)] = ψ m` with it.
- **Why deferred:** it did not shorten the existing proof (the CRT/fibration argument is still needed); its value is
  mathlib-style statements and an upstream contribution.
- **Effort:** medium.

## 3. Hermite normal form in any rank
- **Now:** `Cox/HermiteNormalForm.lean` treats 2×2 integer matrices / rank-two lattices, with existence, uniqueness
  (`IsColumnHermiteNormalForm.eq_of_mul_isUnit_det`), index = |det|, and the cyclicity criterion `rankTwoContent = 1`.
  Mathlib has no Hermite normal form.
- **Change:** n×n column HNF over ℤ (or a Euclidean/Bézout domain with chosen residues), existence and uniqueness.
  The cyclic-quotient criterion in rank n is D_{n−1}(A) = 1 (gcd of the (n−1)-minors); the entry-gcd criterion is false
  from rank 3 on (e.g. diag(1, 2, 2)).
- **Why deferred:** new development; the rank-two version is all the Cox proofs need.
- **Effort:** large.

## 4. Upstream pull requests to mathlib
Candidates judged mathlib gaps (details: `.mathlib-quality/overview/analysis-2026-09-25/step9-mathlibable-triage.md`,
`.mathlib-quality/cleanup-2026-09-26/report-*.md` "New API" sections):
- `lattice_eq_of_g₂_eq_of_g₃_eq` and the ℘-recursion block (`uniqueness.lean`) — fills the TODO in mathlib's
  `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`.
- Sturm bound for arithmetic subgroups and `FiniteDimensional ℂ (ModularForm Γ k)` (`Modularforms/SturmBound.lean`, mathlib-only).
- `HahnSeries.mapRingHom`, `HahnSeries.coeffSubring`, `HahnSeries.leadingCoeff_pow`, `CharP` for Hahn series,
  `LaurentSeries.coeff_single_neg_mul_coe_expand`, `PowerSeries.pow_prime_pow_eq_expand` (`Cox/LaurentSeriesAux.lean`).
- `MeromorphicNFAt.analyticAt_of_eventually_norm_le`, codiscrete/`NeBot` lemmas, `Algebra R (Filter.Germ l A)` (ModularFunctions).
- `Polynomial.eq_or_eq_neg_of_associated`, the conjugate-counting irreducibility lemma, bivariate swap lemmas.
- Dedekind ψ (item 2) and the Γ₀(m) index formula.
- **Why deferred:** outward-facing work under the author's name; each needs mathlib-style review and generalisation first.

## Other postponed items
- `LaurentSeries.substMonomial` + analytic bridge (a single "q ↦ c q^r substitution" lemma): designed, no net deletion yet.
- `HasCoeffsIn` → a `PowerSeries.lifts` mirroring `Polynomial.lifts` (upstream-first).
- Bidegree-≤ n version of `symmetric_bidegree_three_eq_zero_of_laurent_coeff` (needed only for explicit Φ_m with m > 3).
- Cyclic sublattices / Thm 11.23 for an arbitrary rank-two free ℤ-module instead of ℂ-lattices.
- Laurent expansion at the cusp restated as "Laurent expansion of a meromorphic germ" at mathlib generality.
- Module/file names still use lowercase and underscores (`qExpansion_tactic/`, `qexp_simp.lean`, `jfunction.lean`, …);
  mathlib uses UpperCamelCase file names. Renaming changes import paths.
- The per-declaration `/mathlibable` assessment (only triaged so far).
- ~~`BivariatePolynomial R` vs mathlib's `R[X][Y]`~~ — DONE 2026-09-28: switched fully to mathlib's API (see `cleanup-2026-09-26/SUMMARY.md`).
- The two anonymous instances in `Cox/UpperHalfPlaneFunctionField.lean` have long auto-generated names; they could be
  named explicitly.
