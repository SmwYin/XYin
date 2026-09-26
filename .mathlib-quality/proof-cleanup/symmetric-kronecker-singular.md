# Symmetric cubic, Kronecker and singular-modulus cleanup

This bounded batch follows the parent's review of concrete remaining duplication. Full
read-through covered SymmetricCubicLaurent, KroneckerFrobenius and SingularModuli. Changes
in the larger LevelThree and Kronecker files target the reviewed Laurent base-change,
normal-form power and shifted-divisibility proofs. No computation tables or theorem
statements were altered. Baseline is `/tmp/xyin-proof-cleanup-before/XYin`.

| File | Before | After | Reduction |
|---|---:|---:|---:|
| SymmetricCubicLaurent | 452 | 391 | 61 |
| LevelThree | 878 | 858 | 20 |
| Kronecker | 793 | 771 | 22 |
| KroneckerFrobenius | 241 | 233 | 8 |
| SingularModuli | 250 | 238 | 12 |
| Total | 2614 | 2491 | 123 |

## Symmetric cubic proofs

- Added one private `symmetricCubicExpansion_coeff_aux` with bounded index `i ≤ 3`.
  The four existing named coefficient lemmas are direct specializations. Their previous
  proofs were identical apart from the index; the shared proof contains the same finite
  coefficient check, symmetry, and out-of-degree vanishing. All four original signatures
  and names remain intact.
- `cubicCoeff_eq_zero_of_laurent_coeff` uses `wellFounded_gt.induction` on `Fin 10`
  with the existing triangular-step proof, eliminating the manually strengthened reverse
  induction and its endpoint/successor comparisons.
- `eq_zero_of_cubicCoeff_eq_zero` uses the existing finite polynomial expansion and
  simplifies by the vanishing coefficient hypothesis. Removed ten local coefficient
  extractions and their individual vector-index simplifications.
- Retained the symmetric monomial definitions, Laurent orders/leading coefficients,
  leading-term triangularity, coefficient isolation and final detection theorem. These
  express distinct mathematical steps and are already concise. The explicit cubic data
  and its ordering proof are unchanged.

A proposed `simp (disch := omega)` alone did not eliminate the four coefficient index
conditions. It was replaced by four inequalities once in the shared helper; no limit
increase or broad proof-search workaround was used.

## LevelThree and Kronecker

- `LevelThree.bivariateLaurentEval_map` now rewrites each outer eval₂ as evaluation of
  Laurent specialization, applies `bivariateSpecializeLaurent_map_apply` from the existing
  Laurent evaluation module, and maps the outer evaluation. This deletes the repeated
  inner ring-hom compatibility proof and both long evaluation calcs. The two initial
  eval_map rewrites are required: eval₂ and eval-after-map are propositionally, not
  definitionally, equal.
- LevelThree finite jet tables and arithmetic computations are deliberately unchanged;
  this batch targets the proved base-change duplication rather than recasting verified
  numerical certificates.
- `Kronecker.jUnitLaurentSeriesMod_pow_prime_normalForm` obtains the existing
  `single_order_mul_powerSeriesPart` decomposition once, raises it to the p-th power,
  then uses `mul_pow`, `single_pow`, `PowerSeries.coe_pow` and the existing Frobenius
  expansion theorem. Removed local aliases and expanded multiplication/coercion calcs.
- `jUnitPrimeNormalForm_coeff_of_not_dvd` translates natural divisibility using
  `Int.natCast_dvd_natCast`, `Int.toNat_of_nonneg`, and `dvd_add_self_right`, replacing
  an explicitly constructed integer divisibility witness and linear combination.
- Other Kronecker definitions, coefficient formulas, cyclotomic phase/descent and final
  specialization arguments are unchanged.

## Frobenius and singular moduli

- `prime_sq_dvd_iff_dvd_shift_natAbs` uses `Int.natCast_dvd`, cast of the square, and
  `dvd_add_self_right`. The previous two directions were the same divisibility shift.
- Read and retained the Frobenius product classification, coefficient-cutoff argument,
  expansion/Frobenius comparison and final specialization injectivity. Their actual
  mathematics is not duplicated by the removed elementary divisibility steps.
- `fixingMatrix_content_eq_one` now rearranges the content gcd, applies
  `Int.gcd_add_self_right`, then the primitive quadratic equation's gcd-one hypothesis.
  This replaces four entry-divisibility facts and conversion of their difference back
  from Z to N. The identity was first tested as a generic standalone integer-matrix
  lemma importing only the HNF module.
- Retained the even/odd nonsquare determinant constructions: they have parallel structure
  but distinct quadratic shifts and witnesses, so a common abstraction would obscure
  their formulas. Also retained the Möbius fixed-point identity, modular-polynomial root,
  leading-coefficient ±1 argument and final integrality statement.

## API and scope checks

Primary local source search covered the Lean core Int gcd identities, mathlib divisibility,
well-founded reverse order, Laurent/PowerSeries coercions and polynomial eval₂/map APIs.
Independent Lean examples checked both divisibility identities and reverse well-founded
induction. Only one new helper theorem was added; no new data definitions or public API
changes. All original public/private declarations, authorship and mathematical docs remain.
No sorry, admit, new axiom, heartbeat or recursion limit was added. Changed files pass
`git diff --check`. Parent independently reviews actual diffs and owns cumulative builds.

## Validation

All five final files passed complete direct Lean elaboration with zero errors/warnings.
All five baseline profiles and final-source axiom/profile runs exited 0. The final runs
compile copies of the complete edited sources with appended `#print axioms` commands;
they do not inspect stale compiled declarations. Command:

```text
lake env lean -Dprofiler=true -Dprofiler.threshold=100 /tmp/xyin-NAME-cleanup-axioms.lean
```

| File | Tactic before → after | Typeclass before → after |
|---|---:|---:|
| SymmetricCubicLaurent | 632 → 394 ms | 3.23 → 2.04 s |
| LevelThree | 1.75 → 1.39 s | 4.72 → 3.78 s |
| Kronecker | 554 → 559 ms | 2.09 → 1.97 s |
| KroneckerFrobenius | 335 → 296 ms | 1.14 → 1.27 s |
| SingularModuli | 171 → 164 ms | 848 → 892 ms |

These are single concurrent-run cumulative profiler measurements, not a stable benchmark
or a claimed speedup. Existing LevelThree numerical certificates remain the most expensive
individual operations (baseline `simp` 1.05 s; final `simp` 721 ms and type checking up to
923 ms). No resource limits were increased.

The seven checked results depend only on `propext`, `Classical.choice`, and `Quot.sound`:

- `Cox.symmetric_bidegree_three_eq_zero_of_laurent_coeff`
- `Cox.modularPolynomial_three_of_complex_swap`
- `Cox.jUnitLaurentSeriesMod_pow_prime`
- `Cox.specializeJMod_modularPolynomial_eq_formal`
- `Cox.theorem_11_18_v`
- `Cox.PrimitiveQuadraticEquation.fixingMatrix_content_eq_one`
- `Cox.singularModulus_isIntegral`

Logs: `/tmp/xyin-{symmetric,levelthree,kronecker,frobenius,singular}-profile-{before,after}.log`.
All source files in this batch are frozen and ready for the parent's cumulative build.
