# BorelAxis independent review

Review date: 2026-10-04. This review is read-only for Lean sources: no proof edits,
compiler invocations, model/environment changes, or usage resets were performed.

**Verdict: PASS for the retained module and its named strict receipt.** The result
is equality of the embedded subgroup ideals inside one fixed elliptic curve.

## Frozen source and provenance

Retained source:
[YZeroCoarseBorelAxis.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseBorelAxis.lean).
It has 119 lines and SHA-256
`9ee3ab2ae2024383b9a5712038ba2f238aa43678eae04166e9f2d6a34eb68703`.
The retained and isolated-build copies were independently checked byte-equal.

The accepted temporary file had 91 lines and SHA-256
`002c7fb1ffa02bc7cab397d04cd730d8b8f4c764f66b69f8a5bb6fa0bb3b5493`.
The actual diff contains only a license/header, the module exposition, and three
declaration docstrings. All three proof bodies, three sanity examples, imports,
and seven axiom checks are unchanged. The only import is the previously checked
`AINTLIBDrafts.YZeroCoarseConstantAxis`.

## Mathematical and API checks

| Declaration | Verified content | Hypotheses |
| --- | --- | --- |
| `borel_fstEntry_isUnit`, line 43 | `g₀₀` is a unit: the actual Borel condition gives `g₁₀ = 0`, so the unit determinant equals `g₀₀ * g₁₁`. | `NeZero N`; actual `g : ↥(borel N)` |
| `sectionAxis_zsmul_of_unit`, line 52 | The axis of `v • P` is the **positive** label reindexing by `a ↦ v * a`, followed by the original axis. | Arbitrary scheme `S`, elliptic curve `E/S`, `N`-killed section `P`, unit `v : (ZMod N)ˣ` |
| `sectionAxisSubgroup_glSmul_borel_ker`, line 70 | A Borel change of marking preserves the literal kernel ideal of the actual subgroup immersion in the same `E.E`. | `E/Spec R`, invertible `N` on the base, actual full marking `L` and Borel `g` |

The exact final equality is

```lean
(sectionAxisSubgroup R N E hinv (E.glSmul g.val L)).ι.ker =
  (sectionAxisSubgroup R N E hinv L).ι.ker
```

The first section of the pinned `glSmul g L` is
`(g₀₀.val : ℤ) • P + (g₁₀.val : ℤ) • Q`. Thus this argument uses `g` directly,
with the lower-left entry zero; it introduces no inverse matrix or action
convention change. On the component labelled `a`, the scalar lemma checks

```lean
(a.val : ℤ) • (((v : ZMod N).val : ℤ) • P) =
  ((((v : ZMod N) * a).val : ℤ) • P)
```

using scalar associativity and `val_smul_mul` under the actual `N`-killing
hypothesis. The explicitly composed constant family in lines 57–60 is a typing
repair for the coproduct API; it does not alter the positive permutation.
The reindexing map is an actual scheme isomorphism, so precomposition preserves
the kernel ideal by `Scheme.Hom.ker_comp_of_isIso`.

The generic scalar statement needs no field, domain, nontrivial base, or
`N ≥ 3` hypothesis. Base invertibility is used by the existing finite locally
free subgroup constructor. No unnecessary hypothesis was introduced.

The pinned upstream definitions checked independently were:

- AINTLIB `Moduli/GammaH.lean:125`: actual `glSmul` column convention;
  `Moduli/GammaH.lean:250`: `val_smul_mul` for a killed section.
- AINTLIB `Moduli/CoarseSpace.lean:199`: actual Borel carrier `g₁₀ = 0`.
- mathlib `CategoryTheory/Limits/Shapes/Products.lean:599`: generated
  `Sigma.ι_reindex_hom`, with positive permutation direction.
- mathlib `Algebra/Group/Units/Equiv.lean:56`: `Units.mulLeft` maps `a` to `v * a`.
- mathlib `AlgebraicGeometry/IdealSheaf/Basic.lean:744`: kernel invariance under
  precomposition by an isomorphism.

## Strict verification receipt

Pins: AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `v4.35.0-rc3`.
The named emission session 76217 exited 0. The actual log
`/private/tmp/xyin-y0-borel-axis.log` contains seven checks, each with exactly
`propext`, `Classical.choice`, and `Quot.sound`, and no warnings or errors.

The actual setup `/private/tmp/YZeroCoarseBorelAxis.setup.json` names
`AINTLIBDrafts.YZeroCoarseBorelAxis`, sets `autoImplicit = false` and
`relaxedAutoImplicit = false`, and has no plugins or dynamic libraries.
The exact compiler invocation is preserved in the paired
[verification report](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/YZeroCoarseBorelAxis.md).
Canonical artifacts were checked: `.olean` 39608 bytes, `.olean.private` 103648,
`.olean.server` 3224, `.ilean` 25793, `.ir` 1440, and `.ir.sig` 176.

All three sanity examples passed:

1. Unit `2` modulo 3 preserves the kernel of an arbitrary killed section axis.
2. The literal actual full-marking/Borel subgroup theorem instantiates at level 3.
3. Unit `2` modulo 5, with inverse `3`, satisfies the **positive morphism**
   equation itself. This checks reindexing direction more strongly than a kernel
   equality or a self-inverse unit modulo 3.

The first family-matching failure at
`/private/tmp/YZeroBorelAxisProbe.first-failure.log` is excluded, including its
staged downstream `sorryAx` output. The intermediate mathematical-green run had
a deprecated-name warning; it is separately saved at
`/private/tmp/YZeroBorelAxisProbe.kernel-green-warning.log`. The accepted final
source uses `Sigma.ι_comp_desc`, and the named final receipt is warning-free.

## Exact boundary

The equality holds for embedded subgroup ideals in the fixed ambient curve.
It does not prove literal equality of bundled `GammaZeroStructure` records,
classification of all cyclic subgroup pairs by native Borel marking classes,
or quotient-curve `j` descent. It does not produce a Weierstrass model for `E/C`
or a modular-polynomial equation. No circular classification or quotient-model
assumption occurs in the checked declarations.
