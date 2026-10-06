# Actual full-level constant axis

The retained source is `AINTLIBDrafts/YZeroCoarseConstantAxis.lean`. It constructs the literal
first-coordinate axis of a naive full-level marking on the actual elliptic curve over a
full complex scheme point. The labels are `a ↦ ![a, 0]`, and the section morphism is the
coproduct of the sections `(a.val : ℤ) • P`.

The point-image subgroup statement is proved on every test scheme, by representing its
constant-scheme points as locally constant label functions. Addition is checked on the
open pieces where both labels are constant. It requires only that `P` is killed by `N`.
This avoids an argument that checks subgroup closure only on geometric points.

The torsion factorization is through the actual `fullLevelHom`; the killing statement
uses the actual defining pullback of `E[N]`. For `N` invertible on `Spec R`, the full-level
map is the checked `fullLevelIso`. Restriction of functions to the coordinate axis is
surjective, with right inverse `f ↦ (v ↦ f (v 0))`, so the constant-axis morphism is a
closed immersion. Composition with `fullLevelIso.hom` and `torsionι` proves that the
section morphism is a closed immersion. The complex specialization uses the native
pulled-back marking `fullComplexPointLevel` and transfers `IsUnit (N : ℂ)` through
`Scheme.ΓSpecIso`.

The projection from the constant `ZMod N` scheme to `Spec R` is finite by the finite
product module `ZMod N → R`. It is flat and locally of finite presentation because each
coproduct component is the identity of the base. Its rank is computed through the same
Spec isomorphism and `Module.rankAtStalk_pi`, giving `card (ZMod N) = N`. This does not
assume that `R` is a domain or even globally nontrivial; a specific prime point supplies
the nontriviality used in the rank calculation, and an empty `Spec R` makes the rank
statement vacuous.

The checked bundle is `sectionAxisSubgroup` for an actual marking on any elliptic curve
over `Spec R` with `N` invertible. Its literal underlying scheme is the constant `ZMod N`
scheme and its immersion is `sectionAxis`. The native complex specialization is
`fullComplexPointAxisSubgroup`; its immersion equals `fullComplexPointAxis` by `rfl`.
Both versions have checked `HasRank N` and `HasKillingInt` theorems. The latter is proved
using the literal equation `sectionAxis ≫ [N] = constSchemeπ ≫ zero` from the torsion
pullback; it does not use the upstream generic rank-kills statement.

## Strict verification

The source is tested against AINTLIB commit
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, its pinned mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3` in the isolated checkout
`/private/tmp/xyin-y0-aintlib-work`. The retained local project uses Lean `v4.30.0`; these
AINTLIB integration modules are deliberately checked in the isolated pinned environment.

The strict setup comes from the library target, with `autoImplicit=false` and
`relaxedAutoImplicit=false`. The following is the literal direct invocation, run from the
isolated checkout after copying the retained source into `AINTLIBDrafts/`:

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean --setup .lake/build/ir/AINTLIBDrafts/YZeroCoarseConstantAxis.setup.json AINTLIBDrafts/YZeroCoarseConstantAxis.lean -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseConstantAxis.olean
```

Verified snapshots:

- The initial point-image and torsion layer: exit 0, zero warnings/errors, all 11 printed
  declarations depend only on `propext`, `Classical.choice`, `Quot.sound`. Receipt:
  `/private/tmp/xyin-y0-constant-axis-strict.log`.
- The closed-immersion layer: exit 0, zero warnings/errors, all 15 printed declarations
  depend only on the same three standard axioms. Receipt:
  `/private/tmp/xyin-y0-constant-axis-closed.log`.
- The independent finite/flat/lfp/rank projection fixture: exit 0, zero warnings/errors,
  all four printed declarations depend only on the same three standard axioms. Receipt:
  `/private/tmp/YZeroConstantProjectionProbe.log`.
- The retained complete subgroup bundle: exit 0, zero warnings/errors, all 28 printed
  declarations depend only on the same three standard axioms. Receipt:
  `/private/tmp/xyin-y0-constant-axis-bundle.log`.
- The subsequent named generator target rebuilt the unchanged constant-axis module in
  52 seconds, with the same 28 standard-axiom checks and zero own diagnostics. Receipt:
  `/private/tmp/xyin-y0-axis-generator.log` (the combined target exited 0, 9410 jobs).

This layer does not claim `IsCyclic` or `GammaZeroStructure`. Those native predicates
require a separate comparison with the exact-order section divisor. In particular, the
upstream geometric-to-Drinfeld bridge `Section.hasExactOrder_of_geometric` has `sorryAx`
in the pinned source and is not used here. The generic constant-rank killing theorem also
has `sorryAx`; the retained killing proof instead factors through the literal torsion
pullback.

## Checked prerequisites for the divisor comparison

The previously missing upstream target
`ModularCurves.ForMathlib.ClosedImmersionFinrankIso` was built successfully without
editing upstream source or configuration. It built the three missing modules
`SurjectiveFreeSameRank`, `SpecQuotientIso`, and `ClosedImmersionFinrankIso`; the other
dependencies were already available. The target receipt is
`/private/tmp/xyin-y0-closed-finrank.log` (exit 0, 2804 jobs).

The exact three declarations were then independently axiom-probed, with exit 0, zero
warnings/errors, and only the three standard axioms:

- `ModularCurves.isIso_of_isClosedImmersion_of_finrank_eq_isAffineBase`;
- `ModularCurves.RelEffCartierDiv.factors_sectionsDivisor`;
- `ModularCurves.RelEffCartierDiv.sectionsDivisor_degree`.

Receipt: `/private/tmp/YZeroDivisorAxisAxioms.log`. These are prerequisites for a
separate generator leaf; none of them assumes an exact-order generator or subgroup
condition in order to produce the component factorization or rank comparison.
