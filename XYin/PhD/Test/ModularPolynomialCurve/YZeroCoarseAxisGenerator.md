# Native Γ₀ data from actual full complex points

The retained leaf `AINTLIBDrafts/YZeroCoarseAxisGenerator.lean` extends the checked
constant-axis bundle without modifying `YZeroCoarseConstantAxis.lean`. Its assumptions
for the cyclicity construction are an actual elliptic curve over `Spec R`, an actual
naive full-level marking, `[NeZero N]`, and `NIsInvertible (Spec R) N`. It does not
assume that `R`, the fine global section ring, or the coarse invariant ring is a domain.

## The comparison

The constant axis uses `(a.val : ℤ) • P` for `a : ZMod N`. The native order divisor
uses `((i.val : ℤ) + 1) • P` for `i : Fin N`. The index
`⟨(a - 1).val, ZMod.val_lt (a - 1)⟩` gives equal coefficients in `ZMod N`, so the
already available equation `N • P = 0` identifies the two sections. This is essential
at `a = 0`, where the integer coefficients are `N` and `0`.

`factors_sectionsDivisor` then factors each component of the constant scheme through
the actual order divisor. Their coproduct is `orderDivisorAxisLift`, with literal
immersion and base triangles. For a full marking with `N` invertible, the axis is a
closed immersion. The lift to the divisor is therefore also a closed immersion; its
source and target are finite, flat, locally finitely presented, and both have rank
`N`. The checked upstream same-rank closed-immersion criterion makes this lift an
isomorphism.

`Scheme.Hom.ker_comp_of_isIso` and `IdealSheafData.ker_subschemeι` identify the native
axis bundle's divisor ideal with `P.orderDivisor`. Points factoring through either
immersion correspond by composition with the lift and its inverse on every test
scheme. The checked axis point-image subgroup thus proves the native
`P.HasExactOrder E N`.

For native `IsCyclic`, the fppf cover is the identity of `Spec R`. Its generator is the
literal section on `E.baseChange (𝟙 _)` obtained by `Point.asSection` and `Point.pull`.
The checked `HasExactOrder.baseChange` and `orderDivisor_baseChange` provide precisely
the generator and ideal equality consumed by `isCyclic_of_generator`.

The proof does not use `hasExactOrder_of_geometric`, the sorried geometric/fppf
comparison, or the generic Deligne rank-kills statement. The exact-order predicate is
proved through the actual divisor and every-test-scheme subgroup condition.

## Native interfaces

- `sectionAxisGammaZeroStructure` is a native `EllipticCurve.GammaZeroStructure N`
  built with `GammaZeroStructure.ofIsCyclic` over `Spec R`.
- `fullComplexPointGammaZeroStructure` specializes it to the literal elliptic object
  and full marking pulled back from an actual full complex scheme point.
- The subgroup and immersion are equal by `rfl` to the previously checked constant
  axis bundle and section axis; the record supplies the native rank and cyclicity.
- `yZeroComplexSchemePoint_lifts_withGammaZeroStructure` gives, for every actual
  coarse complex point `p`, an actual full point `q` with literal projection `q ↦ p`
  and `Nonempty` of the native Γ₀ datum on the curve pulled back at `q`.

The last theorem asserts existence on a lift. It does not assert independence of the
lift, descent of a canonical Γ₀ datum, classification of native Γ₀ curves by coarse
points, existence of the quotient elliptic curve, or the modular-polynomial equation.
The source-j equality with the actual pulled-back Weierstrass model is already provided
separately by the fine complex-point layer.

## Verification receipts

The environment is the isolated AINTLIB checkout
`/private/tmp/xyin-y0-aintlib-work`, pinned to commit
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
The local XYin project remains on its existing Lean `v4.30.0` setup.

The temporary strict compiler fixtures passed with zero warnings/errors and only
`propext`, `Classical.choice`, and `Quot.sound`:

- Divisor lift/isomorphism: six declarations,
  `/private/tmp/YZeroDivisorAxisProbe.log`.
- Ideal equality and native exact order: eight own declarations plus the five exact
  kernel/base-change/generator prerequisites,
  `/private/tmp/YZeroDivisorAxisExactOrderProbe.log`.
- Native identity-cover cyclicity: nine own declarations plus the same five exact
  prerequisites, `/private/tmp/YZeroDivisorAxisCyclicProbe.log`.

The retained strict library build passed with exit 0 (9410 jobs; the new leaf took
67 seconds). It has zero own warnings/errors, all 26 printed checks depend only on the
same three standard axioms, and all four `N = 3` sanity examples pass. The unchanged
constant-axis module also rebuilt successfully in 52 seconds, with its 28 standard-
axiom checks. Its literal invocation from the isolated checkout is:

```sh
ELAN_HOME=/private/tmp/xyin-y0-elan /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lake build AINTLIBDrafts.YZeroCoarseAxisGenerator
```

Retained build receipt: `/private/tmp/xyin-y0-axis-generator.log`. The target has
`autoImplicit=false` and `relaxedAutoImplicit=false`; it prints the 21 retained own
declarations and the five primitive prerequisites for transitive axiom inspection.

The checked 307-line retained source has SHA256
`d102529f57067ea5c5bb5eb2478551c2097c32a102cea007284aa233dd43b31f`.
