# A source-j morphism for the actual AINTLIB coarse curve

This is a source-backed implementation route, not a completed geometric identification.
The source revision checked is AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`. The external checkout was only read.

The concrete implementation is split between `AINTLIBDrafts/GeometricJ.lean` and
`AINTLIBDrafts/YZeroCoarseJ.lean`. It contains chart independence, section gluing and
naturality, actual quotient descent, base-ring compatibility, and a sanity statement
identifying the pulled-back coordinate in every actual local Weierstrass chart. These
modules are intentionally not imported by XYin, since they target AINTLIB's toolchain.
The complete generic `GeometricJ` module has now typechecked in the exact upstream
Lean/mathlib environment, without warnings. Its chart-independence, global gluing,
scheme-map naturality, base-compatibility, and full polynomial-pullback declarations
use only `propext`, `Classical.choice`, and `Quot.sound`. The final actual
`YZeroCoarseJ` module has also passed the strict pinned Lake build without new-module
warnings. Its actual source-j map, over-base triangle, every-chart coordinate formula,
and level-three complex specialization have the same three-axiom closure. The
auxiliary affine-base instance is local to the generic coarse-descent section.

## What exists already

There is no geometric `EllipticCurve.j` global section or `EllObj.jMap` in the checked
ModularCurves source. The occurrences of the classical `W.j` in `Moduli/Coarse.lean` are
classification goals whose proofs contain `sorry`. They need not be used for the first
source-j morphism.

All the geometric input needed for that first morphism is available:

| Input | Exact source declaration |
|---|---|
| Affine local Weierstrass charts, including zero and structure compatibility | `EllipticCurveGeom.atlas`, `EllipticCurve/WeierstrassAtlasBundle.lean:59` |
| Bundle one such chart | `WeierstrassAtlasData.presentation`, `EllipticCurve/InvariantDifferential.lean:107` |
| Compare charts over the same affine open | `LocalPresentation.transVC_smul`, `InvariantDifferential.lean:151` |
| Restrict a chart to a smaller affine open | `LocalPresentation.restrict`, `InvariantDifferential.lean:471` |
| Transport a chart along a pointed cartesian square | `LocalPresentation.transport`, `InvariantDifferential.lean:386` |
| Transport acts by the expected coefficient ring map | `LocalPresentation.transport_W`, `InvariantDifferential.lean:450` |
| j is unchanged by variable change | mathlib `WeierstrassCurve.variableChange_j` |
| j commutes with ring maps | mathlib `WeierstrassCurve.map_j` |
| Glue sections on an open cover | mathlib `TopCat.Sheaf.existsUnique_gluing'` |
| Check section equality on an open cover | mathlib `TopCat.Sheaf.eq_of_locally_eq'` |
| Fine full-level base is affine over the base ring | `gammaFullNaive_isAffineHom_structMap`, `Moduli/CoarseSpace.lean:112` |
| Invariant morphisms descend uniquely | `Functor.RepresentableBy.coarsePr_existsUnique_lift`, `CoarseSpace.lean:168` |

The only nontrivial chart-comparison theorem behind this route is already proved:
`pointedIso_exists_variableChange` in `EllipticCurve/Comparison.lean:172`. In particular,
no j-classification theorem and no quotient elliptic curve `E/C` theorem is needed here.

## Smallest first implementation

For the immediate application it is enough to assume that the elliptic curve's base
scheme `S` is affine. This is satisfied by `xFullNaive ... .base`. It simplifies both
gluing and the action-invariance proof, since intersections of affine opens are affine
(`IsAffineOpen.inf`), and the action maps are scheme isomorphisms, so inverse images
of affine opens are affine (`IsAffineOpen.preimage`).

Affineness here is a proof convenience, not a mathematical restriction on the
j-invariant. The intersection steps only need an affine diagonal, which is the
actual hypothesis of the pinned `IsAffineOpen.inf` API. A version over an arbitrary
scheme can instead cover each intersection by affine opens, compare the restricted
presentations there, and use sheaf separation before gluing. The retained first
implementation keeps the affine hypothesis because all its actual modular-curve
applications satisfy it; no claim of maximal generality is made for this auxiliary API.

1. Define `LocalPresentation.j` using `P.W.j` after making `P.elliptic` a local instance.
   Prove `P.j = Q.j` for presentations over the same open. Use `transVC_smul`, then
   `variableChange_j`; this is the entire presentation-independence argument.
2. Prove the two section formulas: restriction of `P.j` is `(P.restrict h).j`, and
   transport sends `P.j` to `(P.transport ...).j`. Both follow from `map_j` and
   `transport_W`; restriction also simplifies `sectionsMapLE (𝟙 S)` to restriction.
3. On the atlas opens put `s i := (G.atlas.presentation i).j`. For a pair `i,j`, use
   the affine intersection as a new chart, restrict both presentations to it, and
   apply step 1. The sections `s i` are therefore compatible. Glue to
   `jSection : Γ(S, ⊤)` with `TopCat.Sheaf.existsUnique_gluing'`.
4. Prove a useful characterization: for any local Weierstrass presentation `P` over
   an affine open `V`, the restriction of `jSection` to `V` is `P.j`. Cover `V` by
   `V ⊓ G.atlas.U i`, compare presentations there, and use sheaf separation. This
   characterization is more useful downstream than the construction's atlas-specific
   gluing equation.
5. Given `X : EllObj R`, define the ring morphism
   `R[X] →+* Γ(X.base, ⊤)` by `Polynomial.eval₂RingHom` using the structure-map pullback
   on coefficients and `jSection` for the variable. Its associated scheme morphism is
   `X.base.toSpecΓ ≫ Spec.map ... : X.base ⟶ Spec (.of (Polynomial R))`.

These steps construct an actual regular morphism from the universal fine curve's base
to the j-line. They do not merely assign a j value to its complex points.

## Invariance and the actual `YZeroCoarse`

For the Borel action, let `r := xFullNaiveRepr ...` and `φ := gammaHAut R N (borel N)`.
Each acting morphism is the base leg of the pointed cartesian `EllHom`
`(r.autMulHom (φ γ)).inv`. Its fields supply all three transport inputs:
`baseHom`, `top`, `isPullback`, and `zero_w`.

To prove invariance of `jSection`, compare an own chart on `U_i` with a transported
chart from `U_j` on `U_i ⊓ f ⁻¹ᵁ U_j`. Step 4, step 2, and presentation independence
give equality on these opens. They cover the source, so sheaf separation gives
`f.appTop.hom jSection = jSection`. Coefficients are invariant because
`f ≫ X.structMap = X.structMap` (`baseSchemeAction_over`). Polynomial extensionality
and `Scheme.toSpecΓ_naturality` then give invariance of the entire j morphism.

Finally, apply `coarsePr_existsUnique_lift`. The codomain of that descent is definitionally
the scheme used by `YZeroCoarse`, after unfolding `YZeroCoarse` and `YHCoarse`. It gives
an actual source-j morphism

```
YZeroCoarse N hN hinv ⟶ Spec (.of (Polynomial R))
```

with its pullback along the fine quotient projection equal to the universal source-j
morphism. This construction uses the actual invariant-Spec quotient, rather than a
replacement scheme whose name is `YZeroCoarse`.

## What this does and does not settle

The completed source-j descent supplies a concrete regular coordinate on the actual
coarse curve. It still leaves the second coordinate, the j of the
quotient elliptic curve `E/C`, and the identity `Φ_N(j(E), j(E/C)) = 0` to prove.
Those are mathematically new inputs; they cannot be obtained from the categorical
quotient property alone. Finiteness, birationality, and normalization of the resulting
map likewise need separate proofs.

The source-j construction does not assume that either the fine or the coarse section
ring is a domain, and it does not prove that the j coordinate is transcendental.
It is therefore valid before any connected-component or integrality argument, but
does not yet identify a function field or justify taking fractions of the actual
coarse ring. In particular, an integrality assumption on the full-level scheme should
not be inserted just to obtain a fraction-field interface.

An initial module can import `ModularCurves.EllipticCurve.InvariantDifferential` and
`ModularCurves.Moduli.CoarseSpace`; it should avoid `ModularCurves.Moduli.Coarse`.
The source project uses a newer Lean/mathlib pin than XYin. Any executable bridge must
therefore either be verified in that upstream toolchain, or carefully port the actual
dependencies before being called a kernel-checked XYin result.
