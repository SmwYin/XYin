# Source-only normality audit for the native subgroup quotient

This is a bounded read-only audit of pinned AINTLIB and mathlib sources. No Lean
proof, compiler invocation, new hypothesis record or retained Lean edit was made.
Exact source hashes are saved in
`/private/tmp/YZeroQuotientNormalitySourceAuditHashes.json`. The source statements
below have not received fresh `#print axioms` verification in this audit.

## What exists for the native curve

`EllipticCurve/IntegralOverField.lean:38` supplies
`ModularCurves.EllipticCurve.isIntegral_of_field` for an actual
`E : EllipticCurve (Spec k)` over an arbitrary field. Mathlib
`AlgebraicGeometry/Properties.lean:241` then gives `IsDomain Γ(E.E, U)` for every
**nonempty** open `U`. In particular, each actual chosen `gluePatch` is nonempty
by `mem_gluePatch`. An arbitrary affine patch should not silently get this
domain instance when its open might be empty.

Searches of the pinned native elliptic-curve, subgroup and algebraic-geometry
sources found no scheme class named `IsNormal`, nor a direct native-curve theorem
making every nonempty affine section ring integrally closed or Dedekind. Relative
normalization exists in mathlib; that does not provide the missing normality
property or its native elliptic-curve instance.

There are two concrete algebraic inputs:

1. `ForMathlib/StandardSmoothMaximalDVR.lean:43`:
   `ModularCurves.isDiscreteValuationRing_localizationAtPrime_of_isStandardSmooth`
   takes an arbitrary field `k`, an algebra `A`, a **global** instance
   `Algebra.IsStandardSmoothOfRelativeDimension 1 k A`, and a maximal ideal `q`.
   It returns both `IsDomain (Localization.AtPrime q)` and a DVR instance. No
   `IsAlgClosed k` or initial domain assumption is required by this statement.
2. `ForMathlib/StandardSmoothIntegrallyClosed.lean:46`:
   `isIntegrallyClosed_of_isStandardSmoothOfRelativeDimension_one` takes the
   same global standard relative dimension one instance plus `IsDomain A`, and
   returns `IsIntegrallyClosed A`. It uses the previous theorem and mathlib's
   `IsIntegrallyClosed.of_localization_maximal`.

Both files have actual proofs and no literal `sorry` in their inspected bodies.
Their exact transitive axiom dependencies must be checked before a new proof
consumes them. The actual arbitrary source patch provides a **Locally** standard
relative dimension one condition, not a global standard-smooth instance; the
stronger premise must not be supplied without a localization adapter.

The vendored coordinate-model route also has a concrete statement:
`Vendored/RiemannRoch/EllipticCurve/Dedekind.lean:349`,
`WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain`, and its instance at
`:357`, for `W : WeierstrassCurve.Affine k` over a field with `[W.IsElliptic]`.
It proves `IsDedekindDomain W.CoordinateRing`. This is a genuine Weierstrass affine
coordinate ring, not automatically every native `Γ(E.E,U)`. Transport through the
actual model/affine-open dictionary, and treatment of a chart meeting infinity,
would still be needed. The inspected theorem body has no literal `sorry`; no
kernel-clean claim is made before its dependencies are checked.

## Exact first missing source-normality adapter

A useful small generic statement, not yet proved here, is:

```lean
theorem isIntegrallyClosed_of_locally_standardSmoothRelDim_one
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap k A)) : IsIntegrallyClosed A
```

The intended proof is genuinely local: choose a standard localization avoiding
each maximal ideal, use the existing standard-smooth DVR/integral-closed theorem,
then transport to the localization at that maximal ideal. Mathlib
`RingTheory/LocalProperties/IntegrallyClosed.lean:69` provides the final
`IsIntegrallyClosed.of_localization_maximal` inference. Alternatively, its `:48`
localization-submonoid intersection criterion can join a covering family of
integrally closed standard localizations, once their intersection is proved to
be the base ring. The scalar/localization equations remain required proof work.

Applying this to a native curve affine ring also requires its actual field
scalar map and the actual relative-dimension-one `appLE` property. For chosen
patches over `Spec k`, the base open is nonempty and hence top, so its section
ring is genuinely isomorphic to `k`. This must be proved/transported rather than
assuming `P.baseRing = k` definitionally.

## Faithfully flat descent to the raw quotient

There is no packaged faithfully-flat descent of `IsIntegrallyClosed` in the
searched pinned mathlib/AINTLIB ring APIs. It can nevertheless be reduced to
concrete existing primitives, without an étale or quotient-model assumption.
A suitable next generic statement is:

```lean
theorem isIntegrallyClosed_of_faithfullyFlat
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain B] [Module.FaithfullyFlat A B] [IsIntegrallyClosed B] :
    IsIntegrallyClosed A
```

The source-backed elementary route is:

- Faithfully flatness supplies `FaithfulSMul` and hence the injective scalar map;
  use this to derive `IsDomain A` from the genuine source domain.
- Extend the inclusion to fraction fields with `IsFractionRing.map`
  (`Localization/FractionRing.lean:417`). Map a monic equation with
  `IsIntegral.map_of_comp_eq` (`IntegralClosure/IsIntegral/Basic.lean:143`).
- Normality of `B` puts the mapped integral fraction in `B`, using
  `isIntegrallyClosed_iff` (`IntegralClosure/IntegrallyClosed.lean:125`).
- Write the original fraction as `a / s`, `s ≠ 0`, using
  `IsFractionRing.div_surjective` (`FractionRing.lean:261`). The equality in `B`
  shows the image of `a` belongs to the ideal generated by the image of `s`.
- `Ideal.comap_map_eq_self_of_faithfullyFlat`
  (`Flat/FaithfullyFlat/Algebra.lean:107`) contracts that ideal back to `(s)`.
  `Ideal.map_span` (`Ideal/Maps.lean:185`) and `Ideal.mem_span_singleton`
  (`Ideal/Span.lean:180`) give `s ∣ a` in `A`. Thus the original fraction was
  already in `A`.

This descent needs no module finiteness; the actual finite-flat quotient provides
more than is necessary. For an actual free stable patch, the genuine Hopf datum
already gives faithfully-flatness of canonical coinvariants `C → B`. Once actual
`B` normality is proved, this generic lemma would yield `IsIntegrallyClosed C`.
The existing `P.quotientCoinvariantsAlgEquiv`/carrier ring equivalence then
transports it to the literal raw quotient ring using `IsIntegrallyClosed.of_equiv`
(`IntegrallyClosed.lean:261`). This avoids asserting a raw normality premise.

The actual global quotient cover can then be described as having integrally
closed nonempty affine chart rings. Packaging an intrinsic scheme-normality class
is additional API work, not an existing clean inference. No genus, DVR property
for arbitrary raw quotient stalks, Dedekind structure for every quotient chart,
elliptic model or target-j assertion follows merely by naming this local ring
descent route. Those conclusions require their own source-backed adapters.
