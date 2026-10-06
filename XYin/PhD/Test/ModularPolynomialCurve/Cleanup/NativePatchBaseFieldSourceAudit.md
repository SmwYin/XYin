# Source-only native affine patch base-field audit

This is a bounded source/API audit. No proof fixture, compiler invocation,
retained Lean edit, or new axiom-check claim is made. Exact inspected source
hashes are recorded in `/private/tmp/YZeroNativePatchBaseFieldSourceAuditHashes.json`.

## Actual chart scalar and local relative dimension

`projects/ModularCurves/ModularCurves/GroupScheme/StableCharts.lean:87–101`
defines `G.AffineChartPatch` with actual base open `P.V`, affine proofs `P.hV/P.hU`,
and `P.hover : P.U ≤ E.π ⁻¹ᵁ P.V`. Its `baseRing` is literally
`Γ(S,P.V)` (:108), its `chartRing` is `Γ(E.E,P.U)` (:111), and its
`Algebra P.baseRing P.chartRing` (:120–121) is precisely
`(E.π.appLE P.V P.U P.hover).hom.toAlgebra`.

The unconditional exact local property already appears inside the proved
retained `YZeroCoarseChartKaehlerRank.lean:50–54`:

```lean
have hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
    (algebraMap P.baseRing P.chartRing) := by
  change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
    (E.π.appLE P.V P.U P.hover).hom
  exact HasRingHomProperty.appLE (@SmoothOfRelativeDimension 1) E.π E.smooth
    ⟨P.V, P.hV⟩ ⟨P.U, P.hU⟩ P.hover
```

This uses mathlib `Smooth.lean:141–150`, associating genuine scheme
`SmoothOfRelativeDimension 1` with the **local** ring property, and
`RingHomProperties.lean:292–294` `HasRingHomProperty.appLE`. It assumes no
standard-smooth structure on the whole chart, and no subgroup freeness,
Noetherian, or étale condition. The source scalar is already literal; no scalar
transport from the original field is necessary to use it over `P.baseRing`.

## Nonempty actual base open

For `E : EllipticCurve (Spec (.of k))`, `[Field k]`, any actual point
`x ∈ P.U` supplies `P.hover hx : E.π x ∈ P.V`. Mathlib
`AlgebraicGeometry/Scheme.lean:626–627` supplies `Unique (Spec (.of k))`, through
`PrimeSpectrum.Basic.lean:399–401`. Thus this is a nonempty open of a singleton
space and `P.V = ⊤` follows by `top_unique`, transporting membership along
`Subsingleton.elim`. Alternatively use `TopologicalSpace.Opens.ext` and
`Set.Nonempty.eq_univ` (`Data/Set/Basic.lean:587–589`).

For the genuine free cover, `SubgroupQuotientGlueData.lean:47–51` defines
`G.gluePatch N hkill x` by the proved affine-patch existence theorem and supplies
`G.mem_gluePatch N hkill x`. Hence each chosen patch has a real point in its
source open, and therefore a nonempty base open. The existing killing inputs
are only those used to choose the actual patch; `free_gluePatch` is irrelevant
to this base-open argument. An arbitrary `P` may have empty `P.U`; the point or
nonemptiness premise must be kept for that generic patch API.

## Actual base-ring equivalence and field structure

Given the resulting `hVtop : P.V = ⊤`, the exact ring-category iso with the
correct variance is

```lean
(Spec (.of k)).presheaf.mapIso (eqToIso hVtop.symm).op ≪≫
  Scheme.ΓSpecIso (.of k)
```

Its source is actual `P.baseRing = Γ(Spec k,P.V)` and target is `k`.
The equality iso before `.op` is `⊤ ≅ P.V`, so contravariance gives
`Γ(P.V) ≅ Γ(⊤)`. `Scheme.ΓSpecIso` is the existing canonical ring iso
(`Scheme.lean:601–602`), and `CategoryTheory.Iso.commRingCatIsoToRingEquiv`
(`Algebra/Category/Ring/Basic.lean:710–722`) converts this composite into
`e : P.baseRing ≃+* k`.

Install a **local** field on the existing ring by
`(e.toMulEquiv.isField (Field.toIsField k)).toField`. The exact
`MulEquiv.isField` statement in `Algebra/Field/Equiv.lean:31–32` transfers
fieldhood to the source of that equivalence. `IsField.toField` in
`Algebra/Field/IsField.lean:86–92` explicitly extends the **existing Ring**,
so it preserves the source ring operations rather than using an unrelated
transported commutative-ring structure. Consequently the existing literal
`Algebra P.baseRing P.chartRing` and `hlocal` remain the same scalar map.
No unproved equality between a newly transported `k`-algebra and the curve's
actual appLE algebra is needed: apply the forthcoming local normality theorem
with the actual base ring itself as the field.

## Smallest proposed actual interfaces

The following are proposed signatures/proof contracts, not compiled declarations:

```lean
baseOpen_eq_top_of_mem (P : G.AffineChartPatch) (x : E.E) (hx : x ∈ P.U) :
  P.V = ⊤

baseRingEquivFieldOfMem (P : G.AffineChartPatch) (x : E.E) (hx : x ∈ P.U) :
  P.baseRing ≃+* k

chartRing_isIntegrallyClosed_of_mem
  (P : G.AffineChartPatch) (x : E.E) (hx : x ∈ P.U) :
  IsIntegrallyClosed P.chartRing
```

For the last, the only still separate mathematical dependency is the parent's
generic local-standard-smooth-relative-dimension-one integral-closedness
adapter. The native curve is genuinely integral over a field by
`EllipticCurve/IntegralOverField.lean:38`. Install `Nonempty P.U` from `⟨x,hx⟩`;
then mathlib `Properties.lean:241–245` supplies `IsDomain Γ(E.E,P.U)` from
`IsIntegral.component_integral`. The actual local property above and the local
base-ring field give the proposed normality adapter's exact inputs. Thus a
true `G.gluePatch N hkill x` specialization has no extra nonempty, field-base,
chart-domain, subgroup free/étale, Noetherian, model or genus assumption.
No quotient normality proof is part of this audit.
