# Source-only actual native stalk integral-closed construction

No new proof fixture, compiler, source edit, or kernel-check claim for a stalk
normality theorem is made here. Seven actual source hashes are recorded in
`/private/tmp/YZeroNativeStalkNormalitySourceAuditHashes.json`.

The proposed smallest native interface can first keep an actual affine patch P
and a true membership `hx : x ∈ P.U`:

```lean
stalk_isIntegrallyClosed_of_mem (P : G.AffineChartPatch)
  (x : E.E) (hx : x ∈ P.U) : IsIntegrallyClosed (E.E.presheaf.stalk x)
```

For the desired actual cover at any x, choose `P := G.gluePatch N hkill x` and
`hx := G.mem_gluePatch N hkill x`. The approved `NativeChartIntegrallyClosed`
wrapper gives `IsIntegrallyClosed P.chartRing`. Nonemptiness from `⟨x,hx⟩` and
actual native E integrality again give `IsDomain P.chartRing`; this is needed
for the localization preservation API and is not a new assumed domain.

Install the actual germ scalar, rather than an arbitrary algebra:

```lean
let : Algebra P.chartRing (E.E.presheaf.stalk x) :=
  E.E.presheaf.algebra_section_stalk ⟨x, hx⟩
```

`Topology/Sheaves/CommRingCat.lean:274–281` defines this algebra precisely as
`(E.E.presheaf.germ P.U x hx).hom.toAlgebra`. Its `stalk_open_algebraMap`
identity is `rfl`, hence this is the actual section-to-stalk ring homomorphism.

Set `p := (P.hU.primeIdealOf ⟨x,hx⟩).asIdeal`. The prime is the actual image of
the point under the affine chart's `isoSpec.hom`
(`AlgebraicGeometry/AffineScheme.lean:771–773`). The exact
`P.hU.isLocalization_stalk ⟨x,hx⟩` theorem (:830–837) supplies

```lean
IsLocalization.AtPrime (E.E.presheaf.stalk x) p
```

for that same germ algebra. Its source primed theorem (:814–828) explicitly
fixes `TopCat.Presheaf.algebra_section_stalk` before transporting the real Spec
structure-sheaf stalk localization. Thus the API reaches the stalk of E itself,
not only the stalk of the restricted open scheme, and no independent scalar
compatibility premise or restriction-stalk iso is needed.

`IsLocalization.AtPrime` is literally `IsLocalization p.primeCompl`
(`Localization/AtPrime/Basic.lean:48–51`). Since P.chartRing is a domain and p is
prime, `Ideal.primeCompl_le_nonZeroDivisors` in `Ideal/Operations.lean:1409–1411`
provides the denominator submonoid inclusion. Finally apply the exact
`isIntegrallyClosed_of_isLocalization (E.E.presheaf.stalk x) p.primeCompl
  p.primeCompl_le_nonZeroDivisors`
from `IntegralClosure/IntegrallyClosed.lean:380–397`. It requires only actual
source integral-closedness/domain and the already installed genuine
localization structure. It does not require target-domain as an extra premise,
Noetherian, maximal/closed point, DVR, relative dimension or subgroup étale.

An optional more general first helper is the same localization argument for
any `IsAffineOpen U` of any scheme, with only domain and integral-closed section
ring inputs and `x : U`. Native source normality then supplies those inputs.
This is a generality proposal, not a proved declaration. The native chosen-patch
route is already source-complete and adds no assumptions beyond the existing
actual N/nonzero/killing datum used to select that patch. No quotient stalk or
genus/model assertion is included.
