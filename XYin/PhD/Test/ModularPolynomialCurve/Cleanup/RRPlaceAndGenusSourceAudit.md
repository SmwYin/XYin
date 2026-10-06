# RR places, local valuations and the remaining genus/model comparison

This is a bounded **source-only audit** of the pinned AINTLIB and mathlib sources,
performed on 2026-10-04. No new proof, compiler run or transitive-axiom check belongs
to this audit. An absence below means no matching API was found in the inspected
pinned source and search scope; it is not a claim about future releases.

The worktree is `/private/tmp/xyin-y0-aintlib-work`, with AINTLIB revision
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17` and mathlib revision
`300d0e535721bc098547106fc297d8ba2a63f6bb`. Existing retained work already supplies
the actual quotient's integral function fields, finite degree, independent geometric
base-field scalars, and the all-point equality of maximal ideals under the actual
quotient stalk map. These are inputs to a possible future comparison, not a completed
RR place dictionary, Riemann–Hurwitz theorem or quotient Weierstrass model.

## 1. The intrinsic place interface

`Vendored/RiemannRoch/Place.lean:206` defines `FunctionField.Place k K`, for fields
`k`, `K` with `Algebra k K`, as a valuation subring of `K` with:

- `ne_top`: the valuation subring is not all of `K`;
- `triv_on_k`: every `algebraMap k K c` belongs to it;
- `isDiscrete`: a nonempty ordered multiplicative equivalence from its value group
  to `ℤᵐ⁰`.

This definition does not require a chosen rational-function chart or a full-constant
field assumption. The normalized valuation is `Place.valuation` at line 247;
`Place.valuationSubring_valuation` at 262 identifies its valuation ring, and
`Place.degree` at 303 is the finrank of its residue field over `k`.

`PlaceEquiv.lean:448` gives `FunctionField.chartToPlace : PlaceA k K ≃ Place k K`.
Its input is the two integral-closure charts of an already chosen `k(X)` presentation.
It is not a dictionary between scheme points and places. The exact normalized
valuation formula is `FunctionField.placeValuation_eq` at 462.

The only restriction API found in this RR layer is
`FunctionField.Place.restrict` (`PlaceEquiv.lean:214`): it restricts a place to the
already chosen `RatFunc k` subfield. `restrict_isNontrivial` at 226 uses algebraicity
of the extension; `restrict_classification` at 244 uses the rational-function
valuation classification. No generic `Place.comap` for an arbitrary finite field
embedding, and no scheme-point-to-`Place` constructor, was found.

Mathlib does supply `ValuationSubring.comap` (`ValuationSubring.lean:854`) and its
membership/composition lemmas. That construction alone does not prove the
nontriviality and discreteness fields required by an RR place.

## 2. The smallest genuine closed-point-to-place route

The first missing scheme adapter can be proved without a new algebraic DVR theorem.
For `π : X ⟶ Spec k`, `[SmoothOfRelativeDimension 1 π]`, and a point `x` with
`IsClosed {x}`, the following existing source APIs give a concrete route:

1. `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension`
   (`Morphisms/Smooth.lean:128`) gives a standard-smooth affine source chart around
   `x` over an affine base open. Since this base open contains `π x`, and `Spec k`
   has one point, the base open equals `⊤`. Transporting by `Scheme.ΓSpecIso` gives
   the actual chart algebra over `k`, not an assumed standard-smooth chart.
2. `IsAffineOpen.primeIdealOf_isMaximal_of_isClosed`
   (`AffineScheme.lean:801`) proves that the chart prime corresponding to `x` is
   genuinely maximal.
3. `ModularCurves.isDiscreteValuationRing_localizationAtPrime_of_isStandardSmooth`
   (`ForMathlib/StandardSmoothMaximalDVR.lean:45`) states, for a standard-smooth
   relative-dimension-one algebra `A` over any field `k` and a maximal ideal `q`,
   `∃ hd : IsDomain (Localization.AtPrime q),
   IsDiscreteValuationRing (Localization.AtPrime q)`.
4. `IsAffineOpen.isLocalization_stalk` (`AffineScheme.lean:830`) identifies the
   literal scheme stalk with a localization of the actual section ring at that
   prime. The canonical localization equivalence transfers the paired domain/DVR
   output to the stalk. Alternatively, `Scheme.Opens.stalkIso` and
   `Spec.stalkIso` give explicit stalk isomorphisms.

This route should yield a **closed-point** stalk DVR interface without presupposing
that the whole scheme is integral. The generic stalk of an integral curve is a
field, so an all-point DVR statement would be incorrect.

Once a literal stalk `A = X.presheaf.stalk x` is a DVR and `X` is integral, mathlib
already gives `Scheme.stalkFunctionFieldAlgebra` (`FunctionField.lean:81`),
`IsFractionRing A X.functionField` (163), and the stalk domain instance (178).
`IsDiscreteValuationRing.maximalIdeal` (DVR valuation file:41),
`isRankOneDiscrete` (46), `map_algebraMap_eq_valuationSubring` (134), and
`equivValuationSubring` (146) then construct the actual non-top discrete valuation
subring of the literal function field.

The constants condition must use independent geometric scalars: take
`ΓSpecIso.inv`, then `π.appTop`, then the germ at `x`. The equality
`Scheme.algebraMap_germ_eq_germToFunctionField` (`FunctionField.lean:95`) shows that
the image in the function field is the retained independently defined `κπ`.
Defining constants by a previously chosen field equivalence would not establish
this comparison.

Constructing these places is still less than a bijection between all closed points
and all intrinsic RR places. The reverse direction needs a centre theorem and the
actual proper/separated curve hypotheses, with residue-field compatibility.

## 3. Actual map compatibility and ramification

For a dominant map of integral schemes `f : X ⟶ Y`, the minimal local comparison is
the literal square

```text
f.functionFieldMap.hom ∘ algebraMap (stalk Y (f x)) Y.functionField
  = algebraMap (stalk X x) X.functionField ∘ (f.stalkMap x).hom.
```

This follows from `Scheme.Hom.stalkSpecializes_stalkMap`
(`Scheme.lean:923`) at the generic-point specialization to `x`, together with
`genericPoint_eq_of_isDominant` from native `ForMathlib/DominantFunctionField.lean`.
It supplies genuine scalar towers for the actual stalk map and native field map;
it should be packaged before invoking a valuation comparison.

Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`
(`NumberTheory/RamificationInertia/Valuation.lean:56`) states

```text
v.valuation K z ^ w.asIdeal.ramificationIdx A
  = w.valuation L (algebraMap K L z).
```

Its assumptions include actual Dedekind domains `A`, `B`, torsion-freeness of `B`
over `A`, the two fraction-field structures, scalar towers and the lies-over
relation. DVR stalks satisfy the relevant one-dimensional domain properties, but
the actual field/stalk square must still install the intended scalar structures.

`Ideal.ramificationIdx_eq_one`
(`RingTheory/RamificationInertia/Ramification.lean:71`) is a smaller local input:
for a prime `q`, essentially finite type algebra and `Algebra.IsUnramifiedAt R q`,
it proves the new localized-length ramification index equals one. Its proof uses
`Algebra.FormallyUnramified.map_maximalIdeal`. Current FU/LFT stalk evidence can
support this input without first proving a DVR statement. That alone is not an
unramified-place theorem, normalized-valuation formula or genus comparison.

## 4. Riemann–Hurwitz is a separate gap

`Vendored/RiemannRoch/Genus/Ramification.lean:357` proves only

```text
Chart.deg k K (polarDivisor k K (XK k K)) ≤ Module.finrank (RatFunc k) K.
```

This is the ramification half of the pole bound in Stichtenoth 1.4.11, using the
ramification/inertia fundamental identity at infinity. It is not Riemann–Hurwitz
for two finite separable function fields.

`CoordinateFree/RiemannRoch.lean:285` gives Riemann–Roch, and `deg_canonical` at 302
gives `deg W = 2g - 2`. The theorem context includes the rational-function chart
algebras and towers, `FunctionField k K`, separability over `RatFunc k`, and
`IsFullConstantField k K`. No canonical-divisor pullback/different formula across
an extension, or unramified-extension genus comparison, was found.

The source search covered all vendored RR files, the ModularCurves/HasseWeil
projects, mathlib algebraic geometry and ring theory, and the native mathlib
function-field file, with explicit Riemann–Hurwitz and genus/extension/unramified
patterns. No matching theorem was found in that scope. A future proof through RH
therefore needs actual place restriction/lifting, valuation and residue-degree
compatibility, divisor/differential comparison, and a genuine RH theorem (or an
independent cohomological genus comparison). Finite generic separability and
all-point maximal-ideal equality are valuable inputs, but do not replace it.

## 5. Genus one does not yet construct the native quotient model

`CoordinateFree/EllipticCurve.lean` begins with an existing `WeierstrassCurve.Affine`
`W` satisfying `W.IsElliptic`. `infinityPlace` (37), `placeOfPoint` (41), the
degree-one-place dictionary (61), and `genus_eq_one` (88) all have this model input.
They prove properties of an already given Weierstrass coordinate fraction field;
they do not construct a Weierstrass model from a generic genus-one field/scheme.

`EllipticCurve/Basic.lean:28` explicitly records genus-one ⇒ locally Weierstrass as
the deferred `T-W-cmp` comparison. Its `FibrewiseElliptic` predicate is itself a
pointed isomorphism to an existing Weierstrass model, not an RR genus predicate.
The same source-scoped searches found no converse constructor.

Consequently, even a future proof that the raw quotient function field has genus
one would leave the model construction/pointed scheme comparison to prove. The
known three `NIsogeny.lean` quotient-model `sorry` gates are not used by this route.

## 6. Source provenance and limits

The inspected key RR files and `StandardSmoothMaximalDVR.lean` contain no literal
`sorry`, `admit`, `axiom` or `opaque` declaration found by the bounded search.
This observation is **not** a transitive axiom receipt. No new kernel-check claim
is made here. Every hash below was recomputed directly from the pinned worktree.

Paths in this first table are relative to
`projects/ModularCurves/ModularCurves/`:

| Source | SHA-256 |
|---|---|
| `Vendored/RiemannRoch/Place.lean` | `46a453beeec7e5d70829cea81a5dd2d9f4e8dc4665a0a3778542a43e70a6f6a7` |
| `Vendored/RiemannRoch/PlaceEquiv.lean` | `0cb31141a93ab647e33bc141054731e0c3463a81fe6560a20a98b88f7508ad1d` |
| `Vendored/RiemannRoch/Genus/Ramification.lean` | `7e26a74b4334506414403491f5cd3b40ad8c918943063ffedd56ac0cede7ee95` |
| `Vendored/RiemannRoch/CoordinateFree/RiemannRoch.lean` | `ebed1b23bd52099c73a508462e3870df97e221d52779230c72b3f35a6aa1f07a` |
| `Vendored/RiemannRoch/CoordinateFree/EllipticCurve.lean` | `0cb78da0b489f7a0ca7597a5a26df39e36fe39953fce7b91afab01eaf79bbf24` |
| `ForMathlib/StandardSmoothMaximalDVR.lean` | `bc4540857ce551134f34b3ca0e9e537417bd3243b2fded3ba30c1fc2a63de5da` |
| `ForMathlib/DominantFunctionField.lean` | `801809792bc1fce93d82dfaf144f4949d36a2f524f9fc4b952fccd31265c85f2` |
| `EllipticCurve/Basic.lean` | `23629e5ef3808f97fbbd347b10a49909d809e0428435252c6a921a5ba0074108` |

Paths in the next table are relative to `.lake/packages/mathlib/Mathlib/`:

| Source | SHA-256 |
|---|---|
| `AlgebraicGeometry/FunctionField.lean` | `cb75548259bfb9b3a5affcef0959941d6ca4fc58a9f8e86a5c7b1eb00d617bee` |
| `AlgebraicGeometry/Scheme.lean` | `57baffd07501f10889ded1493b7e8a912dadfb92eda87cc3c4e25ca0af7cfc67` |
| `AlgebraicGeometry/AffineScheme.lean` | `9c1e33d156ec1cdc081e2ac6d6d1d836f0c905fc9a5d4de6069d4b9890afcf90` |
| `AlgebraicGeometry/Morphisms/Smooth.lean` | `982bb7793ef714c0a3dcfcb93eab0dbeba05ff64e70b7b1be71489294ecb2300` |
| `RingTheory/Valuation/Discrete/IsDiscreteValuationRing.lean` | `7ad9f814ba1259364a88feb3211cfe04e0a0d7b2e808773cb6ee00fcbf76f8f7` |
| `RingTheory/Valuation/ValuationSubring.lean` | `939ea2c91d6dc26159a79c431794f65ba04d9136ba6cd6589d6cd3bc21e91bcb` |
| `NumberTheory/RamificationInertia/Valuation.lean` | `53ed30f1b012f1bb4cc79fba90350e80dc85ba7094a35c04dba7db7b783e7cec` |
| `RingTheory/RamificationInertia/Ramification.lean` | `3dc8547ddee8f6848cdbff118a5832e458c808a094c4927ac6f3ee48204cd87c` |
