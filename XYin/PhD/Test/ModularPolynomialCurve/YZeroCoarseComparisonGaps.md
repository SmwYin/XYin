# Comparing the actual `YZeroCoarse` with the modular-polynomial model

Source audit: 2026-10-04. AINTLIB is fixed at
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`; its mathlib is fixed at
`300d0e535721bc098547106fc297d8ba2a63f6bb`. This audit is based on the actual
source files, not on the project descriptions or historical build receipts.
No Lean theorem asserting the missing comparison has been introduced here.

## The precise next mathematical input

The modular-polynomial plane model in this directory uses

```lean
(Cox.modularPolynomialC N).evalEval sourceJ targetJ = 0
```

Its first coordinate is the j of the source curve. To obtain a morphism from the
actual AINTLIB `YZeroCoarse`, one needs two regular functions on the fine full-level
base: the j of the universal elliptic curve and the j of its quotient by the
cyclic subgroup picked out by the full-level marking. Both must be invariant
under the Borel action. The missing equation is an equation between those actual
sections; it cannot be supplied by assigning unrelated analytic j-pairs to points.

The source-j construction and descent can be done without uniformization; see
`YZeroCoarseJRoute.md`. The quotient-j construction and its modular-polynomial
identity require additional mathematical inputs, separated below.

## What the local Cox result actually says

`Cox.theorem_11_23`, in
`XYin/PhD/Cox/CyclicSublattice/Classification.lean:198`, proves

```lean
((Cox.modularPolynomial N).map
  (Polynomial.mapRingHom (Int.castRingHom ℂ))).evalEval v u = 0 ↔
  ∃ L : PeriodPair, ∃ S : PeriodPair.CyclicSublattice L N,
    u = S.j ∧ v = L.j
```

Thus it classifies cyclic index-N inclusions of **actual complex lattices**.
`PeriodPair.CyclicSublattice` carries a submodule of the period lattice, its index,
and cyclicity of the quotient. It does not carry an elliptic scheme, an AINTLIB
`EllObj`, or a scheme isogeny.

For a cyclic isogeny `E → E/C`, the analytic lattices would have the orientation
`Λ ⊆ Λ′`, with source `ℂ/Λ`, target `ℂ/Λ′`, and cyclic group `Λ′/Λ` of order N.
Using `L = Λ′` and `S = Λ`, the displayed theorem first gives
`Φ.evalEval targetJ sourceJ = 0`. The plane model uses the reversed coordinates.
This is harmless, but it should be handled explicitly: the existing
`Cox.modularPolynomial_map_complex_zero_swap` in `Cox/Arithmetic.lean:58`
reverses the zero relation. No new symmetry assumption is needed.

The following local inputs are already proved and useful:

- `UpperHalfPlane.j_surjective` and `j_eq_periodPair_j` in `Cox/LatticeJ.lean`;
- `PeriodPair.discriminant_ne_zero` and `j_eq_iff_homothetic` there;
- `Cox.cyclicSublatticeEquivCoxMatrixOfPeriodPair`,
  `modularPolynomialC_zero_iff_normalizedCyclicSublattice`, and `theorem_11_23`;
- the independent plane ring, scheme, and function-field comparison in this
  directory.

None of these inputs identifies the lattice of an arbitrary geometric elliptic
curve together with its given subgroup C.

## The quotient elliptic curve still has upstream proof gaps

AINTLIB has a genuine scheme quotient with a universal property:

- `FiniteLocallyFreeSubgroup.quotient`, `quotientS`, `quotientπ`;
- `quotientπ_over`, `quotientπ_isInvariant`, `quotient_lift`;
- all are in `GroupScheme/SubgroupQuotient.lean:51–90` and require
  `G.HasKillingInt`.

The quotient **elliptic curve** used to define quotient-j is a further upgrade.
At the pinned main revision, `GroupScheme/NIsogeny.lean` still contains these
direct, theorem-level `sorry`s:

| Declaration | Source line | Missing content |
|---|---:|---|
| `quotient_smoothOfRelativeDimension` | 2957 | Smooth relative curve structure on E/G |
| `quotient_isProper` | 2963 | Properness over the original base |
| `quotient_locallyWeierstrass` | 2971 | Local projective Weierstrass presentations |
| `pointMap_eq_zero_iff` | 3132 | Forward half of the kernel identification |
| `quotientHom_finite` | 3151 | Finiteness of the quotient isogeny |
| `quotientHom_flat` | 3156 | Flatness of the quotient isogeny |
| `quotientHom_finrank` | 3162 | Degree equals subgroup rank |

`quotientCurveGeom` uses the first three fields directly, and `quotientCurve` at
2994 enriches that record with its atlas-derived group law. Consequently, using
this `quotientCurve` as the target of the new j construction without repairing
those inputs is a real dependency on `sorryAx`; the fact that the definition has
no literal `sorry` in its own body does not avoid that dependency.

For the intended characteristic-zero application, a complete theorem about
arbitrary finite locally free subgroups in mixed characteristic is stronger than
necessary. A targeted construction for a cyclic subgroup of E[N] over a
characteristic-zero base can potentially use its finite étale translation action.
The killing-integer proof should come from its inclusion in E[N], rather than
requiring the still open general Deligne order-kills-group theorem. This is a
possible honest specialization, not an already available quotient-curve proof.

## There is no existing complex isogeny/lattice bridge

The pinned `ModularCurves` source contains no use of `PeriodPair` linking it to
`EllipticCurve` or `EllObj`. Its analytic planning file explicitly records this
gap:

[`ModularCurve/IrreducibilityScoping.lean:42`](https://github.com/CBirkbeck/AINTLIB/blob/ab1451487da02cd4483d0e2cdb2cc9e44bbbac17/projects/ModularCurves/ModularCurves/ModularCurve/IrreducibilityScoping.lean#L42)
lists the transcendental identification `(Y ⊗ ℂ)^an ≅ ℍ/Γ̃` among the missing
infrastructure. The existing LeanModularForms j theorem classifies orbits in the
upper half-plane; it does not classify geometric elliptic schemes with level
structure.

The pinned mathlib `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` provides
the Weierstrass ℘ function, periodicity, meromorphy, and
`PeriodPair.derivWeierstrassP_sq`. Its endpoint is the differential equation

```text
℘′(z)^2 = 4 ℘(z)^3 − g₂ ℘(z) − g₃.
```

It does not provide the group isomorphism from `ℂ/Λ` to the points of its
Weierstrass cubic, or a classification of geometric finite cyclic isogenies by
lattice inclusions. In particular, the differential equation alone establishes
that an explicit pair of coordinates satisfies a cubic equation; it does not
prove surjectivity, identify fibres modulo Λ, prove the addition law, or
identify a prescribed algebraic isogeny.

There is a smaller algebraic comparison that can be obtained without a full
modular-curve analytification theory. Over ℂ, an AINTLIB elliptic curve has a
projective Weierstrass presentation by its `LocallyWeierstrass` field. Define the
lattice cubic with coefficients `a₁=a₂=a₃=0`, `a₄=−g₂/4`, `a₆=−g₃/4`.
The local discriminant result makes it elliptic, and a direct computation gives
its algebraic j equal to `PeriodPair.j`. Then local j-surjectivity and mathlib's
`WeierstrassCurve.exists_variableChange_of_j_eq` provide an isomorphism of
Weierstrass models.

That argument can match the **underlying curve** to a lattice model. It still
does not transport C to a quotient of period lattices: an algebraic j value
does not select, or classify, the given cyclic subgroup. Applying j-surjectivity
separately to E and E/C would produce two unrelated lattices and would not prove
the modular-polynomial relation.

The statements `jLine_coarse_points` and `jLine_coarse_points_j` in
`Moduli/Coarse.lean:86–96` are still `sorry`-backed. They cannot be substituted for
the missing subgroup/isogeny compatibility theorem either.

## A checked descent shortcut that does not apply to the translation quotient

`ForMathlib/QuotientCurveModel.lean:334` has a genuine
`exists_descended_model_of_curveActionFamily` theorem, but its quotient is a
different construction. It descends a **family over a base with a free group
action**. Its hypotheses include zero equivariance and a free action on the
coefficient ring; its resulting model becomes isomorphic to the original model
after base change. `Moduli/EngineDescentCore.lean:589` uses this for
`locallyWeierstrass_quotientπ` of that family.

Our subgroup quotient is by translations within the elliptic curve over the
same base. `GroupScheme/TranslationBySection.lean:40,81` constructs those
translations in `Over S`: the base map is identity and translation by P sends
zero to P. A nonzero translation therefore fails the zero-equivariance
hypothesis. The structure-map compatibility also forces any proposed base
action to be identity: precompose its π-equivariance equation with the zero
section and use zero≫π=id. Moving the chosen zero cannot create a fixed point
for a nonzero translation. Thus this family-descent theorem does not prove the
translation quotient's missing Weierstrass presentation.

There is another proved construction in
`EllipticCurve/PoleSheafWeierstrassComparison.lean:114`: Cartier-generator and
pole-basis data yield a local Weierstrass presentation. Its additional
`FibrewiseElliptic` hypothesis is defined at `EllipticCurve/Basic.lean:68` using
a pointed isomorphism of each field fibre with an elliptic projective
Weierstrass model. Over `Spec ℂ`, accepting that hypothesis without proof
would already accept the missing field-model conclusion. It is not an
independent genus-one criterion.

A concrete sufficient **new theorem to prove**, for the actual subgroup G on
an actual complex curve E, is:

```text
∃ elliptic Weierstrass model W over ℂ,
  ∃ e : G.quotient ≅ projModel W,
    e.hom ≫ projModelπ W = G.quotientS,
    (E.zero ≫ G.quotientπ) ≫ e.hom = projModelZero W.
```

`Comparison.lean:273` and `Basic.lean:304` could then transport the genuine
model's local presentation to this actual quotient. No record or Lean theorem
here assumes this existence statement. The audited sources have no Vélu
construction; their genus-one and isogeny/function-field APIs start with a
given Weierstrass model and do not construct the target. This field theorem
would still need a relative/functorial extension before producing regular
quotient-j on the full-level moduli base.

## The smallest honest comparison target

For the polynomial identity alone, full GAGA and an isomorphism of modular
Riemann surfaces are unnecessary. A smaller sufficient new result is the
following mathematical theorem, to be **proved** for actual complex curves:

> Given a pointed finite cyclic isogeny of degree N between two geometric
> elliptic curves over ℂ, there are period lattices Λ ⊆ Λ′ with cyclic quotient
> of order N, whose lattice j values equal the two algebraic j values.

This is still substantial mathematics, but it isolates the exact input used by
`theorem_11_23` and avoids an entire modular-curve analytification/GAGA package.
There are two plausible proof routes:

1. Prove ℘ parametrization as a bijective holomorphic group map on the complex
   torus, compare geometric Weierstrass points through AINTLIB's existing
   `projModelPointsEquiv`, and show that a finite algebraic isogeny lifts to a
   complex-linear map of the universal covers. Its kernel and degree then give
   the cyclic lattice inclusion. This needs new parametrization and lift theory;
   it is not an invocation of a currently available theorem.
2. Construct the quotient isogeny algebraically by a Vélu-type formula on a
   Weierstrass model and prove compatibility with finite-index lattice quotients
   using ℘ identities. This can also supply the needed quotient-curve
   construction in characteristic zero, but no Vélu/isogeny-lattice comparison
   is present in the audited source. It should be scoped as a new proof stream,
   not hidden in an assumed record field.

The source-j morphism and its Borel descent are complete. The actual coarse/fine
complex-point correspondence, lifting through the actual projection, and the
invariant-ring Borel-orbit fiber statement are also now proved. Pulling back the
same universal curve gives a native elliptic curve with its actual full-level
marking; its source-j equals the j of a genuine pointed Weierstrass presentation.
These steps connect to the moduli objects themselves, without choosing unrelated
j-pairs. In addition, actual projective models of `ofJ z` show that the actual
coarse source-j takes every complex value. Polynomial evaluation at these
actual points proves ℂ[X]→B injective without assuming B is a domain. These
results still do not produce the quotient curve. The next proof work is a
characteristic-zero quotient
elliptic curve with functoriality and the pointwise isogeny/lattice comparison.
Introducing a record whose fields simply assert quotient-j compatibility or the
desired polynomial equation would only move the missing proof into hypotheses.

## From complex-point identities to the actual scheme morphism

Even after the pointwise theorem above, one additional algebraic step is needed
to factor the two-coordinate morphism through `planeScheme N`:

1. Construct quotient-j as a regular section on the fine full-level base, with
   base-change/isomorphism compatibility; prove Borel invariance of the cyclic
   subgroup and of this quotient-j section.
2. Evaluate the two j sections at its ℂ-valued points. Their fibrewise
   interpretations must be proved using the same base-change compatibility.
3. Prove that the modular-polynomial section vanishes globally. Pointwise
   vanishing is sufficient on a reduced finite-type ℂ-scheme, using the
   Jacobson/Nullstellensatz separation argument. Finite type of this **actual
   chosen representing base** and of the actual coarse structure map is now
   established in `AINTLIBDrafts/YZeroCoarseFiniteType.lean`; the actual Borel
   invariant ring is also Noetherian over any Noetherian base. These proofs use
   the actual smooth full-level representation and the integral, injective
   invariant-ring inclusion, with no domain assumption on the full-level ring.
   Reducedness of the actual fine section ring, fine base, invariant ring, and
   coarse scheme is now also established in `AINTLIBDrafts/YZeroCoarseReduced.lean`.
   The proof supplies the missing generic smooth-over-domain reducedness API:
   use standard-étale polynomial charts, embed their rings into reduced
   fraction-field fibres by flatness, and glue by injectivity of the product of
   localizations. Only the original base is required to be a domain; over `ℂ`
   this is automatic. No domain hypothesis is imposed on fine-level sections.
   The section-separation argument is now proved in
   `AINTLIBDrafts/ComplexPointSeparation.lean` and instantiated on the actual coarse
   ring in `YZeroCoarseComplexPoints.lean`. What remains is the actual pointwise
   modular-polynomial identity to which that argument would apply.
   Alternatively prove the identity universally before descent.
4. Use the quotient-ring universal property to obtain the fine morphism to the
   independent plane scheme, then descend it by
   `coarsePr_existsUnique_lift`.

This gives a genuine morphism from `YZeroCoarse` to the modular-polynomial model.
Finiteness, birationality, normality and the normalization isomorphism remain
separate goals. A function-field equivalence with the analytic modular-function
field does not discharge them.

## A separate subgroup seam discovered during the point bridge

The full-level marking is available on the actual pulled-back elliptic curve.
The following pre-existing shortcut is not axiom-clean:
`hasExactOrder_of_isNaiveGammaOne` and
`hasExactOrder_fst_of_isNaiveFullLevel` use the unproved
`ExactOrder.hasExactOrder_of_geometric` bridge (T-D6c). Similarly, the general
rank-kills-group theorem has an unproved Deligne input; its field and
invertible-rank specializations are checked alternatives.

There is a clean input for another construction:
`EllipticCurve.fullLevelIso` really trivializes `E[N]` by the constant scheme
`(ZMod N)²` when N is invertible. Exact checks of this isomorphism, its underlying
morphism, the torsion embedding, and the constant-scheme point APIs use only the
three standard axioms. The coordinate axis can therefore be transported into
the actual curve. The retained `ConstantAxis` now packages it as an actual
finite locally free subgroup of rank N and proves killing directly from the
torsion factorization. The retained `AxisGenerator` factors this axis through the
first section's order divisor, proves the factor is an isomorphism by the
same-rank closed-immersion criterion, and compares their literal ideal sheaves.
Transferring all-test-scheme subgroup factorings gives `HasExactOrder`. Its
base-change theorem and the order-divisor base-change formula then give an
identity-fppf generator and the actual `IsCyclic`, with only the three standard
axioms. The generator leaf and native `GammaZeroStructure` wrappers have passed
the named strict build, with twenty-six axiom checks and four level-3 sanity
examples. Every actual coarse point has a full lift carrying this native Γ₀
structure. No claim about cyclic-subgroup classification or
quotient elliptic curves follows from these constructors alone.

The new `BorelAxis` leaf proves that the embedded subgroup ideal in a fixed curve
is unchanged by the actual Borel marking action. The argument positively
reindexes the constant label scheme by the unit in the first diagonal entry;
it does not identify the bundled records literally or supply quotient-j.

The raw scheme quotient now has independently checked projection flatness and
surjectivity, together with universal closedness of its structure map, in
`SubgroupQuotientGeometry`. These are proved using its actual local patches and
gluing maps, not the held `NIsogeny` elliptic-quotient upgrade. The new
`HopfGaloisLeft` leaf retains the literal canonical Galois ring equivalence while
recording the stronger left-factor B-algebra structure needed for subsequent
finite-module and étale descent. Those algebraic descents are now proved in
`HopfFinite` and `HopfEtale`. The actual target chart preimages and pullback
squares are proved in `SubgroupQuotientChartPullback`; `LocalQuotientGeometry`
then gives local quotient projection finiteness and etaleness. Checking the
actual target chart cover proves the global quotient projection finite, and
etale under the explicit subgroup-projection etaleness input, in
`SubgroupQuotientFinite` and `SubgroupQuotientEtale`. The marked constant axis
satisfies that input by `ConstantAxisEtale`. These are clean properties of the
raw quotient, with no Noetherian/domain assumption. The quotient's structure
map is already universally closed and quasi-compact. `SubgroupQuotientSeparated`
also proves it separated over arbitrary base schemes, using diagonal descent
through the finite surjective projection. The new `LocalQuotientFiniteType`
uses the actual source chart's smoothness and Artin--Tate over Noetherian base
patches. `SubgroupQuotientFiniteType` glues the actual structural triangles,
proving locally finite type, locally finite presentation, and properness of
the raw quotient over locally Noetherian bases. Subgroup etaleness is not
needed for these properties. `HopfSmooth` uses clean etale faithfully-flat
algebra descent; `SubgroupQuotientSmooth` glues it to actual scheme smoothness
when the subgroup projection is etale and the base locally Noetherian. The
literal marked axis supplies the etale input. The new
`ChartQuotientRelativeDimension` transfers the checked coinvariant dimension
condition to the actual raw scalar map. `SubgroupQuotientRelativeDimension`
then uses the genuine source cover and structural triangles to prove smooth
relative dimension one, under the same locally Noetherian and subgroup-etale
scope. These local and global named modules are checked independently; a
Weierstrass presentation still needs separate proof.

The source-precomposition finite-presentation descent in upstream
`Moduli/SmoothDescent.lean` is not a clean shortcut: its actual proof chain
passes through the unproved
`RingHom.FinitePresentation.of_comp_of_faithfullyFlat`. A Noetherian
finite-type route, using Artin--Tate on the actual local invariant algebras,
is now checked independently. No unproved descent theorem is used by the
retained geometric leaves. The rank comparisons in `KaehlerRank`,
`StandardSmoothRank`, and `LocallyStandardSmoothRank` are checked algebraic
prerequisites. The new `StandardSmoothRankConverse` and `SmoothRankCriterion`
prove both converse directions and the smooth constant-rank equivalence,
including the zero-ring boundary. `ChartKaehlerRank` proves rank one on the
actual source chart, and `KaehlerRankDescent` / `ChartCoinvariantsKaehlerRank`
descend that rank through the actual faithfully flat etale inclusion. The
raw scalar transfer and scheme relative-dimension adapters are now checked,
with the scopes stated above. `SubgroupQuotientIntegral` proves that the actual
raw quotient of an elliptic curve over any field is integral, using only its
actual flat surjective projection and the independently checked native
field-integrality theorem. No etaleness or quotient model is assumed. This
does not establish integrality of the full-level or coarse moduli scheme.
`FiniteFunctionField` now proves finiteness for the literal native field
pullback of a finite dominant morphism of integral schemes.
`SubgroupQuotientFunctionField` applies it to the actual raw, chosen-killing,
and marked-axis projections over arbitrary fields. `FunctionFieldFormallyUnramified`
provides the generic-stalk unramified map under the weaker irreducible scope.
`FunctionFieldEtale` and the actual `SubgroupQuotientFunctionFieldEtale`
specialization prove generic field etaleness in arbitrary characteristic,
using the actual etale quotient projection.
These earlier generic field-map statements alone are not a comparison of curve
places. The subsequently checked actual place restriction/map now proves normalized
valuation compatibility for every source place, finite fibers, and additive divisor
pullback; the characteristic-zero wrapper also proves principal-divisor compatibility.
No Riemann--Hurwitz theorem follows from those statements alone.

Properness, smooth relative dimension one, and a section do not alone yield an
elliptic curve: a pointed projective line is a counterexample. The pinned
`EllipticCurve` record requires `LocallyWeierstrass` independently. The
`FibrewiseElliptic` reconstruction input already includes a pointed Weierstrass
isomorphism on every field fibre, so assuming it for the quotient would move
the unresolved model into a hypothesis. The pole-sheaf reconstruction also
retains that input. Its cotangent H¹ smoothness lemmas are unrelated to
H¹(𝒪) or genus. No quotient model or quotient-j is inferred here.

The vendored `Ramification.lean` proves a polar-degree bound, not a
Riemann--Hurwitz formula for a finite extension of two curve function fields.
The genus-one lemmas found in `GenusOne`/`GenusCounting` concern an already
elliptic Weierstrass function field. The actual quotient function-field extension and the comparison from etaleness
to normalized valuations at every source place are now proved, as are finite-fiber
and principal-divisor pullbacks. The remaining route needs weighted degree
pullback, canonical-divisor/differential comparison, and an unramified genus formula,
followed by noncircular model reconstruction; alternatively one can construct
quotient coefficients directly.

The actual native `GammaHClasses` is now equivalent to actual coarse complex points.
Its relation is the upstream pointed-isomorphism plus
Borel marking relation, rather than a newly declared classifier kernel. The
fine-classifier native roundtrip is proved, as is the construction of a
marking-preserving native pointed isomorphism from equal fine classifiers.
The converse class-map argument is also proved: the actual Borel fiber criterion
gives the positive marking transform, the marked pointed iso converts to an actual
`HomOver`, and its two forward section equations give a witness of the original
relation, hence `Quot.sound`. The inverse can be computed using any actual full
lift, with its native curve and actual marking. The named strict class leaf has
thirteen standard-three-axiom checks, five level-three sanity examples, and no
own warnings/errors. None of these results supplies quotient-j or the
modular-polynomial identity.

## Verification boundary

This document records the remaining source-audit gaps. The actual invariant-spectrum
identification and the finite-type/Noetherian/reducedness prerequisites have now been checked
in the pinned AINTLIB environment, with only `propext`, `Classical.choice`, and
`Quot.sound`. A valid eventual receipt must still inspect the axioms of
the actual quotient-j morphism and polynomial factorization, including their
selected quotient-curve construction. A green import/build of sorried AINTLIB
files is not a proof that these comparison theorems are axiom-clean.
