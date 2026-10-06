# Independent review of the actual complex-point orbit bridge

Review date: 2026-10-04. Reviewer: `y0_invariant_route`.

This is a fresh read-only mathematical and API review of the three files below, including
the full explicit orbit-quotient equivalence. No Lean source was edited and no compiler or
build was started during this review. Existing compiler logs were inspected separately
from the source arguments. This is not a claim that a new full cleanup workflow was run.

All three current retained files agree byte-for-byte with the corresponding files in the
pinned AINTLIB workspace. The snapshots at the beginning and end of the review agree.

| File | Lines | Current SHA-256 |
| --- | ---: | --- |
| `YZeroCoarsePointLifting.lean` | 123 | `51431ee27ab7c5a93fa07bf09340b7039b0e605d43e58e0eedb09431b25cd1ae` |
| `YZeroCoarsePointOrbits.lean` | 175 | `20f8b19dd1e78eb5952cf1eee72829f4fd78200df6ee3620ca2a86ba0856a27a` |
| `YZeroCoarseComplexPointOrbits.lean` | 176 | `1748d03839445c539ee36dab3726c771bd8b7a79d015b39ebe4a76dbfa338ac1` |

The source workspace is `/private/tmp/xyin-y0-aintlib-work`, pinned to AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, Lean `4.35.0-rc3`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`.

## Verdict

No mathematical defect or required repair was found. The current code proves a bijection
between actual coarse complex scheme points and the quotient of actual full-level complex
scheme points by the literal actual Borel orbit relation. It does not encode coarse
equality as the definition of that relation. The lifting, invariant-ring criterion, and
scheme-point criterion are independently proved steps.

The fine coefficient ring is never assumed to be a domain. Freeness of the Borel action is
never assumed. Algebraic closedness and finite type are used for lifting complex points;
they are not used by the generic orbit criterion. Reducedness is unnecessary for either
the lift or this set-level orbit classification.

## Generic lifting and its actual instantiation

`exists_algHom_comp_eq_of_injective_integral` uses names `B` for the lower ring and `A`
for the upper ring. Its hypotheses are an algebraically closed field `k`, commutative
`k`-algebras, finite type of `A/k`, and an injective integral `k`-algebra map `ι : B → A`.
It correctly produces an extension of each coefficient-linear point `φ : B →ₐ[k] k`.

The proof uses the exact maximal ideal `ker φ`. Surjectivity of `φ` follows from its scalar
law, so this ideal is maximal. Lying over is applied with the verified condition
`ker ι ≤ ker φ`, obtained from injectivity of `ι`. The maximal upper ideal supplies a
coefficient-linear point through the existing finite-type residue-field lemma. Finally,
the element `b - algebraMap k B (φ b)` determines the restriction equality. This last step
is needed: agreement of contracted ideals alone would not establish the literal ring-map
equality without the coefficient condition.

For the actual instantiation, the upper ring's scalar algebra is exactly
`fullCoefficientHom.toAlgebra`, the lower ring uses `yZeroInvariantAlgebra`, and
`yZeroComplexInvariantInclusion.commutes'` is proved from
`yZeroInvariantCoefficientHom_comp_inclusion`. Thus the extension is along the actual
coarse-to-fine inclusion and uses the actual structure morphisms. Its integrality,
injectivity, and fine finite type are previously proved actual facts. The product
`ℂ × ℂ` sanity check also confirms that no fine-ring domain condition is hidden.

The named local instances `pointLiftingFullAlgebra` and `pointLiftingInvariantAlgebra`
avoid the earlier collision of anonymous declarations on combined imports.

## Generic orbit criterion and its inverse convention

Here the source uses `A` for the invariant ring and `B` for the ring being acted on; these
letters have the opposite roles from the lifting lemma. The hypotheses are:

| Statement | Needed coefficient/general assumptions |
| --- | --- |
| `algHom_eq_of_ker_eq` | Commutative coefficient ring `k`, commutative `k`-algebra `B` |
| `invariant_restriction_eq_iff_orbit` | Additionally `IsDomain k`, finite group `G`, ring action on `B`, commuting scalar actions, and `Algebra.IsInvariant A B G` |

The first lemma is correctly more general than a field statement. The difference
`x - algebraMap k B (φ x)` belongs to `ker φ`, and equality of kernels forces its image
under `ψ` to vanish. This determines `ψ x = φ x`. The coefficient-ring product sanity
check exercises exactly this generality, not the domain-dependent orbit theorem.

The domain assumption in the orbit theorem is on the target coefficient ring `k`: it
makes the two kernels prime. It is not on `A` or `B`. Equality of restrictions gives equal
contractions to `A`. The exact mathlib theorem
`Algebra.IsInvariant.exists_smul_of_under_eq` then supplies `ker ψ = g • ker φ`.
Membership in this transformed ideal is `g⁻¹ • x ∈ ker φ`; accordingly the intermediate
point is `θ = φ.comp (MulSemiringAction.toAlgHom k B g⁻¹)`. The proof returns `g⁻¹` as its
existential witness. This inverse is in the correct place, and it does not introduce an
extra inverse into the final stated orbit relation.

The reverse implication uses `smul_algebraMap`. This requires the stated commuting
`A`-scalar action; `Algebra.IsInvariant` alone asserts only that fixed elements come from
`A`. Both directions of the invariant-image condition are therefore justified. No
scalar-tower condition between `k` and `A` is mathematically required by this generic
criterion, and none is silently assumed.

## Actual scalar and section-action alignment

`pointOrbitsFullAction` is the action on global sections induced by the exact actual
`borelAction`, using the top-open stability witness obtained from the actual structure
morphism and `borelAction_over`. These are the same data used by
`AffineInvariantQuotient.invariantSections` and the literal invariant inclusion.

`fullComplexSection_smul_eq_appTop` proves that this action is the actual pullback
`((borelAction ...).hom g).appTop.hom`; it accounts for the `appLE`/top-open wrapper
instead of assuming it away. `fullComplexSection_scalar_fixed` derives invariance of
actual complex coefficients from the over-base scheme triangle. The resulting
`SMulCommClass G ℂ B` is therefore about the actual complex structure.

The invariant extension uses the literal inclusion's `toAlgebra`. Its invariant-image
and commuting-scalar instances reduce to `FixedPoints.subalgebra ℤ` for the same section
action. The `ℤ` in that construction is not a replacement for the coefficient `ℂ` action:
the complex scalar structures and the inclusion's complex-linearity were proved
separately. The final actual algebra-point statement compares restrictions along
`yZeroComplexInvariantInclusion` and transforms by the actual `appTop` map.

## Scheme points, right-action variance, and literal fibers

Upstream `SchemeAction.hom_mul` states `σ.hom (g*h) = σ.hom g ≫ σ.hom h`. Consequently,
if `T_g(p) = p ≫ σ.hom g`, then

```text
T_h(T_g(p)) = (p ≫ σ.hom g) ≫ σ.hom h = T_(g*h)(p).
```

This is a right action on points. The module says so and does not export a false left
`MulAction` instance. The ring action is a left action by pullback, as verified by
upstream `gammaMulSemiringAction.mul_smul`.

`fullComplexAlgebraPointOfScheme_borelTransform` checks the variance explicitly:
the algebra point of `T_g(p)` evaluates `x` as `φ_p(σ.hom g.appTop.hom x)`. The use of
`toSpecΓ` naturality and contravariant `Spec.preimage_comp` is in the correct order.
`yZeroComplexSchemePointOfFull_eq_ofAlgebra` then identifies the actual projection with
the actual invariant restriction through the proved affine point equivalences.

Both directions of `yZeroComplexSchemePointOfFull_eq_iff_borel` use these checked bridges.
In particular, equality of algebra points is transported back to actual scheme points
using injectivity of the fine algebra/scheme equivalence. The conclusion is literal:

```text
coarse(p) = coarse(q) ↔ ∃ g : borel N, q.val = p.val ≫ actualBorelAction.hom g.
```

It contains no assumed comparison of point fibers, no target quotient elliptic curve,
and no guess about how the Borel action acts on an analytic marking.

## Explicit quotient equivalence and actual-lift surjectivity

`fullComplexBorelOrbitSetoid.r` is defined by the displayed existential Borel transform.
Reflexivity, symmetry, and transitivity are certified by the independently proved fiber
criterion. Using coarse equality to prove these laws does not change the literal
relation into a kernel-relation definition.

`yZeroComplexSchemePointOfBorelOrbit` is the actual coarse map descended by
`Quotient.lift`. Injectivity of this quotient map follows from the actual fiber theorem
and `Quotient.sound`. Surjectivity uses `yZeroComplexSchemePoint_lifts`, which lifts a
literal complex scheme point over `Spec ℂ` through the actual projection. It does not
infer complex rational-point surjectivity merely from the scheme projection being
topologically surjective. The required algebraically closed field and fine finite-type
input have already been discharged by the actual lifting theorem.

`fullComplexBorelOrbitEquivYZero` packages this proved bijection. Its `mk` theorem is
definitionally the original actual projection, and the level-3 examples exercise both
inverse laws. The conclusion is a set-level equivalence of complex points, not a new
scheme isomorphism or a coordinate-ring presentation. The actual current construction
still has `N ≥ 3` and `NeZero N`.

## Existing verification receipts and nonblocking API observations

The inspected existing logs contain successful pinned target builds:

- `/private/tmp/xyin-y0-point-orbits.log`: `YZeroCoarsePointOrbits` built in 91s,
  9395 jobs. The two generic statements and the actual restriction/orbit statement all
  print only `propext`, `Classical.choice`, `Quot.sound`; the named PointLifting
  declarations are also replayed with those axioms.
- `/private/tmp/yzero-complex-point-orbits-build.log`: full
  `YZeroCoarseComplexPointOrbits` built in 153s, 9403 jobs. All ten printed declarations,
  including the literal setoid, quotient bijectivity, explicit equivalence, and its `mk`
  theorem, print only the same standard three axioms. There is no own-module warning or
  error. Replayed upstream warnings are not assertions about these new statements.

These are existing receipts, not builds rerun in this review. The final cumulative
build remains the integration authority for any subsequent dependency changes.

Two possible future API improvements are nonblocking and were not implemented here.
The lifting lemma could weaken global injectivity to the point-specific condition
`ker ι ≤ ker φ`; its current hypothesis is sufficient and actual injectivity is proved.
Explicit transform-one and transform-multiplication lemmas could make use of the right
action more convenient. Their absence does not affect the proved orbit relation or
quotient equivalence. No source repair is requested.
