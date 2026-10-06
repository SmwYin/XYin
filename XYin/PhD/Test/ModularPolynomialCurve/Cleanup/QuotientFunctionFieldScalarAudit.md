# Quotient function-field scalar audit

Snapshot: 2026-10-04. This is a source/mathematics audit of the actual raw subgroup
quotient, plus a separately checked temporary transcendental-existence proof. It does
not supply a quotient Weierstrass model or a quotient-genus comparison.

AINTLIB: `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`.
Mathlib: `300d0e535721bc098547106fc297d8ba2a63f6bb`.
Lean: `leanprover/lean4:v4.35.0-rc3`.
All source paths below are relative to the pinned isolated workspace
`/private/tmp/xyin-y0-aintlib-work`; hashes appear at the end.

## Subsequent checked results

The source-only plans below are preserved as the original audit. They have now
been partially implemented and should not be mistaken for the current boundary:

- `NativeCoordinateTowerObstruction` formally proves the conditional rank-divides-2
  obstruction and the actual rank3 contradiction.
- `RatFuncTranscendentalParameter`, `RatFuncTranscendentalParameterFinite`, and
  `RatFuncSubfieldParameter` prove the new parameter embedding, naturality and
  finiteness while preserving the original constant-field algebra.
- `RatFuncParameterScalars` proves the literal polynomial/RatFunc scalar tower.
- `YZeroCoarseSubgroupQuotientParameterFinite` applies these results to the actual
  raw and public quotient fields over arbitrary fields. It uses the genuine native
  quotient pullback and introduces no embedding-finiteness, etale, genus or model
  hypothesis. The two raw/public APIs and ten exact standard-three checks passed
  strict named session84251, with zero diagnostics and all six artifacts plus C
  verified by the owner and root.

These leaves are independently checked after the historical99-module checkpoint.
The actual quotient FunctionField/scalar wrappers are now also proved in
`YZeroCoarseSubgroupQuotientParameterFunctionField`: arbitrary fields give the
finite pack, and characteristic zero gives separability. The actual quotient's
all-place residue-finiteness and positive degree are proved under characteristic
zero in `YZeroCoarseSubgroupQuotientPlaceResidueFinite`. Their conclusions expose
only the independently geometric constants, with no chosen-parameter premise.

`YZeroCoarseSubgroupQuotientPlaceRestriction` now connects every source intrinsic
place to an actual quotient place with normalized valuation equality on the
literal native field pullback. Its scope is arbitrary fields with actual etale
subgroup; no residue/chart/characteristic-zero premise is used there.
Cross-field genus comparison, Weierstrass reconstruction and target-j remain
subsequent work. The original source-only plans below record their earlier status.

## Independent base constants and the failed old-coordinate shortcut

The scheme function field of the actual quotient Q is already a field. Its k-algebra
is specified independently by `Q → Spec k`, global sections, and the generic germ:
`quotientS.functionFieldBaseAlgebra`. The checked
`YZeroCoarseSubgroupQuotientBaseAlgHom.lean:41` constructs the literal pullback
`KQ →ₐ[k] KE`; its underlying ring map is the actual quotient's
`functionFieldMap.hom`, not a freely selected embedding.

Mathlib's `_root_.FunctionField k K` has additional chart data:
`Mathlib/NumberTheory/FunctionField.lean:58` defines it as finite dimensionality
for a specified `Algebra k⟮X⟯ K`. One therefore must choose and justify a
transcendental embedding into KQ to use that API.

The retained native RatFunc embedding is the chosen source Weierstrass x-coordinate:
`NativeRatFuncScalars.lean:36` uses the actual coordinate fraction ring and
`WeierstrassCurve.Affine.algebraRatFunc` (native `EllipticCurve/Instances.lean:121`).
For that embedding, `finrank_ratFunc_eq_two` (same native file:161) computes
`[KE : k(x)] = 2` with basis `1,y`.
The actual marked-axis quotient-degree theorem
`YZeroCoarseSubgroupQuotientFunctionFieldDegree.lean:86` gives `[KE : KQ] = N`.

**Mathematical obstruction, not a proved Lean declaration in this audit:** if the
same old embedding `k(x) → KE` factored through `KQ → KE` with the genuine scalar
tower, the tower law would give

`2 = [KE : k(x)] = [KQ : k(x)] · [KE : KQ] = d · N`.

Thus N would divide 2, excluding level 3 in particular. The relevant formal
primitive is `Module.finrank_mul_finrank` / `Module.finrank_dvd_finrank_left`
(`Mathlib/LinearAlgebra/Dimension/Free.lean:68–79`). This explains why transferring
that fixed source RatFunc algebra to the quotient cannot be the general route.
The argument is conditional on that factorization; it does not assert any failure
of the actual quotient's independently defined k-algebra.

## Smallest intrinsic existence route — temporary proof checked

There is a shorter path to a quotient transcendental element than proving finite
generation or transcendence degree first:

1. Install the existing native RatFunc algebra and its **proved independent k-base
   tower**. The image of `RatFunc.X` in KE is transcendental over k, by
   `RatFunc.transcendental_X` (`AsPolynomial.lean:262`) and
   `transcendental_algebraMap_iff` (`Algebraic/Basic.lean:332`).
2. Use the literal checked quotient base AlgHom φ. Define the KQ-algebra on KE by
   `φ.toRingHom.toAlgebra`. Its `commutes` law proves the actual `k → KQ → KE`
   tower. The checked quotient finite-map theorem supplies `Module.Finite KQ KE`.
3. Consequently KE is algebraic over KQ (`Algebra.IsAlgebraic.of_finite`,
   `Algebraic/Integral.lean:107`). If KQ were algebraic over k,
   `Algebra.IsAlgebraic.trans` (same file:347) would make KE algebraic over k.
   The source transcendental element excludes that possibility.
4. `Algebra.transcendental_iff_not_isAlgebraic` (`Algebraic/Defs.lean:87`) supplies
   `∃ t : KQ, Transcendental k t`.

The temporary file
`/private/tmp/xyin-y0-aintlib-work/YZeroSubgroupQuotientTranscendentalProbe.lean`
contains `nativeField_isTranscendental`, `gluedQuotient_exists_transcendental`, and
`quotient_exists_transcendental`. Its raw assumptions are arbitrary field k,
actual E/Spec k, actual finite locally free subgroup G, nonzero killing N and the
actual killing equation. The public theorem forwards the genuine chosen
`killN`/`killN_spec`. It adds no etale, Noetherian, separability, genus, or model
assumption.

Strict no-output compiler session **30702 owner-polled CLOSED, exit 0**.
96 lines, width 93, SHA
`fde4d1bd560351959d3898ff5f69ec48dc3a82cdf1ed5554ffb385f5e6e4a3fb`.
Full log `/private/tmp/YZeroSubgroupQuotientTranscendentalProbe-first.log`:
12 exact printed declarations, 11 with the standard three axioms and the tower
constructor with `propext` only; zero diagnostics; two raw/public API examples.
Receipt `/private/tmp/YZeroSubgroupQuotientTranscendentalProbe-receipt.json`.
No temporary artifact was emitted. After the parent reviewed the full source and log,
the exact mathematical suffix was retained as
`AINTLIBDrafts.YZeroCoarseSubgroupQuotientTranscendental` (115 lines, SHA
`71b74fa509acd1ba563d93ff4a5f382ccbefb15adea72eb83e527dbfc8906daf`).
Correct-name emission **17095 owner-polled CLOSED, exit 0** has the same 12 checks,
zero diagnostics, two APIs, and six canonical outputs plus C. The independent named
receipt is `/private/tmp/xyin-y0-subgroup-quotient-transcendental-receipt.json`; see
`SubgroupQuotientTranscendentalVerification.md`. This new leaf is outside cumulative76.

## New-t RatFunc construction and shortest finite pack — source-only follow-up

For a field extension K/k with its specified independent k-algebra and
`ht : Transcendental k t`, the direct polynomial lift is already supported:

- `transcendental_iff_injective` (`Algebraic/Basic.lean:105`) makes
  `Polynomial.aeval t : k[X] →ₐ[k] K` injective.
- `RatFunc.liftAlgHom` (`RatFunc/Basic.lean:639`) lifts that map with the exact
  nonzero-divisor condition furnished by
  `nonZeroDivisors_le_comap_nonZeroDivisors_of_injective`.
- The resulting `ζ : k⟮X⟯ →ₐ[k] K` sends X to t by
  `RatFunc.liftRingHom_X` (`RatFunc/AsPolynomial.lean:99`) and `Polynomial.aeval_X`
  (`Polynomial/AlgebraMap.lean:292`). Its polynomial restriction is exactly aeval t
  by `RatFunc.liftRingHom_algebraMap` (`RatFunc/Basic.lean:597`).
- An existing higher-level alternative is
  `RatFunc.algEquivOfTranscendental t ht : k⟮X⟯ ≃ₐ[k] k⟮t⟯`
  (`AsPolynomial.lean:226`), composed with the literal intermediate-field inclusion.
  `algEquivOfTranscendental_X` (:237) and its polynomial formula (:230) prove
  the same X and polynomial equations. A localization-ext proof identifies
  this alternative with the direct lift, so no second incompatible scalar choice
  is needed.

For the actual quotient, let φ be the literal retained base AlgHom, y=φ(t), and
ζ the direct lift for KQ. Keep the independent k-algebras; the new RatFunc algebra
on KE is defined by `(φ.comp ζ).toRingHom.toAlgebra`, and that on KQ by
`ζ.toRingHom.toAlgebra`. The RatFunc→KQ→KE tower then follows from the literal
composition, while the original source RatFunc is used only to obtain the
following finite-dimensional statement:

1. `isAlgebraic_algHom_iff` / `transcendental_algebraMap_iff` transfers
   transcendence of t to y.
2. `FunctionField.finiteDimensional_of_adjoin_transcendental`
   (`NumberTheory/FunctionField.lean:229`) gives `Module.Finite k⟮y⟯ KE`.
3. The existing `e_y : k⟮X⟯ ≃ₐ[k] k⟮y⟯` is finite as a ring map
   (`RingEquiv.finite`, `Finiteness/Basic.lean:463`). Compose it with the finite
   adjoin inclusion using `RingHom.Finite.comp` (:469). Polynomial restriction
   and `IsLocalization.algHom_ext` (`Localization/Basic.lean:669`), together with
   `Polynomial.aeval_algHom` (`Polynomial/AlgebraMap.lean:398`), identify that
   composite with φ.comp ζ. This supplies finiteness of KE for the *new* RatFunc
   scalar map; the original x does not factor through KQ.
4. Repackage φ as a RatFunc algebra map using the defining composition law.
   `FiniteDimensional.of_injective` (`FiniteDimensional/Defs.lean:84`) then
   supplies `Module.Finite k⟮X⟯ KQ`, hence the new `_root_.FunctionField` class.

This avoids an additional intermediate-field-image equivalence adapter. The only
alignment obligation is equality of the new embeddings on polynomial restriction;
its exact extensionality and aeval primitives are already present. No separating
statement follows from this finite pack. This follow-up is a source contract and
has not been drafted or compiled.

## Potential finite-generation route after choosing a new t — source only

Let t be a transcendental element of KQ and y its actual image in KE. The same
base AlgHom transfers transcendence to y. Then
`FunctionField.finiteDimensional_of_adjoin_transcendental`
(`Mathlib/NumberTheory/FunctionField.lean:229`) makes KE finite over k(y), using
the already checked source FunctionField structure.

`IntermediateField.adjoin_map` (`Adjoin/Defs.lean:409`) and
`IntermediateField.equivMap` (`IntermediateField/Basic.lean:778`) identify the
actual image of k(t) with k(y). After explicitly aligning those scalar maps,
`FiniteDimensional.of_injective` (`FiniteDimensional/Defs.lean:84`) restricts
finiteness to KQ over k(t). This is a concrete route to a newly chosen quotient
RatFunc algebra and FunctionField class; it still requires those scalar adapters.

For finite generation, singleton adjoin is FG by
`IntermediateField.fg_adjoin_of_finite` (`Adjoin/Defs.lean:662`), and
`IntermediateField.essFiniteType_iff` (`Adjoin/Algebra.lean:118`) turns that into
an essentially-finite-type k-algebra. A finite algebra is finite type, then
`Algebra.EssFiniteType.of_finiteType` (`EssentialFiniteness.lean:95`) and
`Algebra.EssFiniteType.comp` (same file:140) provide the remaining composition.
This avoids guessing a generic essentially-finite-type subfield descent lemma.
None of these quotient adapters has been proved in this audit.

## Separating choice over perfect fields — separate source-only step

For an essentially finite type extension over a perfect field, the exact theorem
`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`
(`Mathlib/FieldTheory/SeparablyGenerated.lean:312`) supplies a finite
transcendence basis s and separability of KQ over `IntermediateField.adjoin k s`.
It does not directly assert a singleton basis. A quotient trdeg-one proof,
`IsTranscendenceBasis.cardinalMk_eq_trdeg`
(`AlgebraicIndependent/TranscendenceBasis.lean:422`), and a singleton extraction
would bridge that final choice. `trdeg_add_eq` (same file:545) and
`trdeg_eq_zero_iff` (`AlgebraicIndependent/Transcendental.lean:88`) are available
for the finite/algebraic tower. Arbitrary fields require a separate analysis of
separating generation; the existence theorem above alone gives no such claim.

## Genus comparison boundary

The actual source intrinsic genus-one theorem is now retained as `NativeGenus`.
The intrinsic quotient genus expression already makes sense with its independent
k-algebra (`CoordinateFree/RiemannRoch.lean:79`); a chart comparison requires the
actual polynomial/RatFunc/finite/separable/full-constant-field pack.

`FunctionField.Chart.genus_le_of_family` (`Genus/Basic.lean:250`) is a one-field
criterion: it needs a genuine quotient divisor family with a defect bound and
unbounded Riemann–Roch dimension. `deg_polarX_le_finrank`
(`Genus/Ramification.lean:357`) bounds the poles of the chosen coordinate by its
RatFunc extension degree. Neither theorem is a cross-field genus inequality.

A bounded search of the pinned vendored Riemann–Roch, mathlib AlgebraicGeometry,
and mathlib FieldTheory sources found no Riemann–Hurwitz theorem or general
`genus(KQ) ≤ genus(KE)` extension theorem. The earliest RR prerequisites remain
a genuine quotient separating chart and a proved cross-field place/divisor or
regular-differential comparison (or an actual quotient family bound). This audit
adds no quotient genus-one, Weierstrass presentation, target-j, or modular
polynomial assertion.

## Exact snapshot hashes

| Source, relative to the pinned isolated workspace | SHA256 |
| --- | --- |
| `AINTLIBDrafts/NativeRatFuncScalars.lean` | `b57878716090858304375d3e75c5d05864ae192b216ab84d3b2a6b3bd045e22f` |
| `AINTLIBDrafts/NativeGenus.lean` | `26f006dc6ef42e7adba7bfa4ac033fafc6b936c70372b3ca0d34c4ef9de2296e` |
| `AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionField.lean` | `55b414d14df7d149ba6965ffb5efb25cf09eb47b36a223d12a53a077ab70fcc3` |
| `AINTLIBDrafts/YZeroCoarseSubgroupQuotientBaseAlgHom.lean` | `f5ea5516f25308b695c11885477e5d42ef734ec81a44f285c8c73265b42f4652` |
| `AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionFieldDegree.lean` | `fa8c23229cde4cda6adab461dbcdbab22970a00b4d2deb3ec294f0b1b86a44ac` |
| `.lake/packages/mathlib/Mathlib/NumberTheory/FunctionField.lean` | `adc39a94bf85118dc10660f6ef5b9aeff7e3bfe5c3428bd86d388b70c29eb58f` |
| `.lake/packages/mathlib/Mathlib/FieldTheory/RatFunc/AsPolynomial.lean` | `29251ef0c7d2e6f53eadd4a8c0cb77ea4fc9b1e27e47e57f839afaaeb032fbda` |
| `.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Defs.lean` | `4c25b9f55ecd629a00eac8b686e553fb27bd6d48dc10fef02cf65d0d7bc3a134` |
| `.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean` | `16fd98b24b39d459f660cb752f75bf933f1a6b70cf47527bd2753599ffe8e44d` |
| `.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Integral.lean` | `64cd1a91776db4a4e1922a114a171f69a4f631fa88917b6de8c5330a771e6de4` |
| `.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean` | `3c2eec81418ebe321c3a21ff0dfd40226489bf8463bcf5c447064136b4e386ce` |
| `.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean` | `a3e88c4fe00ba476440d68a1568afecf6be685a488b5b8718f6b2ef969a15fa4` |
| `.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Basic.lean` | `8a08838457e90b5f32125189bdae4e7e79fdae7872f3d44ad86f9b053be57849` |
| `.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean` | `b9f8f0d32500e6df1f392a1cbe8729cad66a594098d1ba0c02c85c38c5eb10d3` |
| `.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean` | `45e6f559a926f738d635666a19ad72878fdbbadf9400cba9e1f691ae8a7711ad` |
| `.lake/packages/mathlib/Mathlib/RingTheory/EssentialFiniteness.lean` | `962035ff36c063d4c3cc707364b780742a892ad7aa048069dda40e66e8f40c5e` |
| `.lake/packages/mathlib/Mathlib/FieldTheory/SeparablyGenerated.lean` | `885af82f540b1f05565be33cc183448bb919ef5fc410ff861175b9ae27d0cf35` |
| `.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/Transcendental.lean` | `2095cea5dd3ca2efba3025781ebcd93e46db7294a2f388a54b21fa8d11bb755b` |
| `.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean` | `0a0fe1baa58a98680b580046d39b61121309944f6daceadad63e3267a2b6b4d4` |
| `projects/ModularCurves/ModularCurves/Vendored/RiemannRoch/EllipticCurve/Instances.lean` | `e3054d3edd7282106c707ead40047fce914eaf6b05cd8225d34342b25247cd4b` |
| `projects/ModularCurves/ModularCurves/Vendored/RiemannRoch/Genus/Basic.lean` | `e79437fe3d0d8910de9e93ba01d42c414437abf553e460482ce9025dab189a32` |
| `projects/ModularCurves/ModularCurves/Vendored/RiemannRoch/Genus/Ramification.lean` | `7e26a74b4334506414403491f5cd3b40ad8c918943063ffedd56ac0cede7ee95` |
| `projects/ModularCurves/ModularCurves/Vendored/RiemannRoch/CoordinateFree/RiemannRoch.lean` | `ebed1b23bd52099c73a508462e3870df97e221d52779230c72b3f35a6aa1f07a` |
| `AINTLIBDrafts/YZeroCoarseSubgroupQuotientTranscendental.lean` | `71b74fa509acd1ba563d93ff4a5f382ccbefb15adea72eb83e527dbfc8906daf` |
| `.lake/packages/mathlib/Mathlib/FieldTheory/RatFunc/Basic.lean` | `343e108fbff17b4bbce6e5784ef673b3c73e11f067ce9f56344f3543b573c29f` |
| `.lake/packages/mathlib/Mathlib/Algebra/Polynomial/AlgebraMap.lean` | `a01f04ebcb720c95ba906cc8da0cee902ea8068ecb92d865fde80db90afce537` |
| `.lake/packages/mathlib/Mathlib/RingTheory/Localization/Basic.lean` | `871467f69dac004f32b48b49130ceebc638eb0c74919ef6bca84a9a5048c067d` |
| `.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Defs.lean` | `aa5c6c53c292d0fa6688419fefdd97182605d6dd1bc3bfd898846e9fe8262c36` |
| `.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Basic.lean` | `704734b7dbe3ace88c1302bca72a629483a70bff40e210dcbc31e96ba54866ce` |
