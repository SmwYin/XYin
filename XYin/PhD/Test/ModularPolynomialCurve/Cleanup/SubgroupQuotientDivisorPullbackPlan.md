# Actual quotient divisor pullback: source-backed interface

This is an interface/proof plan only: no new Lean source or compiler run. The actual coordinate-free abbreviation in `Vendored/RiemannRoch/CoordinateFree/Divisor.lean:170` is `FunctionField.Divisor k K := Place k K →₀ ℤ`. Its type needs the fields and original `Algebra k K`; the surrounding chart, function-field pack and separability inputs are not used by this abbreviation. They are needed for other APIs such as the chart-defined principal divisor, which is outside this step.

The sibling's checked generic interface is:

```lean
Finsupp.comapDomainOfFiniteFibers
  (r : A → B) (hfib : ∀ b, (r ⁻¹' {b}).Finite) [AddZeroClass M] :
  (B →₀ M) →+ (A →₀ M)
```

Its literal coefficient formula is `... D a = D (r a)`. It needs neither injectivity nor surjectivity of `r`, and finite fibers ensure finite support. Specialize `M := ℤ`, `A := Place k K(E)`, `B := Place k K(Q)`, and `r := G.gluedQuotientPlaceMap N hkill`. The auditor is proving the actual finite-fiber input over any field and with actual subgroup étaleness.

The proposed actual raw signature is:

```lean
noncomputable def gluedQuotientDivisorPullback
    (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) :
    let _ : IsIntegral (G.gluedQuotient N hkill) :=
      G.gluedQuotient_isIntegral N hkill
    let _ := (G.gluedQuotientS N hkill).functionFieldBaseAlgebra
    let _ := E.π.functionFieldBaseAlgebra
    FunctionField.Divisor k (G.gluedQuotient N hkill).functionField →+
      FunctionField.Divisor k E.E.functionField
```

It lives in `ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup` with `{k} [Field k]`, native `E` over `Spec k`, actual `G`, and `[Etale G.π]`. No characteristic-zero premise is needed for this coefficient pullback. Its body installs the actual proved quotient surjectivity needed by the existing place-map interface and applies the generic additive hom to that map and its **proved** finite fibers. No finite-fiber hypothesis is added to the public declaration.

The public `quotientDivisorPullback [G.HasKillingInt]` forwards exactly `G.killN` and `G.killN_spec` and has type `FunctionField.Divisor k G.quotient.functionField →+ FunctionField.Divisor k E.E.functionField`, under the same two original geometric constant algebras and actual quotient integrality.

The coefficient theorem should state, after installing the actual integrality/surjectivity and both geometric algebras:

```lean
∀ (D : FunctionField.Divisor k (G.gluedQuotient N hkill).functionField)
  (v : FunctionField.Place k E.E.functionField),
  G.gluedQuotientDivisorPullback N hkill D v =
    D (G.gluedQuotientPlaceMap N hkill v)
```

The generic coefficient lemma should discharge this directly. The same formula with the literal chosen-killing public map is a forwarding wrapper. No ring-embedding hypothesis, compatibility scalar assumption, chart construction or parameter choice is needed: both original algebras are already specified independently, and the existing place map is already proved along the genuine native function-field map.

There is no ramification factor in this coefficient statement. The existing étale place-map valuation identity has factor one, but this finite-support additive hom alone does not prove principal-divisor compatibility, degree multiplication, Riemann–Hurwitz, or a genus claim. Those remain separate mathematical steps.
