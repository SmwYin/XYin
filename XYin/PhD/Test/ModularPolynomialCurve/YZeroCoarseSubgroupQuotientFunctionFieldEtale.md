# Etale native function-field maps of the actual quotient

The retained module is
`AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionFieldEtale.lean`.
It applies the generic field-map theorem to the actual subgroup quotient
projection over an arbitrary field. The projection direction is
`E.E → quotient`, so the native ring map goes from the quotient's function
field to the original curve's function field.

In namespace `ModularCurves.EllipticCurve.FiniteLocallyFreeSubgroup`, the
three construction parameters are an actual subgroup `G`, a positive level
`N` with `[NeZero N]`, and the literal killing equation
`hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero`. The raw theorem is:

```lean
gluedQuotientπ_functionFieldMap_etale [Etale G.π] :
    let _ : IsIntegral (G.gluedQuotient N hkill) := G.gluedQuotient_isIntegral N hkill
    let _ : Surjective (G.gluedQuotientπ N hkill) := G.gluedQuotientπ_surjective N hkill
    (G.gluedQuotientπ N hkill).functionFieldMap.hom.Etale
```

It installs only already proved actual inputs: integrality of the quotient,
surjectivity and finiteness of its projection, and étaleness of that
projection under `[Etale G.π]`. Surjectivity supplies dominance through the
existing instance. The integral source is the actual native elliptic curve
over a field. The conclusion is the literal native ring map's étaleness,
with no alternate field construction or presumed scalar tower.

The public theorem `quotientπ_functionFieldMap_etale` assumes
`[G.HasKillingInt]` and `[Etale G.π]`. Its target-local integrality and
surjectivity instances are explicit in the statement in the same style as
the previously retained finite/injective API. Its entire proof specializes
the raw theorem to `G.killN` and `G.killN_spec`, exactly matching the native
public quotient and projection definitions. No separate killing integer or
replacement projection is selected.

In namespace `ModularPolynomialCurveTest.AINTLIB.ConstantAxis`,
`sectionAxis_quotientπ_functionFieldMap_etale` takes an arbitrary field `k`,
nonzero invertible `N`, a native elliptic curve over `Spec k`, and an actual
full marking. It uses the literal `sectionAxisSubgroup`, its proved direct
killing instance, and its proved étale structure map. Thus the subgroup
étaleness hypothesis is supplied for this particular construction. No
Noetherian, characteristic-zero, or algebraically-closed-field assumption
is added.

The two actual examples check the public chosen-killing interface and the
literal subgroup/quotient attached to a native full complex point at level
3. The level-3 example explicitly types the native curve and subgroup,
matching the already reviewed finite/injective fixture. This leaf proves a
generic function-field property; it supplies no quotient elliptic-curve
model, genus, target j-invariant, or valuation/place ramification theorem.

The accepted temporary fixture has 85 lines, SHA-256
`88287dd6d8b6892a22b10940ed7c33805de755ec6ea81e99361f6e4ba83aa12f`.
Strict session 76758 exited 0 with ten standard-three-axiom checks, two actual
examples, and zero diagnostics. Root read the actual source and complete
log before authorizing retention. A setup-only preflight failure, caused
by a scanner treating an upstream comment as an import, is preserved and
excluded from the green receipt. No mathematical source repair was needed.
Temporary log: `/private/tmp/YZeroSubgroupQuotientFunctionFieldEtaleProbe-first.log`.
Receipt: `/private/tmp/YZeroSubgroupQuotientFunctionFieldEtaleProbe-receipt.json`.

The retained source has 106 lines, SHA-256
`72f5ec021866bb0ec7cce478fbccb14a737cb5c03a45fe748fb7b0653e6b874c`.
The accepted mathematical suffix, including all hypotheses, proofs, two
examples, and ten prints, is byte-preserved; only the license and scope
documentation are added. Maximum Lean line width is 92. Correct-name strict
session 75417 exited 0 with ten checks using exactly `propext`,
`Classical.choice`, and `Quot.sound`, two examples, and zero warnings/errors
or `sorryAx`. Retained and isolated source copies are byte-equal.

Named log: `/private/tmp/xyin-y0-subgroup-quotient-function-field-etale.log`.
Receipt: `/private/tmp/YZeroCoarseSubgroupQuotientFunctionFieldEtale-receipt.json`.
The receipt records exact source/setup/log hashes and all six canonical
Lean artifacts plus the C output. This named-module check is distinct from
a later cumulative retained-library gate.

The isolated pins are AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`,
mathlib `300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
Setup `/private/tmp/YZeroCoarseSubgroupQuotientFunctionFieldEtale.setup.json`
names `AINTLIBDrafts.YZeroCoarseSubgroupQuotientFunctionFieldEtale`, disables
both implicit options, and loads no plugins or dynamic libraries. The exact
command from `/private/tmp/xyin-y0-aintlib-work` was:

```sh
LEAN_PATH=.lake/build/lib/lean:.lake/packages/mathlib/.lake/build/lib/lean:.lake/packages/batteries/.lake/build/lib/lean:.lake/packages/Qq/.lake/build/lib/lean:.lake/packages/aesop/.lake/build/lib/lean:.lake/packages/plausible/.lake/build/lib/lean:.lake/packages/importGraph/.lake/build/lib/lean:.lake/packages/LeanSearchClient/.lake/build/lib/lean:.lake/packages/proofwidgets/.lake/build/lib/lean:.lake/packages/Cli/.lake/build/lib/lean /private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false --setup /private/tmp/YZeroCoarseSubgroupQuotientFunctionFieldEtale.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionFieldEtale.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionFieldEtale.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionFieldEtale.c AINTLIBDrafts/YZeroCoarseSubgroupQuotientFunctionFieldEtale.lean > /private/tmp/xyin-y0-subgroup-quotient-function-field-etale.log 2>&1
```

Other frozen leaves, upstream source, the toolchain, and runtime settings
were unchanged.
