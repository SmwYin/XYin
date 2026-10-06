# Principal-divisor pullback verification

`AINTLIBDrafts.PrincipalDivisorPullback` proves the generic principal-divisor compatibility formula for a field algebra homomorphism `φ : L →ₐ[k] K` and a finite-fiber place map `r : Place k K → Place k L`. Its explicit normalized valuation restriction hypothesis is `(r v).valuation z = v.valuation (φ z)` for every `v,z`. Coefficients are compared using the actual valuation/principal-divisor formula, injectivity of `WithZero.exp`, and injectivity of negation. The additive finite-fiber pullback retains coefficient `D (r v)`.

Each field has its own independent base algebra and the explicit existing polynomial/RatFunc scalar towers, function-field structure and separability required by the current principal-divisor API. There is no assumed relation between their chart parameters, full constant field, genus or scheme model. The theorem does not claim invariance of the current principal-divisor definition under a change of chart. No actual quotient wrapper is included. The identity example uses true singleton fibers; the second example obtains the pointwise principal coefficient equation from the bundled divisor equality.

Parent independently read the complete accepted temporary 69-line source, full successful second output, strict setup and hashes before promotion. The retained 88-line source adds only license/scope documentation; its `@[expose] public section` mathematical suffix is byte-identical to the accepted source. The first failed source/log is preserved and excluded. The only repair was an explicitly typed actual mapped unit and its `rfl` value equation, plus singleton-fiber proof style; no options, mathematical hypotheses or linter settings were changed.

Named session **59554** was owner-polled **CLOSED, exit 0**. Full log has exactly **9** permitted checks: five standard-three, `WithZero.exp_injective` using `propext`/`Quot.sound`, axiom-free `neg_injective`, and `Units.map`/`Units.coe_map` using only `propext`. Both API examples pass, with zero diagnostics. Combined bounded parser preserves exact declaration names and axiom-free outputs. Strict setup has `autoImplicit=false`, `relaxedAutoImplicit=false`, no plugins/dynlibs and the exact named module. All six canonical Lean outputs plus C output were inspected and hashed.

- Source SHA256: `76effc965b8be75b79fbadd383004a16461d3303a476b4563f12d0e081183de2`.
- Setup SHA256: `36299c0b476487a4ace48e37d70434c04d062635280df516241e829d6aeff0df`.
- Full log SHA256: `c20419a0658dd077acba1846a7a716b00945ba258bc3420359ab9f3b7227d37e`.
- Exact receipt: `/private/tmp/xyin-y0-principal-divisor-pullback-receipt.json`.
- Full log: `/private/tmp/xyin-y0-principal-divisor-pullback.log`.
- Pinned AINTLIB: `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`; mathlib: `300d0e535721bc098547106fc297d8ba2a63f6bb`; Lean: `leanprover/lean4:v4.35.0-rc3`.

Reproduce in `/private/tmp/xyin-y0-aintlib-work` with:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/PrincipalDivisorPullback.lean --setup PrincipalDivisorPullback.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/PrincipalDivisorPullback.olean -i .lake/build/lib/lean/AINTLIBDrafts/PrincipalDivisorPullback.ilean -c .lake/build/ir/AINTLIBDrafts/PrincipalDivisorPullback.c > /private/tmp/xyin-y0-principal-divisor-pullback.log 2>&1
```

This leaf is outside the last cumulative 126-module checkpoint. Retained source and output are frozen pending parent review.
