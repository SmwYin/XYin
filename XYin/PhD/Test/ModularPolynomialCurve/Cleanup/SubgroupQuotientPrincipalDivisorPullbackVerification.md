# Actual quotient principal-divisor compatibility verification

`AINTLIBDrafts.YZeroCoarseSubgroupQuotientPrincipalDivisorPullback` proves raw and public principal-divisor compatibility over a characteristic-zero field for an actual finite locally free subgroup with `Etale G.π` and its genuine nonzero killing witness. The actual quotient's additive divisor pullback sends a principal divisor to the principal divisor of the literal native function-field map. The proof instantiates the generic principal pullback theorem using the actual base-field algebra homomorphism, place map, finite fibers and proved normalized valuation restriction.

Both base-field algebras remain the independent geometric structure-map/generic-germ algebras. The source gets its already proved native polynomial/RatFunc towers, FunctionField structure and separability. Every supplied target transcendental parameter `τ,ht` gets actual aeval and parameter-embedding scalars, with towers/finiteness and characteristic-zero separability derived from the existing actual quotient API. The current principal-divisor definitions still require their chart packs; no caller-provided chart, separating, scalar-compatibility, model or genus premise is introduced. No source coordinate is assumed to factor through the quotient. The public wrapper is exactly the actual chosen killing integer and witness. The two examples check both actual interfaces.

Parent independently read the complete accepted temporary173 source, full second15 output, strict setup/current hashes and owner closure; the invariant worker independently checked the same full source/log/failed-delta and scalar orientation. The retained198 module adds only the license/scope documentation, with its `@[expose] public section` suffix byte-identical to accepted173. The first174 failed source/log is archived and excluded: the only diagnostic was a redundant second `dsimp` after the first had already simplified the nested lets. Removing that tactic did not change the mathematical statement or inputs. No option/linter/settings change occurred.

Named session **27296** was owner-polled **CLOSED, exit 0**. Full output has exactly **15** standard-three checks and **2** actual raw/public API examples, with zero diagnostics. The bounded combined parser handles multiline axiom lists without changing declaration names or permitted subsets. Strict setup has `autoImplicit=false`, `relaxedAutoImplicit=false`, no plugins/dynlibs and the exact named module. All six canonical Lean outputs plus C output were inspected and hashed; both source copies match.

- Source SHA256: `1858a819152f7fa1281f9e94dcf1f3cf7d3c1505dbd03a00dde8a53c2655a5da`.
- Setup SHA256: `97448496fb88dc0112a62c28c4c2e0e9933eb5e9b2e615f7b0d30a7a75969b9c`.
- Full log SHA256: `4aae252a9c77f550b342f87f5837f6a8c3a51fb702facfeaa359a937dad2154d`.
- Exact receipt: `/private/tmp/xyin-y0-subgroup-quotient-principal-divisor-pullback-receipt.json`.
- Full log: `/private/tmp/xyin-y0-subgroup-quotient-principal-divisor-pullback.log`.
- AINTLIB: `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`; mathlib: `300d0e535721bc098547106fc297d8ba2a63f6bb`; Lean: `leanprover/lean4:v4.35.0-rc3`.

Reproduce in `/private/tmp/xyin-y0-aintlib-work` with:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/YZeroCoarseSubgroupQuotientPrincipalDivisorPullback.lean --setup YZeroCoarseSubgroupQuotientPrincipalDivisorPullback.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientPrincipalDivisorPullback.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseSubgroupQuotientPrincipalDivisorPullback.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseSubgroupQuotientPrincipalDivisorPullback.c > /private/tmp/xyin-y0-subgroup-quotient-principal-divisor-pullback.log 2>&1
```

This leaf is outside the historical cumulative126 checkpoint and is now included in the successful final cumulative135 checkpoint and independent audit. It establishes principal-divisor compatibility; it does not establish a canonical/Weil-differential pullback, Riemann–Hurwitz, quotient genus, a quotient Weierstrass model or quotient-j/modular-polynomial equation. Owned source, setup, receipts and compiler work remain frozen.
