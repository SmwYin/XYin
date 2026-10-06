# Finite-fiber Finsupp pullback verification

`AINTLIBDrafts.FinsuppFiniteFiberPullback` defines a coefficient pullback along an arbitrary map with finite fibers. The support lemma needs only `Zero M`; the additive homomorphism needs only `AddZeroClass M`. No injectivity, scheme, principal-divisor compatibility, genus or Weierstrass model input enters the statements.

The coefficient formula is definitionally `D (r a)`. Existing `Finsupp.comapDomain` (Mathlib/Data/Finsupp/Basic.lean:509,614) and the corresponding DFinsupp API (Defs.lean:1042) require injectivity and do not fit a finite quotient. This proof reuses `Finsupp.hasFiniteSupport`/`ofSupportFinite` (Defs.lean:193,275) and `Set.Finite.preimage'` (Set/Finite/Lattice.lean:213). The explicit Bool-to-Unit example pulls coefficient 3 back to both points, so its sanity check genuinely uses a noninjective map. The second example checks addition coefficientwise.

Parent reviewed the complete accepted 62-line temporary proof and its successful third log before promotion. The retained 81-line module adds only the license and scope documentation: its `@[expose] public section` suffix is byte-identical to the accepted temporary source. The first two failed source/log snapshots are preserved and excluded; they concern the `Function.HasFiniteSupport` namespace and explicit inclusion of the proof-only fiber parameter. No options or assumptions were changed to suppress diagnostics.

Named emission session **26130** was owner-polled **CLOSED, exit 0**. Full output contains exactly **9** declared axiom checks, all `propext`, `Classical.choice`, `Quot.sound`, and **2** API examples passed with zero warnings/errors. The parser accepts the embedded apostrophe in `Set.Finite.preimage'`. Strict setup has `autoImplicit=false`, `relaxedAutoImplicit=false`, no plugins/dynlibs and the exact named module. All six canonical Lean outputs and C output were inspected and hashed.

- Source SHA256: `c0f43e6848629ec55baa6b9c0e8ded5d81a2d794599e5c03ce51311136288a2c`.
- Setup SHA256: `f4c09617909233377ccbb8eae1a0101925edc3f634b26465c26e06f4aa706d22`.
- Full log SHA256: `47b6e029dfadb08cfaf2f9a1993e3c1686da7b507431b8149acadd1be08f3827`.
- Full exact receipt: `/private/tmp/xyin-y0-finsupp-finite-fiber-pullback-receipt.json`.
- Full log: `/private/tmp/xyin-y0-finsupp-finite-fiber-pullback.log`.
- Pinned AINTLIB: `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`; mathlib: `300d0e535721bc098547106fc297d8ba2a63f6bb`; Lean: `leanprover/lean4:v4.35.0-rc3`.

Reproduce in `/private/tmp/xyin-y0-aintlib-work` with:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean AINTLIBDrafts/FinsuppFiniteFiberPullback.lean --setup FinsuppFiniteFiberPullback.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/FinsuppFiniteFiberPullback.olean -i .lake/build/lib/lean/AINTLIBDrafts/FinsuppFiniteFiberPullback.ilean -c .lake/build/ir/AINTLIBDrafts/FinsuppFiniteFiberPullback.c > /private/tmp/xyin-y0-finsupp-finite-fiber-pullback.log 2>&1
```

This leaf is outside the last cumulative 126-module checkpoint. It proves the standalone finite-fiber additive API; it does not yet instantiate a quotient divisor pullback or prove principal-divisor compatibility. Retained source and named output are now frozen pending parent review.
