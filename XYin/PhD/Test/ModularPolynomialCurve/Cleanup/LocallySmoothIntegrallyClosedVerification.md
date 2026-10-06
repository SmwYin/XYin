# Locally standard-smooth curve normality

The retained `AINTLIBDrafts.LocallySmoothIntegrallyClosed` was checked in the
isolated pinned AINTLIB environment (Lean 4.35.0-rc3), without changing the
XYin toolchain. Named compiler session **28410 CLOSED, exit 0**.

- Source SHA256: `fe56a5c6e67640283afabbc037c7ab87fc3f32568ff21f4abeffafad275f15f5`.
- Full log: `/private/tmp/xyin-y0-locally-smooth-integrally-closed.log`;
  SHA256 `63622dd6fe4cf2c314385a23543d8110f3fd057de3e2a21df11a5bc99bcac905`.
- Exact receipt: `/private/tmp/LocallySmoothIntegrallyClosed-receipt.json`.
- Nine printed declarations have precisely `propext`, `Classical.choice`,
  and `Quot.sound`; two API examples compile; zero module diagnostics.
- Retained and isolated sources agree byte for byte. The accepted temporary
  proof suffix is unchanged. All six canonical outputs and the C output have
  the recorded hashes. Setup names the actual module, disables both implicit
  variable options, and has no plugins or dynamic libraries.

The theorem assumes a domain algebra over a field and the literal locally
standard-smooth relative-dimension-one scalar map. It extracts its basic-open
cover, proves each nonzero away localization integrally closed using the
native standard-smooth theorem, and applies the separately checked unit-span
localization criterion. It does not assume global standard smoothness,
Noetherianity, normality, a genus, or a curve model. The examples exercise a
global standard-smooth algebra and the polynomial line with its actual native
standard-smooth instance.

The temporary proof's first failure was a missing parenthesis around an
equivalence with a named argument. The second was a missing setup import
artifact before elaboration. Both failed sources and logs were preserved;
only the final successful output is counted. Native dependency build warnings
are recorded separately from this module's zero-diagnostic log.

This leaf was added after the cumulative 76-module checkpoint and is not
claimed as part of that receipt. Independent source and mathematical review
accepted the temporary proof; the next cumulative audit will check the final
named leaf again with its clients.
