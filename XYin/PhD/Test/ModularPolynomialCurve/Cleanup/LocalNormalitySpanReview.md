# Independent localization-span integral-closed review

Read the complete root-owned 63-line `/private/tmp/xyin-y0-aintlib-work/YZeroLocalNormalitySpanProbe.lean` and full successful second log
`/private/tmp/YZeroLocalNormalitySpanProbe-second.log`. Independently checked their hashes and the exact strict setup against
`/private/tmp/YZeroLocalNormalitySpanProbe-receipt.json`. Root's receipt confirms
51823 CLOSED exit 0; this reviewer ran no compiler and edited no root source.
Eight prints are exactly standard-three, two examples remain, and diagnostics
are zero. First failed source/log are excluded from this verdict.

Verdict: **PASS**. The theorem uses a genuinely unit-spanning set and requires
integral-closedness of away rings only at its nonzero elements. For a zero
cover member, exponent one annihilates the tested fraction, so no impossible
zero-localization domain premise is required. For a nonzero cover member,
powers lie in the source non-zero-divisors. The embedded localization
`Localization.subalgebra (FractionRing R)` uses the actual canonical source
scalar, has its genuine fraction-field structure in the same ambient field,
and is ring-isomorphic to the abstract away localization. Its integral-closed
instance therefore transfers along that actual equivalence. `hx.tower_top`
is justified by the embedded scalar tower, not an independently invented
ambient embedding.

Away surjectivity supplies a denominator power. Applying the embedded ring's
ambient algebra map to its denominator equality and using the genuine scalar
tower yields a power multiple of the fraction in the original source-image
submodule. `Submodule.mem_of_span_eq_top_of_smul_pow_mem` then returns membership
in that same source image; `exact hm` is exactly the existential witness in
`isIntegrallyClosed_iff`. No source integral-closedness is assumed in the theorem;
it appears only in the first preservation sanity. The singleton-one sanity
checks the cover endpoint. No finite, Noetherian, curve, or dimension premise
is hidden.

Source SHA `9758108e8b856b70811adb18bde097992ee6e11fcb48c024efc270f327107d58`; setup SHA `b7f45c2703c552b2137e1d28bc3c0720379d3d6ebbf546fdac9677c76d59e2ad`;
second-log SHA `52f705dc631c40c45d2241f8d3f028b041745ef93a7204b52e3513b9fee5e468`. The proof is scope-complete and ready for
retention. The source's longest line is 102 characters, a minor formatting item
for its owner; it does not affect mathematics or the strict receipt.

## Independent named cover follow-up

Read the complete named 81-line `AINTLIBDrafts.IntegrallyClosedLocalizationCover`
source and full eight-print named log, then checked actual files against
`/private/tmp/IntegrallyClosedLocalizationCover-receipt.json`. The accepted 63-line mathematical suffix is token-identical under
whitespace removal; the only proof-line delta is the requested parenthesized
line wrap, resolving the earlier 102-character formatting note. The source
width is now 87. License/scope additions accurately describe the same theorem.
Mathematical verdict remains **PASS** for the zero-cover case, actual embedded
localization scalar tower, and final source-image membership argument.

Named source SHA `49bb58dfd5dfb31c9b6fc5e7b135683c305eecff5600bf12a8395de689d0329c`; correct-module strict setup SHA
`0f81b5ab9c8375e756bad6cfc8eb1f9b826730acb418f193f6c82d678a00c682`; full-log SHA `52f705dc631c40c45d2241f8d3f028b041745ef93a7204b52e3513b9fee5e468` all match. Retained/work
copies agree. Both implicit-variable options are false, plugins/dynlibs empty,
eight prints exactly standard-three, two examples and zero diagnostics. Root's
receipt records actual 41277 CLOSED exit 0; no reviewer compiler was run.
All six canonical outputs plus C were nonempty and independently size/SHA-checked:
11336, 123440, 1592, 7659, 2032, 176, 4152 bytes.
Named proof and artifact provenance: **PASS**.
