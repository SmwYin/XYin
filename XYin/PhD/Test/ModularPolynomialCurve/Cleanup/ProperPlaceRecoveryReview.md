# Proper place recovery: independent temporary review

**PASS.** Read the complete 86-line `YZeroProperPlaceRecoveryProbe.lean`, its actual closed-point-place, centre-stalk-square and proper-closed-centre dependencies, full first log, strict setup, and receipt. No compiler or Lean edits were performed for this review.

At the genuine lift centre `x`, the proof installs the original geometric stalk scalar map from `π`, its true tower to the function field, and the DVR supplied by smooth relative dimension one and actual closedness. Unfolding `closedPointPlace` therefore produces the very same DVR constructor as the generic recovery theorem, with no transported scalar structures.

The already proved centre-stalk square identifies the **canonical** stalk-to-function-field image with the composite through the given place's valuation ring. Evaluating that equality at `a` and reversing it makes image membership the genuine subtype membership of `stalkClosedPointTo l a`. Thus the image inclusion required by DVR recovery is proved from the actual generic-lift triangle, rather than assumed. The valuation-ring overring argument then recovers the original intrinsic place. The generic lemma does not require properness or an over-base lift triangle once the closed centre and generic triangle are provided.

The proper wrapper obtains a real lift and a closed centre from the existing proper-lift theorem. Residue finiteness is explicitly retained as `Module.Finite k v.residueField`; no theorem that all residues are finite, point injectivity, place bijection, or genus conclusion is claimed. Both examples specialize directly to actual native elliptic curves over `Spec k`.

Owner **85598 CLOSED exit 0** is confirmed by the owner and `/private/tmp/YZeroProperPlaceRecoveryProbe-receipt.json`. The reviewer did not poll the owner's process. Independently parsed the full log: exactly twelve standard-three axiom prints, two genuine native API examples, no diagnostics or `sorryAx`. Setup name is correct, both implicit flags are false, and plugins/dynlibs are empty. This was a first-attempt no-output probe, so no artifacts are claimed.

Independently recomputed exact hashes:

- Source: `93b4db4d141837d501ca621bfeeb19ecc9eb6cd7546b485273626646649e9dbc`.
- Setup: `42128f1f59e24f029dbcdc2888c061df7616f55de1240232c7b5f21a0e18fca9`.
- Full first log: `8ea008932dc451b4d140a5eebc90aa1def4b022806bcc17d291ad2b67e663fab`.

No mathematical or scalar-alignment issue identified. Any later retained named source and artifacts need their separate provenance receipt.

## Named current receipt

Subsequently inspected the complete retained **104-line** `AINTLIBDrafts.ProperPlaceRecovery` and its full named log. **PASS**: accepted 86-line expose suffix is byte-exact; retained/work copies agree. Owner **18121 CLOSED exit 0**, twelve exact standard-three prints, two native APIs, no diagnostics, strict correct-name setup with no plugins/dynlibs. Independently recomputed source `7a8d054c38861b19b36ed71cc8a866c5f9ebb6e94f30c92364732adadde3847d`, setup `00e2f2ee7b057d2d8b77747e9581a62c10a07a2f36533720a83edf87c63e574f`, and the same full-log SHA. All six canonical artifact sizes/hashes plus C match `/private/tmp/xyin-y0-proper-place-recovery-receipt.json`: **39800 / 105832 / 1896 / 15770 / 1800 / 176**, C **4444**. No reviewer compiler or Lean mutation.
