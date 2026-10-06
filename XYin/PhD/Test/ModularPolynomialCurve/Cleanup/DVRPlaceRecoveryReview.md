# DVR place recovery: independent review

**PASS.** Read the complete retained 52-line `DVRPlaceRecovery.lean`, its imported `DVRPlace.lean`, the actual valuation-overring and discrete-valuation primitives, and the full named log/setup/receipt. This was a read-only review; no Lean source or compiler invocation was changed or run.

The hypothesis is membership of the **literal image** of `algebraMap A K` in the given place `v`. The already proved `mem_ofDiscreteValuationRing_iff` identifies this image with the valuation subring of the DVR place, so the proof establishes the correct inclusion `ofDiscreteValuationRing.toValuationSubring ≤ v.toValuationSubring`. It then uses `v.ne_top`, which is an actual field of the intrinsic `Place` definition, rather than an assumed nontriviality result about a geometric centre.

Mathlib `ValuationSubring.lean:402–414` states that an overring of a valuation subring of Krull dimension at most one is either the original subring or the whole field. The actual DVR adic valuation subring is a discrete valuation ring (`Valuation/Discrete/Basic.lean:445`) and hence has Krull dimension at most one (`DiscreteValuationRing/TFAE.lean:256`). Thus the selected `eq_of_le_of_ne_top` direction is sound. `Place.ext` needs only equality of the valuation subrings; normalization data is propositional. No geometric properness, closedness, bijection, or centre-recovery claim is used.

The two examples check actual DVR-image membership and recovery in the reverse equality direction. Both independent constant-field algebra structures are the supplied genuine tower; nothing is replaced by a transported scalar structure.

Named verification: owner session **76948 CLOSED exit 0**, confirmed by the owner's message and `/private/tmp/DVRPlaceRecovery-receipt.json`. The reviewer did not poll the owner's process. The full log contains exactly four standard-three axiom prints and no diagnostics or `sorryAx`. The setup is named `AINTLIBDrafts.DVRPlaceRecovery`, both implicit flags are false, and plugins/dynlibs are empty.

Independently recomputed hashes:

- Retained and isolated source, byte-equal: `a2898ea3380d6620bebb93712d40b26daf59be631e7648134407bb763489d974`.
- Setup: `8299b15c59c712b67501ba2ee2d02be014acce6a7282371228fe53434863798d`.
- Full named log: `7b25752b5db4760d69160a8e20fce56865d7b261430769d74ff0ab7404ec4d6b`.

All six canonical artifact hashes and sizes, plus the C output, match the receipt: respectively **15384 / 24520 / 1440 / 5316 / 1848 / 176** bytes and C **3383** bytes. These are the current named artifacts, independently inspected before any later cumulative gate. No issue identified.
