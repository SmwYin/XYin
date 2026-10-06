# Place centre stalk square: independent temporary review

**PASS** for the exact 70-line temporary source `YZeroPlaceCenterStalkSquareProbe.lean`. Read the complete proof, both examples, full second log/setup/receipt, and actual mathlib stalk/specialization APIs. No compiler or Lean edits were made by the reviewer.

The centre is the literal image of the closed point of the local source ring. Its canonical stalk-to-function-field algebra map is exactly `stalkSpecializes` from that centre to the generic stalk. Contravariance of `Spec.map` is handled in the correct order. The proof cancels the actual mono `fromSpecStalk centre`, uses the genuine factorization of the lift through that stalk, and compares it to the actual specialization triangle. It derives the ring square from the stated generic scheme triangle; it does not assume the ring square. No closedness, properness, DVR, or place-classification assumption is present in the theorem. The place example uses its actual valuation-ring embedding.

Owner session **9017 CLOSED exit 0** is confirmed by the owner and `/private/tmp/YZeroPlaceCenterStalkSquareProbe-receipt.json`; the reviewer did not poll that process. The full second log has exactly seven standard-three prints and axiom-free `CategoryTheory.cancel_mono`, two real API examples, and no diagnostics. The strict setup has the correct temporary name, both implicit flags false, and no plugins/dynlibs. The archived first failed attempt is excluded. No temporary artifacts are claimed.

All three hashes were independently recomputed and match:

- Source: `1e01a033c241ebfeed3306a15155e2d3ae84c6fbd8cb2f9478e3be0423a5425c`.
- Setup: `995c7cca7da8501523f1abeea9456dbeb7335d7a147caa15024c73cd31e974a5`.
- Full second log: `8ff55d3239501bd4cc8aa96638e18b170adb9249940b8b75e88ce5ea9381ccea`.

Source-backed generality observation: the theorem's proof needs only `IrreducibleSpace X`, as does the literal `stalkFunctionFieldAlgebra` definition. The place client still needs an integral scheme for its function field to be a field. Parent approved this separate weakening; this historical review does not claim to certify the later named artifacts.

## Named generality change and current provenance

Also read the complete **89-line** named `AINTLIBDrafts.PlaceCenterStalkSquare` and full named log. **PASS**: after exactly the approved generic `IsIntegral` to `IrreducibleSpace` binder change and adding `IsIntegral` to the place example, the entire accepted expose suffix is byte-exact. Proof maps and directions are unchanged; retained/work copies agree. Owner **57159 CLOSED exit 0**, seven standard-three prints plus axiom-free cancellation, two APIs, no diagnostics. Strict name/implicit flags/empty plugins and dynlibs agree. Independently recomputed source `8378448602451a011e8d0a504cedd9dd816d89fc8d98cc5c586566dfd133a986`, setup `25e135f8afc4d01062c8f5e4b62b179641cd771c165036e495d5991a4c8451df`, and the same full-log SHA. All six canonical artifact hashes/sizes plus C match `/private/tmp/xyin-y0-place-center-stalk-square-receipt.json`: **19080 / 22712 / 1744 / 11355 / 1784 / 176**, C **3470**. No compiler or Lean edits by this reviewer.
