# ConstantAxisEtale independent review

Review date: 2026-10-04. **Verdict: PASS for the retained source and named strict
receipt.** This reviewer edited only this report, with no Lean edits or compiler
invocations.

[YZeroCoarseConstantAxisEtale.lean](/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/YZeroCoarseConstantAxisEtale.lean)
has 71 lines and SHA-256
`5643897d64343233f0f7ad7834460172950448b149a415f93b545538e60248bb`.
The accepted temporary source had 47 lines and SHA-256
`1636bb90b52421269982a1cff1adb7b722de31dc488cf3216bb490bf058e4854`.
The actual retained delta is only the license, module exposition, and three
docstrings. Statements, proofs, five axiom prints, and two examples are
unchanged. Retained and isolated sources were independently checked byte-equal.

The generic `constSchemeProjection_etale` holds over every scheme `S` and every
finite label type `A`. The actual pinned `GroupScheme/MuN.lean:114` defines
`constScheme S A` as a coproduct of copies of `S`; `:118` defines its projection
as `Sigma.desc` of identities. Source-locality of étaleness therefore reduces
the conclusion to étaleness of those identity maps.

The explicit local term `HasRingHomProperty.instIsZariskiLocalAtSource` fixes
both `P := @Etale` and `Q := RingHom.Etale`. This is the existing mathlib
instance, with its parameters specified to repair implicit-property
unification in the pinned compatibility context. It introduces neither an
additional mathematical hypothesis nor a new global instance. The actual
source-local coproduct primitive is at `Morphisms/Basic.lean:303`.

For `sectionAxisSubgroup_etale`, the subgroup's actual structure morphism is
`sectionAxis E L.val.1 ≫ E.π`. The checked `sectionAxis_π` rewrites it to the
literal constant projection, so the generic result applies directly. The
native full-point wrapper instantiates the same actual pullback curve,
marking, and subgroup constructor. Base invertibility is used by that existing
subgroup constructor, not by generic constant-projection étaleness.

Named artifact emission session 1802 closed exit 0. The actual log
`/private/tmp/xyin-y0-constant-axis-etale.log` has five exact standard-three
axiom prints and no diagnostics. The arbitrary-base `ZMod 5` example and
actual native full-point level-3 example pass.

The actual setup names `AINTLIBDrafts.YZeroCoarseConstantAxisEtale`, sets both
implicit-variable options to `false`, and contains no plugins or dynamic
libraries. Canonical sizes were independently checked: `.olean` 12728 bytes,
`.olean.private` 15584, `.olean.server` 2888, `.ilean` 11721, `.ir` 1784,
and `.ir.sig` 176. The previous temporary failures and diagnostic trace had
recovery-stage `sorryAx` outputs; all are excluded. The accepted final temporary
run 92440 also closed exit 0 with five standard-three prints and no diagnostics.

This establishes étaleness of the **subgroup structure map** `G.π`, for the
literal marked constant axis. It supplies the explicit geometric input in the
checked chart étale theorems. The module itself does not claim the quotient
projection `G.quotientπ` étale or upgrade the quotient to an elliptic curve.
