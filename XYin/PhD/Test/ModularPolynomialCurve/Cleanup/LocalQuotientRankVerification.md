# Actual local quotient rank verification

The retained module `AINTLIBDrafts.YZeroCoarseLocalQuotientRank` proves
`AffineChartPatch.localQuotientπ_finrank P r hG x`: the actual canonical local
quotient projection has fibre finrank `r` at every target point when `G.HasRank r`.
The only additional hypothesis is `Module.Free P.baseRing P.groupRing`, required
by the actual chart Hopf datum. No Noetherian, étale, domain or model premise is
introduced. The canonical target is literally the Spec of the coinvariant algebra;
raw-subring/global quotient rank and function-field degree are not asserted here.

The genuine Hopf faithfully flat inclusion lifts each target prime to the chart
ring. The retained Hopf stalk-rank comparison identifies the quotient-module rank
with the actual group-chart rank at the prime's base comap, where the genuine
subgroup `HasRank` theorem applies. The actual finite flat Spec-map rank formula,
followed by the source affine isomorphism, identifies the scheme fibre rank.

The two actual API examples check supplied `HasRank r` on an arbitrary patch and
the literal marked-axis subgroup's rank `N`. This is a consequence of the actual
`sectionAxisSubgroup_hasRank` proof, with the patch freeness still explicit.

## Exact verification

- Temporary check: session 71160 CLOSED exit 0 on its first run; no failed staging
  proof or diagnostic was involved.
- Approved temporary source: 73 lines, SHA `6740ab023d66988393317aa36653825d5af3e748c639144b38e24c0f56cd6c20`.
- Retained source: 93 lines, width 93, SHA `166f822db5c6f1068b521689753542909b31ee2aac0c41ceda6e34f030941ce4`.
- Retained and isolated copies are byte-identical; the complete suffix beginning
  `@[expose] public section` is byte-identical to the approved temporary source.
- Correct-name emission: session 26773 CLOSED exit 0, using pinned Lean 4.35.0-rc3.
  Setup name is `AINTLIBDrafts.YZeroCoarseLocalQuotientRank`, with both implicit-variable options false and
  9457 available normalized imports.
- Exact 13 printed declarations all use only `propext`, `Classical.choice`, and
  `Quot.sound`; both actual API examples passed. Own errors/warnings: zero.
- Log: `/private/tmp/xyin-y0-local-quotient-rank-check.log`; SHA `ca49a6f42120294014724a8b1bac91045c2c9527dbeb638d169e73ea675c50b9`.
- Setup SHA: `ac1e4da18acf817abaec089d1411719668a0682f58e021b54aa8f61f4a204a78`.
- Six Lean artifacts and the explicit C output were inspected as nonempty.
  Artifact sizes: 12416, 71768, 2120, 18474, 176, 2272; C 4717 bytes.
- Machine receipt (command, all source/setup/log/artifact hashes and printed names):
  `/private/tmp/xyin-y0-local-quotient-rank-receipt.json`.

No global build, environment/model/settings change or user checkout build was
performed for this bounded named check. The approved probe and this retained
source are frozen after the receipt.
