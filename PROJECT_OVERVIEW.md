# Project Overview: ForMathlib NumberTheory and RingTheory

Generated: 2026-11-04.

**Scope.** `XYin/ForMathlib/NumberTheory/**` and `XYin/ForMathlib/RingTheory/**` (18 files) at commit `c9c68e0`,
Lean 4.35.0, mathlib `56a00585` (13 Oct 2026). `ForMathlib/LinearAlgebra` (HNF) is out of scope. Its overview of
2026-10-20 is archived at `.mathlib-quality/overview/hnf-2026-10-19/PROJECT_OVERVIEW-hnf-2026-10-20.md`.

**How this was produced.**
- `/overview` Steps 1–8 were run. Step 9 (one full `/mathlibable` per declaration) was skipped at your request, so
  Part 8 is a triage list, not a set of verdicts.
- The per-declaration inventory was written by six read-only agents, one per file group. The full entries are in
  `.mathlib-quality/overview/formathlib-nt-rt-2026-11-04/inventory/` (links in Part 1).
- A script confirmed that all 370 declarations appear there, each with What, How, Hypotheses and Uses-from-project
  fields.
- **Build evidence.** `lake build` of the four leaf modules `JFunction.Properties`, `JFunction.EllipticCurve`,
  `QExpansion.ModularForm` and `QExpansion.Degenerate`, which together import all 18 files, passed: 3,860 jobs,
  0 errors, 30 warnings.
- **Evidence marks.** "(checked)" means confirmed against mathlib source or in Lean, by me or by an inventory agent.
  "(not checked)" means argued only.

**Abbreviations used below.** These are path prefixes under `XYin/ForMathlib/NumberTheory/` unless stated otherwise.

| short | file |
|---|---|
| QE/Basic, QE/CuspReps, QE/ChangeRep, QE/Algebra, QE/ModularForm, QE/Order, QE/Degenerate | `ModularForms/QExpansion/{Basic,CuspRepresentatives,ChangeRepresentative,Algebra,ModularForm,Order,Degenerate}.lean` |
| Δ/QExp | `ModularForms/Discriminant/QExpansion.lean` |
| E/QExp | `ModularForms/EisensteinSeries/QExpansion.lean` |
| LQE/Basic, LQE/Algebra, LQE/Convergence | `ModularFunctions/LaurentQExpansion/{Basic,Algebra,Convergence}.lean` |
| J/Basic, J/QExp, J/Properties, J/Lattice, J/EllipticCurve | `ModularFunctions/JFunction/{Basic,QExpansion,Properties,Lattice,EllipticCurve}.lean` |
| HasCoeffsIn | `XYin/ForMathlib/RingTheory/PowerSeries/HasCoeffsIn.lean` |

---

## Executive Summary

The folder stages three pieces of mathematics for mathlib, none of which is in the pinned version:

1. **q-expansions at an arbitrary cusp representative.** These are `Subgroup.strictWidthAt` and
   `SlashInvariantForm.qExpansionAt`, with the invariance and rescaling laws under change of representative.
2. **Laurent q-expansions at ∞ for functions meromorphic at the cusp.** These are `poleOrder`, `poleRemoved`,
   `toQExpansion` and `laurentqExpansion`, with ring-operation laws, change of period, convergence, uniqueness and a
   Cauchy formula.
3. **The arithmetic application.**
   - Integral power series (`HasCoeffsIn`).
   - Integrality of the q-expansions of E₄, E₆ and Δ, and Ramanujan's τ.
   - The j-function, its integral Laurent expansion and special values.
   - The link from complex lattices and Weierstrass curves to the analytic j.

The mathematics is sound. Everything compiles without `sorry`, and no proof is longer than 30 lines.

**The folder is a snapshot copy, not the source of truth.** This is the most important finding.

- All 370 declaration names are also declared, in the same namespace, in live files under `XYin/PhD/`.
- Eleven of the 18 files differ from their PhD originals at most in the import line.
- No module reachable from `XYin.lean` imports any of these files. The default `lake build` and CI therefore never
  check them; the oleans exist only because someone built them by hand.
- The two trees can never be imported together.
- The port has already drifted. It dropped lemmas the PhD copy still has (`cuspFunction_apply_of_ne_zero`,
  `PeriodPair.j_smul`, `j_congr`, `qjCoeffs_one = 744`, …).

Decide which tree is canonical before doing anything else (Priority 0).

**Mathlib-alignment findings**, in order of payoff:

- **(a) `qExpansionAt` is a wrapper around mathlib.** `qExpansionAt γ f` is by definition mathlib's `qExpansion` of
  `SlashInvariantForm.translate f γ`, at the strict width of the conjugated level (checked: the coercion of
  `translate f g` is `f ∣[k] g`, NormTrace.lean:43–49). About 20 lemmas in QE/Basic, QE/Algebra, QE/ModularForm and
  QE/Order re-prove mathlib's at-∞ API for that translate. One bridge lemma makes them corollaries, and about 15 of
  them have no users anyway.
- **(b) The Laurent layer is new to mathlib, but its design should change before it is offered.**
  - The mathematics is generic: the Laurent series of a meromorphic germ at a point. Mathlib has no Laurent expansion
    of a `MeromorphicAt` function (checked). The code makes it cusp-specific.
  - It requires `0 < h` on about 14 lemmas that do not need it (checked for add, mul and analyticity).
  - It is unbundled, where mathlib bundles `qExpansionRingHom`.
- **(c) `HasCoeffsIn` should mirror `Polynomial.lifts`.** With a `Polynomial.lifts`-style subsemiring of a ring hom,
  its 14 closure lemmas become `*_mem`.
- **(d) A few copies of mathlib remain.**
  - One exact duplicate of a public mathlib lemma: `periodic_comp_ofComplex_of_vadd` (checked).
  - One copy of a mathlib-*private* definition: `E₄CubeSubE₆SqForm`, in Δ/QExp lines 174–178.
  - One near-verbatim copy of the inside of a mathlib proof: `ModularGroup.exists_eq_T_zpow_or_neg_of_c_eq_zero`.
- **(e) 66 public declarations have no use anywhere**, counting the PhD copies' users.

---

## Statistics

- **Files and size.** 18 files (17 NumberTheory, 1 RingTheory), 3,803 lines.
- **Declarations.** 370 in total: 328 theorems/lemmas, 37 defs/abbrevs and 5 instances, of which 37 are private.
  There is no `sorry`, no `set_option` and no proof longer than 30 lines; the longest is 29.
- **Build.** The build passes with 30 warnings:
  - 13 deprecated names: `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`, `HahnSeries.embDomain_notin_range`,
    `ENat.coe_ne_top`, `ENat.map_coe`.
  - 15 "imports a module-system file without `module`" warnings. 10 of the 18 files lack the `module` header.
  - 2 `letI` lints.
- **Mirror.** 370 of 370 names are also declared in `XYin/PhD/` (Part 2).
- **Moral duplications.** 35 rows in the pairwise table (Part 4), plus the whole-tree mirror.
- **Generalisation opportunities.** 18 (Part 5).
- **Missing API items.** 33 (Part 6).
- **Junk/removable.** 31 action items (Part 7), covering about 60 declarations.
- **Zero-use public declarations.** 66 (Part 7 §C).
- **Mathlibable assessment.** Not run (Step 9 skipped). Part 8 lists 18 standalone-PR candidates and 3 series for
  triage.

---

## Part 1: Declaration Inventory

The full per-declaration inventory is in six files under `.mathlib-quality/overview/formathlib-nt-rt-2026-11-04/inventory/`:

- [QExpansion-Basic-ChangeRep-CuspReps.md](.mathlib-quality/overview/formathlib-nt-rt-2026-11-04/inventory/QExpansion-Basic-ChangeRep-CuspReps.md) (44 decls)
- [QExpansion-small-Discriminant-Eisenstein.md](.mathlib-quality/overview/formathlib-nt-rt-2026-11-04/inventory/QExpansion-small-Discriminant-Eisenstein.md) (46 decls)
- [LaurentQExpansion-Basic.md](.mathlib-quality/overview/formathlib-nt-rt-2026-11-04/inventory/LaurentQExpansion-Basic.md) (89 decls)
- [LaurentQExpansion-Algebra-Convergence.md](.mathlib-quality/overview/formathlib-nt-rt-2026-11-04/inventory/LaurentQExpansion-Algebra-Convergence.md) (49 decls; the agent also listed one generated declaration)
- [JFunction-Basic-QExpansion-Properties.md](.mathlib-quality/overview/formathlib-nt-rt-2026-11-04/inventory/JFunction-Basic-QExpansion-Properties.md) (76 decls)
- [Lattice-EllipticCurve-HasCoeffsIn.md](.mathlib-quality/overview/formathlib-nt-rt-2026-11-04/inventory/Lattice-EllipticCurve-HasCoeffsIn.md) (66 decls)

Each entry gives Type, What, How, Hypotheses, Uses from project, Used by, Visibility, Lines and Notes. Each file also
has Part B (cross-file usage), Part C (a mathlib overlap table) and Part D (observations).

### Per-file summary

| file | lines | decls | private | defs | key API (used by ≥3 others) | zero-use public |
|---|---:|---:|---:|---:|---|---:|
| QE/Basic | 164 | 19 | 0 | 2 | `strictWidthAt`, `qExpansionAt`, `periodic_slash_strictWidthAt`, `strictWidthAt_pos` | 7 |
| QE/CuspReps | 185 | 13 | 0 | 0 | `exists_eq_T_zpow_or_neg_of_c_eq_zero`, `strictWidthAt_mul_T_zpow`, `strictWidthAt_neg` | 2 |
| QE/ChangeRep | 223 | 12 | 0 | 0 | `qExpansion_slash_T_zpow_coeff`, `exists_qExpansionAt_coeff_eq_of_cuspOrbit_eq` | 1 |
| QE/Algebra | 71 | 3 | 0 | 0 | `qExpansionAt_mul` | 1 |
| QE/ModularForm | 102 | 7 | 0 | 0 | `analyticAt_cuspFunction_slash_zero` | 5 |
| QE/Order | 62 | 3 | 0 | 0 | — | 2 |
| QE/Degenerate | 96 | 2 | 0 | 0 | — (two terminal junk-value results) | 2 |
| Δ/QExp | 208 | 28 | 10 | 6 | `integralE4`, `integralE6`, `E₄_isIntegralPowerSeries`, `discriminant_isIntegralPowerSeries` | 5 |
| E/QExp | 46 | 3 | 0 | 0 | `E₄_q_exp`, `E₆_q_exp`, `bernoulli'_six` | 0 |
| LQE/Basic | 887 | 89 | 4 | 4 | `poleOrder` (44 in-file uses), `laurentqExpansion` (18), `toQExpansion` (15), `poleRemoved` (11), `cuspFunction_comp_eventuallyEq` | 11 |
| LQE/Algebra | 457 | 37 | 9 | 3 | `laurentqExpansion_add/_mul`, `shiftedLaurent`, `toQExpansion_nat_mul` | 4 |
| LQE/Convergence | 193 | 12 | 0 | 0 | `hasSum_laurentqExpansion`, `laurentqExpansion_coeff_unique` | 0 |
| J/Basic | 61 | 5 | 0 | 1 | `j`, `j_mdifferentiable`, `j_periodic` | 0 |
| J/QExp | 372 | 56 | 10 | 6 | `deltaOverQ`, `qOverDelta`, `qj`, `qjCoeffs`, `integralDeltaOverQ` | 9 |
| J/Properties | 119 | 15 | 0 | 0 | `j_eq_zero_iff`, `j_sub_1728_eq` | 4 |
| J/Lattice | 257 | 26 | 4 | 6 | `PeriodPair.smul`, `G_smul`, `periodPair`, `discriminant`, `PeriodPair.j` | 0 |
| J/EllipticCurve | 81 | 10 | 0 | 2 | `weierstrassCurve` | 2 |
| HasCoeffsIn | 219 | 30 | 0 | 7 | `HasCoeffsIn`, `hasCoeffsIn_iff_coeff`, `toIntegralPowerSeries`, `coeTo_of_toIntegralPowerSeries` | 11 |
| **total** | **3,803** | **370** | **37** | **37** | | **66** |

Of the "zero-use" declarations, several are intended end results rather than dead code. Examples are
`laurentqExpansion_coeff_eq_circleIntegral`, `j_eq_qjCoeffs_tsum`, `UpperHalfPlane.ellipticCurve_j` and the two
`qExpansion_eq_C_of_*` lemmas. Part 7 separates the two kinds.

---

## Part 2: Cross-File Dependencies

### Import graph (project-internal)

```
QE/Basic ─┬─> QE/CuspReps ─> QE/ChangeRep ─> QE/Order ─┐
          └─> QE/Algebra ──────────────────────────────┴─> QE/ModularForm
QE/Degenerate                         (mathlib only; no project imports)

HasCoeffsIn ───────────────┬─────────────────────────┐
E/QExp ──┬─> Δ/QExp <──────┘                         │
         │      │                                    │
         │      └──────────────────┐                 │
J/Basic ─┼─> J/Lattice ─> J/EllipticCurve            │
         │                         ▼                 ▼
LQE/Basic ─> LQE/Algebra ─> LQE/Convergence ─> J/QExp ─> J/Properties
(J/Basic also feeds J/QExp)
```

The graph has two components that never meet:

- **The cusp-representative pillar:** `QE/*`.
- **The Laurent/arithmetic pillar:** `LQE/*`, `J/*`, `Δ/QExp`, `E/QExp` and `HasCoeffsIn`.

There is no Laurent expansion at a cusp representative, j is expanded only at ∞, and integrality is never stated at
other cusps. `QE/Degenerate` is standalone.

### Build reachability

`lakefile.toml` declares `lean_lib XYin` with no `globs`, so only modules reachable from `XYin.lean` are built.

- `XYin.lean` imports the PhD originals: `XYin.PhD.NewQExpansion.*`, `XYin.PhD.LaurentQExpansion.*`,
  `XYin.PhD.jFunction.*` and `XYin.PhD.IntegralPowerSeries.*`.
- No file anywhere imports `XYin.ForMathlib.NumberTheory.*` or `XYin.ForMathlib.RingTheory.*`, apart from these 18
  files themselves.
- "The full build passes" therefore says nothing about this folder. Today's targeted build is the only current
  evidence.

### The PhD mirror (cross-tree duplication)

"diff lines" counts the output of `diff -w`; 2 usually means only the import line differs.

| ForMathlib file | PhD original (still built) | lines (FM vs PhD) | diff lines | notes |
|---|---|---|---:|---|
| QE/Basic | `PhD/NewQExpansion/Basic.lean` | 164 / 164 | 0 | identical |
| QE/CuspReps | `PhD/NewQExpansion/CuspRepresentatives.lean` | 185 / 185 | 2 | imports only |
| QE/ChangeRep | `PhD/NewQExpansion/ChangeRepresentative.lean` | 223 / 223 | 2 | imports only |
| QE/Algebra | `PhD/NewQExpansion/Algebra.lean` | 71 / 71 | 2 | imports only |
| QE/ModularForm | `PhD/NewQExpansion/ModularForm.lean` | 102 / 102 | 4 | imports only |
| QE/Order | `PhD/NewQExpansion/Order.lean` | 62 / 62 | 2 | imports only |
| QE/Degenerate | `PhD/jFunction/qexp_junk_values_formathlib.lean` | 96 / 96 | 0 | the PhD file is itself an orphan (nothing imports it) |
| LQE/Basic | `PhD/LaurentQExpansion/LaurentQExpansion.lean` | 887 / 898 | 27 | the port dropped `cuspFunction_apply_of_ne_zero` and `cuspFunction_eventuallyEq_comp` |
| LQE/Algebra | `PhD/LaurentQExpansion/Algebra.lean` | 457 / 457 | 2 | imports only |
| LQE/Convergence | `PhD/LaurentQExpansion/Convergence.lean` | 193 / 193 | 2 | imports only |
| HasCoeffsIn | `PhD/IntegralPowerSeries/IntegralPowerSeries.lean` | 219 / 268 | 83 | generalised from ℤ/ℂ to `R`/`A` in the port |
| Δ/QExp | `PhD/jFunction/Deltaqexpansions.lean` | 208 / 222 | 34 | near-copy |
| E/QExp | `PhD/Modularforms/Eisenstein.lean` lines 34–56 | 46 / — | — | header says "Copied from"; identical lines |
| J/Basic, J/QExp | `PhD/jFunction/jfunction.lean` | 433 / 407 | 107 (J/QExp) | the port dropped `qjCoeffs_one = 744` (that lives in `PhD/jFunction/qexp_coeffs.lean`) |
| J/Properties | `PhD/jFunction/jProperties.lean` | 119 / 119 | 2 | imports only |
| J/Lattice | `PhD/Cox/LatticeJ.lean` | 257 / 604 | subset | the port dropped `j_smul`, `j_congr`, `coe_smulLatticeEquiv_apply`, `coe_smulLatticeEquiv_symm_apply` |
| J/EllipticCurve | `PhD/jFunction/jInvariantLink.lean` | 81 / 81 | 2 | imports only |

Downstream PhD consumers (Cox §11, `qExpansion_tactic`, `ModularFunctions/*`) all bind to the PhD copies.

### Cross-file use inside the scope

Exact counts are in each inventory's Part B. These are the load-bearing cross-file declarations:

- `UpperHalfPlane.laurentqExpansion` has 58 uses across LQE/Algebra, LQE/Convergence and J/QExp.
- `poleOrder` has 30 uses.
- `poleRemoved` has 11 uses, and `toQExpansion` has 8.
- `IsIntegralPowerSeries` / `toIntegralPowerSeries` are used in Δ/QExp and J/QExp.
- `E₄_q_exp`/`E₆_q_exp` are used in Δ/QExp and J/QExp.
- `bernoulli'_six` is used in J/Lattice.
- `j`, `j_mdifferentiable` and `j_periodic` are used in J/QExp, J/Properties, J/Lattice and J/EllipticCurve.
- `periodic_comp_ofComplex_of_vadd` is used 3 times in J/QExp.

---

## Part 3: Mathlib API Audit (most important)

### 3a. Every definition against mathlib

| definition | mathlib status (pinned) | recommended choice |
|---|---|---|
| `Subgroup.strictWidthAt Γ γ` | **New.** Mathlib writes `strictWidthInfty (toConjAct g⁻¹ • Γ)` ad hoc (LFunction.lean:27–35). | Keep, but take `g : GL (Fin 2) ℝ` (G1). State it as the strict width of `translate`'s level and add `strictWidthAt_mem_strictPeriods`. |
| `SlashInvariantForm.qExpansionAt` | **New name, but definitionally `qExpansion (strictWidthAt Γ γ) (SlashInvariantForm.translate f γ)`** (checked) | Keep the def, and add `qExpansionAt_eq_qExpansion_translate : … := rfl` as the main API entry. Then derive add/neg/sub/smul/mul/inj/hasSum/coeff_zero from mathlib's `qExpansion_*`, `ModularForm.qExpansion_*` and `CuspFormClass.qExpansion_coeff_zero` applied to `translate`/`ModularForm.translate`/`CuspForm.translate` (NormTrace.lean:43–74). |
| `HasCoeffsIn R A x` (Prop def), `powerSeriesMapSubalgebra` | Not in mathlib. The analogues are `Polynomial.lifts f : Subsemiring S[X]` with `lifts_iff_coeff_lifts` (Algebra/Polynomial/Lifts.lean:61, 73), and `MvPolynomial.coeffsIn` (checked). | Replace with `PowerSeries.lifts (f : R →+* S) : Subsemiring S⟦X⟧ := (PowerSeries.map f).rangeS` plus `PowerSeries.lifts_iff_coeff_lifts`. Use membership `x ∈ lifts f`, not a Prop wrapper, so `add_mem`/`mul_mem`/`pow_mem`/`sum_mem`/`prod_mem`/`neg_mem` apply directly. |
| `toHasCoeffsInPowerSeries` (`Classical.choose`) | — | Either use `PowerSeries.mk fun n ↦ (h n).choose`, or for injective `algebraMap` use `(AlgEquiv.ofInjective (PowerSeries.mapAlgHom _) (PowerSeries.map_injective _ inj)).symm`, which brings `map_add`/`map_mul` for free. The latter is the only case used. |
| `IntegralPowerSeries.IntegralPowerSeriesSubring`, `IsIntegralPowerSeries`, `toIntegralPowerSeries` | ℤ/ℂ re-skins of the above | Drop the namespace, or keep one `abbrev`. `IntegralPowerSeriesSubring` is a dead `Subalgebra.toSubring` wrapper. |
| `modularFormQExpansionSubmodule` + scoped `modularFormModuleofIsScalarTower` | The instance body is exactly mathlib's `FunLike.module` (Algebra/Module/FunLike.lean:76; checked). | Delete (dead). If wanted later, use `Submodule.comap` of an `R`-linear q-expansion map, with `FunLike.module` locally. |
| `integralE4`, `integralE6`, `integralDelta` (`Classical.choose` lifts), private `e4Bar`, `e6Bar` | ℤ-valued q-expansions are absent from mathlib | Define explicitly, e.g. `integralE4 := PowerSeries.mk fun n ↦ if n = 0 then 1 else 240 * σ 3 n`, and prove `map (algebraMap ℤ ℂ) integralE4 = qExpansion 1 E₄`. Coefficients become `rfl`/`simp` and τ(n) becomes computable. |
| `ramanujanTau` | Absent | Keep, as `ModularForm.ramanujanTau`. |
| `j` (root namespace) | **Absent.** Mathlib's only `j` is `WeierstrassCurve.j` (checked: `grep` for `jFunction`/`kleinJ`/`jInvariant` is empty). | Namespace it, e.g. `ModularForm.jFunction` with scoped notation `j`; the root `j` already forces `_root_.j` in J/EllipticCurve:78. Bundle it as `SlashInvariantForm 𝒮ℒ 0` (agent-compiled), so `j_periodic` and `j_modularGroup_smul` become mathlib lemmas. |
| `deltaOverQ`, `qOverDelta` | Mathlib writes the η-product via `eta_q` and `𝕢` (`discriminant_eq_q_prod`) | Write them with `𝕢 1 τ`/`eta_q`, not raw `cexp (2πiτ)`. `qExpansion 1 deltaOverQ = PowerSeries.divXPowOrder (qExpansion 1 Δ)` follows from `discriminant_qExpansion_order` (agent-compiled). |
| `deltaShiftedQSeries` | — | Dead; delete. |
| `qj`, `qjCoeffs` | — | `qj` is the project's `poleRemoved 1 j` (proved equal at J/QExp:303). Delete `qj` and use `poleRemoved`/`toQExpansion`, so its periodic/mdiff/bounded/analytic API comes from LQE. Keep `qjCoeffs`, renamed, e.g. `jCoeff`. |
| `PeriodPair.smul` + `SMul ℂˣ PeriodPair` | Absent (`PeriodPair` has no action and no `@[ext]`) | Upgrade to `MulAction ℂˣ PeriodPair` and add `PeriodPair.ext`. |
| `PeriodPair.Homothetic` | Equivalent to the lattices lying in one ℂˣ-orbit | Define it as `∃ a : ℂˣ, M.lattice = (a : ℂ) • L.lattice`, or via `MulAction.orbitRel`, and give it `Equivalence` API. |
| `PeriodPair.discriminant`, `PeriodPair.j` | Absent | Keep; these are new mathlib content. |
| `smulLatticeEquiv` | Wrapper of `LinearEquiv.ofSubmodules` | Keep only with its `coe_*_apply` simp lemmas, which were dropped in the port. Otherwise inline. |
| `UpperHalfPlane.periodPair` | Absent | Keep. Add `@[simps]` or `periodPair_ω₁/ω₂`, and generalise to `τ ∈ ℂ \ ℝ` (G16). |
| `PeriodPair.weierstrassCurve`, `UpperHalfPlane.ellipticCurve` | Mathlib has `WeierstrassCurve.ofJ*` but no curve attached to a lattice | Keep. Add `@[simps]` so `a₄ = -g₂/4` and `a₆ = -g₃/4` are simp lemmas, and make `ellipticCurve` an `abbrev`. |
| `UpperHalfPlane.poleOrder` (ℕ) | Mathlib has `meromorphicOrderAt` (`WithTop ℤ`). **Master** (not the pin) has `Mathlib.NumberTheory.ModularForms.OrderAtInfty` with `orderAtInfty_eq_qExpansion_order` (reported by agent via loogle, which indexes master; not checked). | Define it directly as `(-(meromorphicOrderAt (cuspFunction h f) 0).untop₀).toNat`, which makes `poleOrder_eq_toNat_neg_meromorphicOrderAt` `rfl`. **Rebase onto master before any PR**, and express it through upstream's order at ∞. |
| `poleRemoved`, `toQExpansion`, `laurentqExpansion` | Absent. Mathlib has no Laurent expansion of a meromorphic function (checked: no `LaurentSeries` in `Mathlib/Analysis`). | See G3: the generic object is the Laurent series of a meromorphic germ. Then `laurentqExpansion h f := laurentSeries (cuspFunction h f) 0`. Rename `laurentqExpansion` to `laurentQExpansion` (house capitalisation, as in `qExpansion`). |
| `shiftedLaurent` | Proof device; `shiftedLaurent h (poleOrder h f) f` is `rfl`-equal to `laurentqExpansion h f` | Either define `laurentqExpansion` through it, or make it private. |
| `natMulOrderEmbedding` | `OrderEmbedding.ofStrictMono` wrapper | Use `HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (m : ℤ)) …` (HahnSeries/Multiplication.lean:881), or add `@[simps]` and `mem_range_natMulOrderEmbedding`. |
| private `analyticTaylor` | `rfl`-equal to `qExpansion` on cusp functions | Fine as a private device. Note that mathlib's QExpansion.lean:206 has a TODO for a PowerSeries ↔ FormalMultilinearSeries API. |

### 3b. API-choice improvements

1. **Build `QE/*` on `translate` + mathlib `qExpansion`** (3a row 2).
   - QE/ModularForm's five lemmas become one-liners: `hasSum_qExpansionAt`, `qExpansionAt_inj`, `qExpansionAt_mul`,
     `qExpansionAt_coeff_zero` and `CuspForm.qExpansionAt_coeff_zero`.
   - So do QE/Basic's `qExpansionAt_add/neg/sub/smul/zero/coeff_zero/eq_zero_iff`.
   - `ModularFormClass.analyticAt_cuspFunction_slash_zero` becomes mathlib's
     `ModularFormClass.analyticAt_cuspFunction_zero` applied to `ModularForm.translate f γ`.
2. **Bundle `laurentqExpansion` as a `RingHom`.** It would be defined on the subring of functions whose cusp function
   is meromorphic at 0; LQE/Basic proves closure under all ring operations.
   - The lemmas `_zero/_one/_neg/_sub/_pow/_smul/_finset_sum/_finset_prod/_polynomial_eval` then come from
     `map_*` and `Polynomial.hom_eval₂`.
   - The private `map_finset_prod_of_mul`/`map_finset_sum_of_add` disappear.
   - This mirrors mathlib's `ModularForm.qExpansionRingHom` (QExpansion.lean:683).
3. **Use the Pi form (`f + g`, `f * g`, `-f`) as mathlib's `qExpansion_add/mul/neg` do.**
   - LQE's `_add/_mul/_neg/_sub/_pow/_const_mul` and the `meromorphicAt_cuspFunction_*` family use lambdas, while
     `_smul/_finset_*` use the Pi form. The mismatch forces `rfl`/`hfun` rewrites (LQE/Algebra L69, L108, L128–145).
   - Use `@[to_fun]` where both forms are wanted.
4. **Use `MeromorphicAt` transport, not 11 hand-written closure lemmas.** A single
   `meromorphicAt_cuspFunction_iff_of_eventuallyEq` (or `MeromorphicAt.cuspFunction_comp₂`) plus mathlib's
   `MeromorphicAt.add/mul/…` gives each closure lemma as a direct application. The current proofs repeat
   `X.congr (cuspFunction_comp₂_eventuallyEq …).symm` nine times.
5. **Get the Δ q-expansion identity from public mathlib.** Apply `ModularForm.qExpansionAlgHom 1 …` to the public
   `discriminant_eq_E₄_cube_sub_E₆_sq_graded` (GradedRing.lean:80). Do not copy the private `E₄CubeSubE₆SqForm`
   (Δ/QExp:174–178).
6. **Use `𝕢 1 τ` and `eta_q`, not `cexp (2 * π * I * τ)`, in J/QExp.** The raw form causes the private
   `mdifferentiable_cexp_aux`, `cexp_vadd_one_aux`, a non-`rfl` `qj_apply` and five `simp [Periodic.qParam]` steps.
7. **Adopt the module system.** 10 of 18 files lack `module` + `public import`: all of LQE/*, all of J/*, Δ/QExp
   and HasCoeffsIn. Every pinned mathlib file uses it, and it causes 15 of the 30 build warnings.
8. **Use namespaces.** LQE/*, J/*, Δ/QExp, E/QExp and most of HasCoeffsIn sit in the root namespace.
   - Where the def is `UpperHalfPlane.laurentqExpansion`, the coefficient lemmas form a separate root namespace
     `laurentqExpansion.*`, so dot notation does not work.
   - Mathlib puts the analogues in `UpperHalfPlane` and `ModularForm`, and `PowerSeries` for `HasCoeffsIn`.

### 3c. Hand-rolled patterns to replace

| pattern | where | replacement |
|---|---|---|
| Periodicity of `f ∘ ofComplex` from `f (h +ᵥ τ) = f τ` | LQE/Basic:205 `periodic_comp_ofComplex_of_vadd` | **Exact duplicate** of `UpperHalfPlane.periodic_comp_ofComplex` (Analysis/Complex/UpperHalfPlane/Topology.lean:184), with the same statement and essentially the same proof (checked). Delete it and repoint its 3 uses in J/QExp. |
| Periodicity proved three ways | J/Basic:54 (`Periodic.div`), J/QExp `*_vadd_one_aux` + the duplicate above, LQE/Convergence:42–54 (manual `Im` split) | Bundled `j : SlashInvariantForm 𝒮ℒ 0` + `SlashInvariantFormClass.periodic_comp_ofComplex` (agent-checked), plus a `qParam` translation lemma. |
| "Δ/q → 1 at i∞" | J/QExp ll. 100–102, 126–128 (verbatim), 147–149, 178–179 | Add `deltaOverQ_tendsto_atImInfty` once. |
| `simpa only [IsBoundedAtImInfty, BoundedAtFilter, Pi.one_def] using (·).isBigO_one ℝ` | J/QExp ll. 100, 126, 186, 251; LQE/Convergence:70 | Missing `Filter.Tendsto.isBoundedAtImInfty`. Mathlib lacks it too and uses the same trick in RamanujanFormula.lean, so it is a mathlib PR. |
| `filter_upwards [self_mem_nhdsWithin] …; simp only [cuspFunction, Periodic.cuspFunction_eq_of_nonzero …]` | LQE/Basic ll. 70, 78, 90, 501, 590 | `UpperHalfPlane.cuspFunction_apply_of_ne_zero`. The PhD copy has it and the port dropped it, and mathlib inlines the same step in `cuspFunction_mul`, `qExpansion_one` and Discriminant.lean:207. |
| `mapGL ℝ (T ^ n) = upperRightHom n` via `Units.ext` + `fin_cases` | QE/CuspReps:109–114; holomorphic-and-bounded-after-`T^m` blocks at QE/ChangeRep:83–90 and 149–158 | Add `ModularGroup.mapGL_T_zpow` (mathlib gap). |
| `change … mapGL ℝ …` coercion unfolding | 9 sites in QE/Basic, QE/CuspReps, QE/ChangeRep | State the API with `mapGL ℝ γ`, or add a coercion simp lemma. |
| "SL(2,ℤ)-conjugate of an arithmetic group is arithmetic" cast sequence | QE/Basic:63–67; also mathlib Bounds.lean:205–208 and LFunction.lean:30–35 | Missing instance `IsArithmetic (toConjAct (mapGL ℝ g) • 𝒢)` for `g : SL(2, ℤ)` (mathlib gap). |
| Local `FunLike (ℍ → ℂ) ℍ ℂ` instance | QE/ChangeRep:91, LQE/Convergence:165 | Mathlib's `qExpansion_coeff_unique` takes `f : F` with `[FunLike F ℍ ℂ]`. Restate the mathlib lemma for `f : ℍ → ℂ` upstream. |
| Local `SlashInvariantFormClass (ModularForm 𝒮ℒ k) Γ(1) k` instance | J/Properties ll. 41–43, 58–59 | `SlashInvariantForm.slash_action_eqn'' (Γ := 𝒮ℒ) f ⟨S, rfl⟩` (agent-compiled). `S • I = I` is `ModularGroup.stabilizer_I.mpr (by simp)` (agent-compiled). |
| Constant terms of Δ/q and q/Δ via limits | J/QExp ll. 146–150, 264–266 | Algebraic one-liners: `(deltaOverQ_qExpansion_coeff 0).trans discriminant_qExpansion_coeff_one`, and coefficient 0 of the inverse identity (agent-compiled). |
| `coeff_mul_dvd_aux` | Δ/QExp:113 | Special case of `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'` (CoeffMulMem.lean:52). Simpler still: write `e4Bar = C 240 * g`. |
| `mem_smul_lattice`, `map_lattice_mulLeftLinearEquiv` coordinate bash | J/Lattice:59–76 | `(a • L).lattice = (a : ℂ) • L.lattice` via `Submodule.smul_span`; then `Submodule.mem_smul_pointwise_iff_exists`. |
| `LinearIndependent.pair_iff` arguments | J/Lattice:34, 130, 206 | `LinearIndependent.pair_iff'`. |
| `show E₄ τ = (1/2) • eisensteinSeriesSIF … from rfl` | J/Lattice:171, 182 | Missing mathlib `ModularForm.E_apply`. |
| Slash injectivity via `slash_mul`/`mul_inv_cancel`/`slash_one` | QE/Algebra:65–67 | `SlashAction.slash_injective` (mathlib gap; the same trick appears inside `SlashAction.slash_eq_zero_iff`). |
| `z ≠ 0` from `z ∈ sphere 0 R` by `rintro rfl; simp; linarith` | LQE/Basic:823–826 | `ne_zero_of_mem_sphere`. |
| `exists_eq_T_zpow_or_neg_of_c_eq_zero` | QE/CuspReps:25–36 | A near-verbatim copy of the inside of mathlib's `ModularGroup.exists_eq_T_zpow_of_c_eq_zero` (Modular.lean:329–343), which exports only the weaker statement about the action. Upstream the matrix lemma and derive mathlib's from it. |
| Root-of-unity proof of `isOfFinOrder_qParam_natCast_int` | QE/ChangeRep:31–38 | `Complex.isPrimitiveRoot_exp_rat` + `IsPrimitiveRoot.isOfFinOrder`. Moot if the lemma is deleted (Part 7). |

---

## Part 4: Moral Duplications

Pairwise comparison table. The pairs come from the six inventories' Part D sections, plus a cross-pillar pass.
"Same proof" means the same mathematical argument.

| # | Decl A | Decl B | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|---|
| 1 | whole tree `XYin/ForMathlib/{NumberTheory,RingTheory}` | `XYin/PhD/{NewQExpansion,LaurentQExpansion,jFunction,IntegralPowerSeries,Cox/LatticeJ,…}` | yes (370/370 names) | yes (11 files identical apart from imports) | **UNIFY: one canonical tree (P0)** |
| 2 | `periodic_comp_ofComplex_of_vadd` (LQE/Basic:205) | mathlib `UpperHalfPlane.periodic_comp_ofComplex` | yes, exactly | yes | **DELETE A** |
| 3 | `discriminant_qExpansion_eq_smul_eisenstein_difference` setup (Δ/QExp:174–178) | mathlib private `E₄CubeSubE₆SqForm` (GradedRing.lean:33–40) | yes | yes (copied) | **REPLACE** via `qExpansionAlgHom` on the public graded identity |
| 4 | `ModularGroup.exists_eq_T_zpow_or_neg_of_c_eq_zero` | inside of mathlib `ModularGroup.exists_eq_T_zpow_of_c_eq_zero` | stronger (matrix level) | yes (copied) | **UPSTREAM A, derive mathlib's** |
| 5 | `qExpansion_coeff_eq_circleIntegral_of_differentiableOn` (LQE/Basic:794) | mathlib `qExpansion_coeff_eq_circleIntegral` | A strictly more general | yes (body copied) | **UPSTREAM A, mathlib's becomes a corollary** |
| 6 | `meromorphicAt_cuspFunction_const_mul` (LQE/Basic:140) | `meromorphicAt_cuspFunction_smul` (:146) | yes (defeq) | yes | **DELETE B** (unused) |
| 7 | `laurentqExpansion_const_mul` (LQE/Algebra:205) | `laurentqExpansion_smul` (:212) | yes (defeq) | yes | **KEEP ONE** (Pi-form `smul`) |
| 8 | `laurentqExpansion.order_eq_neg_poleOrder` (LQE/Basic:757) | `laurentqExpansion.poleOrder_to_order` (:767) | yes (rearranged) | yes | **DELETE B** (unused) |
| 9 | `laurentqExpansion.coeff_eq_zero_of_lt` / `coeff_neg_poleOrder_add` / `coeff_of_geq` (:650/655/660) | primed versions `…'` with `hM : poleOrder h f = M` (:669/675/682) | yes up to `subst` | yes | **DELETE primed** |
| 10 | `laurentqExpansion.coeff_of_qExpansion` (:690) | `coeff_eq_zero_of_lt` + `coeff_of_geq` | yes (as one `if`) | yes | keep the two cases; derive or delete the `if` form |
| 11 | `cuspFunction_comp_eventuallyEq` (:68) | `cuspFunction_comp₂_eventuallyEq` (:75) | A special case of B | yes | derive A from B (or delete A) |
| 12 | `cuspFunction_qpow_mul_eq`/`_eventuallyEq` (:497/506) | `cuspFunction_poleRemoved_eq`/`_eventuallyEq` (:595/605) | B = A at `n = poleOrder` | yes | derive B from A |
| 13 | `meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` (:719) | `poleOrder_eq_iff` (:391), `.mp` | yes (different coercion normal form) | yes | derive A from B; pick one normal form of `-↑N` |
| 14 | `shiftedLaurent h (poleOrder h f) f` (LQE/Algebra:83) | `laurentqExpansion h f` (LQE/Basic:472) | `rfl` | — | define one through the other |
| 15 | `hasSum_laurentqExpansion_natCast_sub_of_norm_lt` (LQE/Convergence:86) | `hasSum_laurentqExpansion_of_norm_lt` (:104) | yes (ℕ-shift vs ℤ index) | yes | keep the ℤ form; the ℕ form follows by `hasSum_int_iff_natCast_sub_of_eq_zero` |
| 16 | `hasSum_laurentqExpansion_natCast_sub` (:116) | `hasSum_laurentqExpansion` (:126) | yes (same pair on ℍ) | yes | as row 15 |
| 17 | `tendsto_atImInfty_of_analyticAt_cuspFunction` (LQE/Convergence:57) | inline in mathlib `cuspFunction_apply_zero` (QExpansion.lean:120–127), `CuspFormSubmodule.lean:111` | yes | yes | **UPSTREAM** (with `ContinuousAt`) |
| 18 | `cuspFunction_apply_zero_of_tendsto` (J/QExp:45) | `cuspFunction_apply_zero_eq` (LQE/Basic:560); mathlib `IsZeroAtImInfty.cuspFunction_apply_zero` (a = 0) | related (limit vs punctured-nbhd equality) | similar | put one at the `Periodic.cuspFunction` level; generalise mathlib's `a = 0` lemma |
| 19 | `qj` and its API: `qj_periodic`, `qj_mdifferentiable`, `qj_isBoundedAtImInfty`, `qj_cuspFunction_analyticAt` (J/QExp) | `poleRemoved 1 j` + `periodic_comp_ofComplex_qpow_mul`, `isBoundedAtImInfty_poleRemoved`, `analyticAt_cuspFunction_poleRemoved` (LQE) | yes (`j_poleRemoved`, J/QExp:303) | different routes | **DELETE `qj`**, use `poleRemoved` |
| 20 | `qj_qExpansion_coeff_zero` (J/QExp:261) | `qjCoeffs_zero` (:274), `qj_cuspFunction_zero` (:282) | yes (ℂ, ℤ and value forms) | yes | keep `qjCoeffs_zero` (simp) + the value form (load-bearing simp) |
| 21 | `j_laurentQExpansion_coeff_of_neg_one_le` (:320) | `j_laurentQExpansion_coeff_sub_one` (:326), `j_laurentQExpansion_coeff` (:333), `_isIntegral` (:341) | yes (reindexings and `if`) | yes | keep `j_laurentQExpansion_coeff`; derive the rest or delete |
| 22 | `hasSum_j_laurentQExpansion` (:346) | `hasSum_j_qjCoeffs` (:352), `j_eq_qjCoeffs_tsum` (:365) | yes (ℤ, ℕ and tsum forms) | yes | keep one HasSum and the tsum corollary |
| 23 | `j_tendsto_cobounded_atImInfty` (J/Properties:112) | `tendsto_norm_j_atImInfty` (:118) | equivalent via `tendsto_norm_atTop_iff_cobounded` | yes | keep A |
| 24 | `SlashInvariantForm.qExpansionAt_inj` (QE/Algebra:51) | `ModularForm.qExpansionAt_inj` (QE/ModularForm:60) | B = A + `toSlashInvariantForm` injectivity | yes | derive B from mathlib via `translate`, or delete (unused) |
| 25 | `qExpansionAt_mul` (QE/Algebra:29) | `qExpansionAt_mul_of_mdifferentiable` (:37), `ModularForm.qExpansionAt_mul` (QE/ModularForm:75) | three versions | glue | keep A + one `ModularForm` corollary; delete the middle (unused) |
| 26 | `qExpansionAt_mul_T_zpow_coeff` (QE/ChangeRep:111) | `qExpansionAt_mul_T_zpow` (:122) | yes (coefficient vs `rescale` form) | yes | keep the `rescale` form; derive the coefficients by simp |
| 27 | `strictWidthAt_eq_of_smul_infty_eq` (QE/CuspReps:135) | `strictWidthAt_eq_of_cuspOrbit_eq` (:142) | point vs orbit version | B re-does A's case split | derive B from A + `strictWidthAt_mul_left` |
| 28 | `exists_intCast_strictWidthAt` (:154) | `exists_natCast_` (:169), `exists_pos_natCast_` (:178) | one fact three times | chain | merge into one (or delete with the unused `IsOfFinOrder` conjunct) |
| 29 | `ModularForm.SL_slash_T_zpow`, `SL_slash_neg_matrix` (QE/ChangeRep:45, 52) | `slash_T_zpow`, `slash_neg_T_zpow` (`PhD/ModularFunctions/CuspMeromorphy.lean:287, 299`) | yes | yes | keep one (GL-general, G10) |
| 30 | `periodic_slash_strictWidthAt` + `strictWidthAt_pos` (QE/Basic) | `SlashInvariantForm.exists_pos_period_at_cusp` (`PhD/ModularFunctions/CuspPeriod.lean:50`) | B = ∃-form of A | similar | keep A; derive B in PhD |
| 31 | `eisenstein_difference_coeff_dvd_aux` (Δ/QExp:131, private) | `eisenstein_difference_coeff_modEq_zero` (:167) | yes (`∣` vs `Int.ModEq`) | yes | state `IsIntegralPowerSeriesmod` with `∣`; delete B |
| 32 | `E₄_q_exp` (E/QExp:25) | private `E₄_qExpansion_coeff` (Δ/QExp:35), `integralE4_coeff` (:58), `_coeff_zero` (:68), `_coeff_of_pos` (:76), mathlib `E_qExpansion_coeff` | one formula five times (likewise E₆) | yes | state `E₄_q_exp` pointwise; delete the private pair and the unused `_zero/_of_pos` |
| 33 | `periodPair_g₂_eq_E₄` (J/Lattice:166) | `periodPair_g₃_eq_E₆` (:177) | parallel (4 ↔ 6) | identical script | one public `periodPair_G_eq (hk : 3 ≤ k) : G k = 2 ζ(k) E_k(τ)` |
| 34 | `g₂_congr`/`g₃_congr`, `g₂_smul`/`g₃_smul` (J/Lattice:95–118) | each other | parallel | identical | `G_congr` and `G_smul` already cover them; make the g-lemmas one-liners |
| 35 | `hasCoeffsIn_algebraMap` (:83) / `coeTo_of_toIntegralPowerSeries` (:149) | `hasCoeffsIn_C_algebraMap` (:86) / `mapAlgHom_ofId_toIntegralPowerSeries` (:154) | yes (via `PowerSeries.algebraMap_apply` / defeq) | same term | **DELETE B** (both unused) |

**Cross-pillar observation.** The cusp-representative pillar (`QE`) and the Laurent pillar (`LQE`) are two
q-expansion theories that never meet. `qExpansionAt` is the power-series expansion of `f ∣[k] γ` at width
`strictWidthAt Γ γ`; `laurentqExpansion` is the Laurent expansion of any `ℍ → ℂ` at a given period. The natural common
generalisation, `laurentqExpansion (strictWidthAt Γ γ) (f ∣[k] γ)`, is not defined. As a result there is no order or
pole at a non-∞ cusp, and the cusp-orbit invariance results of QE/ChangeRep are not available for meromorphic
functions.

---

## Part 5: Generalisation Opportunities

The literature references are standard textbooks, cited from memory at chapter or section level. No web literature
search was run beyond three checks that mathlib master has no j-function, cusp-representative q-expansions or Laurent
series of meromorphic germs; those checks found nothing, which is weak evidence.

| # | declaration(s) | current | generalisation | evidence | difficulty |
|---|---|---|---|---|---|
| G1 | `strictWidthAt`, `qExpansionAt`, `strictWidthAt_one/nonneg/mul_left`, `periodic_slash_strictWidthAt` | `γ : SL(2, ℤ)` | `g : GL (Fin 2) ℝ`, matching mathlib's `translate`. Positivity then needs `IsCusp (g • ∞) Γ` or rational `g`. | defs and these lemmas go through verbatim (agent-checked) | low |
| G2 | `laurentqExpansion_add/_mul/_const_mul/_smul/_neg/_sub/_pow/_finset_sum/_finset_prod/_polynomial_eval`; `analyticAt_cuspFunction_qpow_mul/_qParam_pow/_qpow_of_poleOrder_le`; `periodic_comp_ofComplex_qpow_mul` | `hh : 0 < h` | drop it: for `h ≤ 0` every cusp function is analytic (`analyticAt_cuspFunction_of_not_pos`), and mathlib's `qExpansion_add/mul` have no `0 < h` | add, mul and analyticity checked in Lean (agent); the rest not checked | low |
| G3 | `poleOrder`, `poleRemoved`, `toQExpansion`, `laurentqExpansion`, Cauchy formula | cusp functions of `f : ℍ → ℂ` only | **the Laurent series of a meromorphic germ**: `MeromorphicAt.laurentSeries (F : 𝕜 → 𝕜) (z₀)`, with order = `meromorphicOrderAt` and leading coefficient = `meromorphicTrailingCoeffAt`; the cusp version is the specialisation at `cuspFunction h f`, `z₀ = 0`. The Cauchy-integral formula needs `𝕜 = ℂ`. | standard (Ahlfors, *Complex Analysis*, Ch. 5, Laurent series); mathlib has none (checked) | high |
| G4 | `meromorphicAt_of_comp_pow` (+ private aux) | `g : ℂ → ℂ`, one direction | `g : ℂ → E` with `[NormedSpace ℂ E] [CompleteSpace E]`, stated as `meromorphicAt_comp_pow_iff` (← is `comp_analyticAt`) | ingredients are E-valued in mathlib (agent; not compiled) | medium |
| G5 | `MeromorphicAt.polynomial_eval` | `g : 𝕜 → 𝕜`, `P : 𝕜[X]` | the `aeval` form over `[NormedAlgebra 𝕜 𝕜']`, mirroring `AnalyticAt.aeval_polynomial`; add `@[fun_prop]` | `MeromorphicAt.mul/pow` hold in that generality (not compiled) | low |
| G6 | `hasFPowerSeriesAt_expand_analyticTaylor`, `analyticTaylor_comp_pow` (private) | ℂ | any complete char-0 nontrivially normed field via `AnalyticAt.hasFPowerSeriesAt`; `hF` follows from `hG` and `hEq` | not checked | medium |
| G7 | `HasCoeffsIn`, `hasCoeffsIn_iff_coeff`, the lift and its uniqueness | `algebraMap R A`; uniqueness stated only for ℤ → ℂ | any ring hom `f : R →+* S` (`PowerSeries.lifts f`), with uniqueness for injective `f` | mirrors `Polynomial.lifts` (checked to exist) | medium |
| G8 | `IsIntegralPowerSeriesmod` | ℤ/ℂ, `hc : c ≠ 0`, `Int.ModEq`, about the *chosen* lift | `HasCoeffsIn R K` for a field `K` (or `algebraMap c` a unit), `c ∣ coeff n g` for **any** `g` with `map g = f`; drop `hc` | `c = 0` forces `f = 0` (agent; not compiled) | low |
| G9 | `coeff_mul_dvd_aux`, `coeff_pow_dvd_aux` (private) | ℤ | any commutative semiring, or delete via `CoeffMulMem` | the proof uses only `mul_dvd_mul`, `Finset.dvd_sum` | low |
| G10 | `SL_slash_neg_matrix`; `strictPeriods_conj_upperRightHom`; `qExpansion_slash_T_zpow_coeff` | `SL(2,ℤ)`; `GL (Fin 2) ℝ`; integer shifts and weight `k` | `g : GL (Fin 2) ℝ`; `GL (Fin 2) R` for any `[Ring R]`; any real translation `x` with factor `qParam h x ^ n` | the first two checked by `lean_run_code`; the third not checked | low |
| G11 | `exists_eq_mul_T_zpow_of_cuspOrbit_eq`, `strictWidthAt_eq_of_cuspOrbit_eq`, the `IntegralSubgroup` sections of QE/ChangeRep and QE/Order | `[Γ.FiniteIndex]` plus a hypothesis on `cosetToCuspOrbit … ⟦γ⁻¹⟧` | hypothesis `∃ δ ∈ Γ, δ • (γ • ∞) = γ' • ∞`; `FiniteIndex` is needed only to typecheck `cosetToCuspOrbit` | agent reading; not compiled | medium |
| G12 | `E₆_apply_I`, `E₄_apply_rho` | E₆ and E₄ | any `ModularFormClass F 𝒮ℒ k` vanishes at `i` if `k ≡ 2 (mod 4)` and at `ρ` if `3 ∤ k` | Serre, *A Course in Arithmetic*, Ch. VII §3; the proofs use only `f(i) = iᵏ f(i)` and `(ρ+1)ᵏ ≠ 1` | low–medium |
| G13 | `j_slash_invariant` | `E₄³/Δ` | the quotient of any two level-1 forms of equal weight (`div_slash_SL2`), with no nonvanishing needed | agent reading | low |
| G14 | `j_analyticAt`; `j_cuspFunction_tendsto_cobounded`, `j_tendsto_cobounded_atImInfty` | `j` | generic `MDifferentiable.analyticAt_comp_ofComplex`; generic "periodic with `poleOrder ≠ 0` ⇒ cobounded at i∞" in LQE | they use only `MDiff j` and `poleOrder 1 j ≠ 0` | low |
| G15 | `tendsto_atImInfty_of_analyticAt_cuspFunction`; `cuspFunction_apply_zero_of_tendsto` | `AnalyticAt`; `ℍ → ℂ` | `ContinuousAt` (agent-checked); state it for `Function.Periodic.cuspFunction`, generalising mathlib's `Periodic.cuspFunction_zero_of_zero_at_inf` (a = 0) | — | low |
| G16 | `UpperHalfPlane.periodPair` | `τ : ℍ` | `τ ∈ ℂ \ ℝ` (only `Im τ ≠ 0` is used); simplifies the sign split in `exists_homothetic_periodPair` | Cox, *Primes of the Form x² + ny²*, §10; Silverman, *AEC*, Ch. VI | low |
| G17 | `HahnSeries.ofPowerSeries_expand` | `ℤ`-indexed | `ofPowerSeries Γ R` for a strict ordered semiring `Γ` | not checked | low |
| G18 | redundant hypotheses | various | `hmero` whenever `h0 : poleOrder h f ≠ 0` (7 lemmas, LQE/Basic:726–783), via `meromorphicAt_of_meromorphicOrderAt_ne_zero` (checked to exist, Meromorphic/Order.lean:60); `hmero`, `hm` in `poleOrder_nat_mul`, `meromorphicOrderAt_cuspFunction_nat_mul`; `hh`, `hfhol`, `hfbdd` → `AnalyticAt` in `qExpansionAt_neg_matrix` (agent-checked); `hfmero` in `laurentqExpansion_coeff_unique`/`_eq_of_hasSum` (not checked); `0 < N` → `N ≠ 0` in `isOfFinOrder_qParam_natCast_int` | mixed | low |

---

## Part 6: API Improvements

### Missing lemmas (each would simplify several proofs or remove a hack)

1. `SlashInvariantForm.qExpansionAt_eq_qExpansion_translate` (`rfl`). This is the entry point for rebuilding QE/*
   on mathlib (3b.1).
2. `UpperHalfPlane.cuspFunction_apply_of_ne_zero` (5 sites in LQE/Basic). It exists in the PhD copy, and mathlib
   would use it too.
3. `Filter.Tendsto.isBoundedAtImInfty` (5 sites; missing from mathlib).
4. `deltaOverQ_tendsto_atImInfty` and `deltaOverQ_isBoundedAtImInfty` (4 inline derivations).
5. `ModularGroup.mapGL_T_zpow : mapGL ℝ (T ^ n) = upperRightHom n`, plus `mapGL` and negation (QE/CuspReps,
   QE/ChangeRep).
6. `ConjAct.toConjAct (-g) • H = ConjAct.toConjAct g • H` (QE/CuspReps:128–132).
7. `SlashInvariantForm.analyticAt_cuspFunction_slash`. QE/ChangeRep:139 and QE/Algebra:46 both build it; only a
   `ModularFormClass` version exists.
8. `meromorphicAt_cuspFunction_of_poleOrder_ne_zero`, which removes `hmero` from 7 lemmas (G18).
9. `mem_range_natMulOrderEmbedding : k ∈ range … ↔ (m : ℤ) ∣ k`, plus an `embDomain` coefficient simp lemma
   (LQE/Algebra:410, 418, 445, 457 and `PhD/Cox/CoxMatrices/LaurentExpansion.lean:150`).
10. `ModularForm.E_apply : E hk z = (1/2) * eisensteinSeries 0 k z` (J/Lattice:171, 182; missing from mathlib).
11. `PowerSeries.order_eq_of_coeff_eq_zero_iff` (QE/Order:55–58).
12. The generic pole lemmas that QE/Degenerate inlines (ll. 74–93): if `meromorphicOrderAt f x < 0`, then
    `meromorphicOrderAt (iteratedDeriv n f) x = order − n` and `iteratedDeriv (n+1) f x = 0`. The PhD precursor had
    them as standalone lemmas.
13. `HasCoeffsIn.of_mul_eq_one`: integral series are closed under integral inverses (J/QExp:204 proves the instance
    `q/Δ`).
14. `SlashAction.slash_injective` and `ModularForm.toSlashInvariantForm_injective` (QE/Algebra:65–67,
    QE/ModularForm:67–72).
15. `PeriodPair.G_congr`, `discriminant_congr`, `@[simps]` on `periodPair`/`weierstrassCurve`. Three
    `rw [X_of_isShortNF]; change …; ring` blocks in J/EllipticCurve disappear.
16. `meromorphicAt_cuspFunction_iff_of_eventuallyEq`, a generic transport that replaces nine `X.congr …` steps.

### Missing bundling and instances

17. `laurentqExpansion` as a `RingHom` on cusp-meromorphic functions (3b.2).
18. `qExpansionAt` as `AddMonoidHom`/`LinearMap`/`RingHom`, analogous to mathlib's
    `qExpansionAddHom`/`qExpansionRingHom`/`qExpansionAlgHom` at ∞.
19. `j` as `SlashInvariantForm 𝒮ℒ 0` (agent-compiled).
20. `MulAction ℂˣ PeriodPair`, `PeriodPair.ext`, and `Homothetic` as an equivalence relation.
21. A named `ModularForm 𝒮ℒ 12` for `E₄ ^ 3`. The pattern `rw [← ModularForm.coe_pow] … (E₄.pow 3)` appears 3 times
    in J/QExp.

### Completeness gaps

22. `poleOrder`: `_smul` (a ≠ 0), `_pow`, `_mul_le`, `_add_le`, `_inv`, `_eq_zero_iff`.
23. `laurentqExpansion`: `_inv`, `_div`, `_zpow`, `_eq_zero_iff`/injectivity, the `tsum` form, and
    "leading coefficient = `meromorphicTrailingCoeffAt`".
24. `toQExpansion`: `(toQExpansion h f).coeff 0 = meromorphicTrailingCoeffAt (cuspFunction h f) 0`. This is implicit
    in LQE/Basic:737–740.
25. `qExpansion_nat_mul` for ordinary `qExpansion`, the analytic companion of `toQExpansion_nat_mul`.
26. `qExpansionAt` at `ModularForm` level: `_add/_sub/_neg/_smul/_zero/_one/_pow`, `_injective`, `_eq_zero_iff`. Also
    the converse cusp-form criterion: constant term 0 at every cusp ⇒ cusp form. Mathlib has that criterion only at
    level 1.
27. `strictWidthAt`: `_mem_strictPeriods` (inlined at QE/Basic:112 and QE/CuspReps:156), the cocycle
    `strictWidthAt_mul`, and values for `Γ₀(N)`, `Γ₁(N)`, `Γ(N)`.
28. `Function.Periodic.qParam`: `_add` exists; `_zero`, `_neg`, `_sub`, `_zsmul` and `qParam N m ^ N = 1` are
    missing.
29. `integralDelta`: `C 1728 * integralDelta = integralE4 ^ 3 - integralE6 ^ 2` (the key identity, never stated),
    `map_integralDelta`, `coeff 0 = 0`, `coeff 1 = 1` and `order = 1`. `ramanujanTau`: `_zero`, `_one`, and
    `@[simp, norm_cast]` on `ramanujanTau_cast`.
30. `qjCoeffs_one = 744` and `qjCoeffs_two = 196884`. They are in `PhD/jFunction/qexp_coeffs.lean` and were not
    ported.
31. `j`: `j_apply`, a `j_vadd` T-invariance equation, and the natural `@[simp]` set (`qjCoeffs_zero`, `j_poleOrder`,
    `j_poleRemoved`, `j_toQExpansion`).
32. `PeriodPair`: `j_smul` and `j_congr` (dropped in the port), j invariance under `Homothetic`, a public
    `riemannZeta_six`, and the classical normalisation `(periodPair τ).discriminant = (2π)¹² · Δ(τ)`
    (64·1728/27 = 2¹²). That normalisation removes `E₄_cube_sub_E₆_sq_ne_zero_aux` and shortens `j_eq_periodPair_j`.
33. `HasCoeffsIn`: no `@[simp]` lemma at all. Also missing: `hasCoeffsIn_map`, transitivity along `R → S → A`,
    uniqueness of the lift for injective maps, and `HasCoeffsIn` of `mk`/`trunc`. There is also a binder
    inconsistency: `hasCoeffsIn_finset_prod` takes `A` implicit while every sibling takes it explicit.

---

## Part 7: Junk / Removable

### A. Delete: duplicates of mathlib or of another declaration

1. `periodic_comp_ofComplex_of_vadd` (LQE/Basic:205). Use mathlib's `UpperHalfPlane.periodic_comp_ofComplex`
   (3 call sites in J/QExp).
2. The copy of `E₄CubeSubE₆SqForm` (Δ/QExp:174–178). Use `qExpansionAlgHom` on
   `discriminant_eq_E₄_cube_sub_E₆_sq_graded`.
3. `modularFormModuleofIsScalarTower` (HasCoeffsIn:188), which is `FunLike.module`, together with the dead
   `modularFormQExpansionSubmodule` (:196).
4. `IntegralPowerSeriesSubring` (dead `toSubring` wrapper), `mapAlgHom_ofId_toIntegralPowerSeries` (duplicate) and
   `hasCoeffsIn_C_algebraMap` (duplicate).
5. All 14 `hasCoeffsIn_*` closure lemmas, once `HasCoeffsIn` is set-like membership (3a). 8 of them are unused
   anyway: `_one`, `_algebraMap`, `_C_algebraMap`, `_X`, `_finset_sum`, `_finset_prod`, `_neg`, `_sub`.
6. `meromorphicAt_cuspFunction_smul` (duplicate of `_const_mul`, unused).
7. `laurentqExpansion_smul` or `_const_mul`; keep one.
8. `laurentqExpansion.poleOrder_to_order` (rearrangement, unused).
9. Primed `laurentqExpansion.coeff_eq_zero_of_lt'`, `coeff_neg_poleOrder_add'`, `coeff_of_geq'` (`subst`
   wrappers; repoint the 2 J/QExp uses).
10. `qj` and its duplicated API (`qj_periodic`, `qj_mdifferentiable`, `qj_isBoundedAtImInfty`,
    `qj_cuspFunction_analyticAt`, `qj_apply`). Use `poleRemoved 1 j`.
11. Private `E₄_qExpansion_coeff`/`E₆_qExpansion_coeff` (Δ/QExp:35–41), after `E₄_q_exp`/`E₆_q_exp` are stated
    pointwise.
12. `eisenstein_difference_coeff_modEq_zero`, after `IsIntegralPowerSeriesmod` takes `∣`.
13. `coeff_mul_dvd_aux`, `coeff_pow_dvd_aux`. Use `CoeffMulMem` or `e4Bar = C 240 * g`.
14. `natMulOrderEmbedding` + `natMulOrderEmbedding_apply`, if `HahnSeries.embDomainRingHom` is adopted.

### B. Delete: dead wrappers and dead chains (zero uses anywhere)

15. `deltaShiftedQSeries`, `deltaShiftedQSeries_eq_deltaOverQ`, `qj_differentiableAt_of_im_pos`,
    `hasSum_qExpansion_qj` (J/QExp).
16. `integralE4_coeff_zero`, `integralE6_coeff_zero`, `integralE4_coeff_of_pos`, `integralE6_coeff_of_pos`
    (Δ/QExp:68–83). Their content belongs as `@[simp]` facts on the explicit definitions.
17. The `IsOfFinOrder` conjunct of `exists_qExpansionAt_coeff_eq_of_cuspOrbit_eq`. Its only caller (QE/ChangeRep:206)
    discards it. Drop it together with its support chain: `isOfFinOrder_qParam_natCast_int`,
    `exists_intCast_strictWidthAt`, `exists_natCast_strictWidthAt`, `exists_pos_natCast_strictWidthAt` (5
    declarations).
18. `SlashInvariantForm.qExpansionAt_mul_of_mdifferentiable` (QE/Algebra:37, glue, unused).
19. QE/ModularForm's five lemmas: `qExpansionAt_coeff_zero`, `hasSum_qExpansionAt`, `qExpansionAt_inj`,
    `qExpansionAt_mul` and `CuspForm.qExpansionAt_order_pos`. All are unused; after the `translate` bridge, either
    re-derive them as one-liners or delete them. Remove the `@[simp]` on `CuspForm.qExpansionAt_coeff_zero`: its LHS
    is not in simp normal form because of `PowerSeries.coeff_zero_eq_constantCoeff` (likely simpNF failure; confirm
    with `#lint`).
20. QE/Basic's unused `qExpansionAt_coeff`, `_zero`, `_of_mem`, `_add`, `_neg`, `_sub`, `_smul`. Keep them only as
    one-line corollaries of the bridge if a PR wants them.
21. `strictWidthAt_eq_of_smul_infty_eq`, `strictWidthAt_eq_of_cuspOrbit_eq`, `qExpansionAt_mul_T_zpow` (unused). If
    kept, derive them per Part 4 rows 26–27.
22. LQE/Basic unused: `meromorphicAt_cuspFunction_inv`, `_div`, `poleOrder_neg`, `laurentqExpansion.coeff_zero`,
    `toQExpansion_ne_zero`, `laurentqExpansion.toQExpansion_eq_powerSeriesPart`, `laurentqExpansion.eq_qExpansion_iff`.
    These are reasonable PR API; keep them only if the Laurent PR is going ahead.
23. LQE/Algebra unused: `laurentqExpansion_qParam_pow`, `_sub`, `_nat_mul_coeff_of_not_dvd`. They are automatic
    after bundling.
24. J/Properties unused: `j_apply_smul_I`, `j_apply_smul_rho`, `j_meromorphicOrderAt_nonneg` (wrapper),
    `tendsto_norm_j_atImInfty` (equivalent to its sibling).
25. J/EllipticCurve unused: `weierstrassCurve_c₆` (keep with `@[simps]`); `ellipticCurve_j` is the terminal result,
    so keep it.

### C. Inline or make private

26. `norm_lt_one_mem_nhdsNE_zero`, `eventually_ne_zero_and_norm_lt_one` (filter wrappers; generic root names),
    `analyticAt_cuspFunction_const`, `exists_pos_lt_one_differentiableOn_closedBall_to_analyticAt`.
27. `E₄_vadd_one_aux`, `discriminant_vadd_one_aux`, `cexp_vadd_one_aux`, `mdifferentiable_cexp_aux`. They disappear
    with `𝕢`, `eta_q` and the bundled `j`.
28. `E₄_cube_sub_E₆_sq_ne_zero_aux`, which disappears with the `(2π)¹²` normalisation. Also merge
    `periodPair_g₂_eq_E₄`/`periodPair_g₃_eq_E₆` into `periodPair_G_eq`.

### D. File hygiene (blocks any PR)

29. 13 deprecated names: `if_pos`/`if_neg` (LQE/Basic:364, 652, 787; LQE/Algebra:413, 415, 416; Δ/QExp:69, 73),
    `HahnSeries.embDomain_notin_range` (LQE/Algebra:418, 457), `ENat.coe_ne_top`, `ENat.map_coe`
    (LQE/Basic:238, 240). Also 2 `letI` lints (LQE/Basic:288, 318).
30. Add `module` and `public import` to the 10 files that lack them. Close or remove the unused
    `@[expose] public section`/`noncomputable section` in E/QExp, QE/Algebra, QE/ModularForm and QE/Order.
31. Header debris:
    - "Copied from XYin.PhD…" (E/QExp:14) and "dependency subset of XYin.PhD.Cox.LatticeJ" (J/Lattice).
    - Docstrings citing "Cox"/"project's" with no References section.
    - Author name inconsistent: "SmwYin" in E/QExp vs "Samuel Yin" elsewhere.
    - Unused `local notation "𝕢"` and `open`s in J/Lattice; unused `open`s in LQE/Basic:44–45. `open ModularForm`
      also brings protected-name lemmas into scope.
    - Variable shadowing at QE/ChangeRep:165–166.

---

## Part 8: Mathlibable Assessment

**Not run.** Step 9 was skipped at your request, so there are no `/mathlibable` verdicts. The list below is a
**triage list** built from the inventories' mathlib-overlap tables (Part C of each). Each item's pinned-mathlib
absence was checked by grep or leansearch. Upstream master was not checked systematically: loogle, which indexes
master, already shows `Mathlib.NumberTheory.ModularForms.OrderAtInfty`, which is absent at the pin. Run
`/mathlibable <decl>` on any item before opening a PR.

### Small standalone candidates (generic, self-contained)

| # | candidate | from | target in mathlib | note |
|---|---|---|---|---|
| 1 | `bernoulli'_six` (+ `riemannZeta_six`) | E/QExp:34, J/Lattice:159 | `NumberTheory/Bernoulli.lean` next to `bernoulli'_four`; `LSeries/HurwitzZetaValues.lean` | absent at pin and on master (agent: loogle) |
| 2 | `Function.Periodic.qParam_add` and companions | QE/ChangeRep:26 | `Analysis/Complex/Periodic.lean` | no algebraic `qParam` lemmas in mathlib |
| 3 | `UpperHalfPlane.qExpansion_const` | LQE/Basic:99 | `ModularForms/QExpansion.lean` | generalises `qExpansion_zero`/`_one` |
| 4 | `qExpansion_coeff_eq_circleIntegral_of_differentiableOn` | LQE/Basic:794 | same | mathlib's lemma becomes a corollary |
| 5 | `Tendsto.isBoundedAtImInfty`; `tendsto_atImInfty_of_continuousAt_cuspFunction`; `cuspFunction_apply_zero_of_tendsto` | J/QExp, LQE/Convergence | `QExpansion.lean`, `Periodic.lean` | removes inline copies in mathlib itself |
| 6 | `qExpansion_coeff_unique` for `f : ℍ → ℂ` (signature fix) | — | `QExpansion.lean` | removes two local `FunLike` hacks |
| 7 | matrix-level `ModularGroup.exists_eq_T_zpow_or_neg_of_c_eq_zero`, `mapGL_T_zpow`, the stabiliser of ∞ | QE/CuspReps | `NumberTheory/Modular.lean` | derive mathlib's existing lemma from it |
| 8 | `IsArithmetic` instance for `SL(2,ℤ)`-conjugates | QE/Basic:63–67 | `CongruenceSubgroups.lean` | used twice inside mathlib |
| 9 | `MeromorphicAt.aeval_polynomial` (G5) | LQE/Basic:171 | `Analysis/Meromorphic/Basic.lean` | mirror of `AnalyticAt.aeval_polynomial` |
| 10 | `meromorphicAt_comp_pow_iff` (G4) | LQE/Basic:315 | `Analysis/Meromorphic/Basic.lean` | mathlib has only the `deriv ≠ 0` case |
| 11 | iterated derivatives at a pole (Part 6 #12) | QE/Degenerate (inlined) | `Analysis/Meromorphic/Order.lean` | re-extract from the PhD precursor |
| 12 | `analyticOrderAt_const_mul_pow`, `meromorphicOrderAt_comp_const_mul_pow` | LQE/Basic:220, 229 | `Analysis/Analytic/Order.lean`, `Meromorphic/Order.lean` | corollaries of existing composition formulas |
| 13 | `HahnSeries.ofPowerSeries_expand` | LQE/Algebra:404 | `RingTheory/HahnSeries/PowerSeries.lean` | generic |
| 14 | `hasSum_int_iff_natCast_sub_of_eq_zero` | LQE/Convergence:24 | `Topology/Algebra/InfiniteSum/NatInt.lean` | generic |
| 15 | `PowerSeries.lifts` + `lifts_iff_coeff_lifts` (the `HasCoeffsIn` redesign) | HasCoeffsIn | `RingTheory/PowerSeries/Basic.lean` or a new `Lifts.lean` | mirror of `Polynomial.lifts` |
| 16 | `ModularForm.E_apply`; lattice `G_k([1,τ]) = 2ζ(k)E_k(τ)` (`periodPair_G_eq_aux`, now private) | J/Lattice | `ModularForms/EisensteinSeries/*`, `Elliptic/Weierstrass.lean` | bridges two existing mathlib APIs |
| 17 | `PeriodPair` scalar action and homogeneity of `G`, `g₂`, `g₃`; `PeriodPair.discriminant` and `discriminant_ne_zero`; `PeriodPair.j`; `weierstrassCurve` | J/Lattice, J/EllipticCurve | `Elliptic/Weierstrass.lean`, `EllipticCurve/*` | Cox §10; Silverman Ch. VI |
| 18 | vanishing of level-1 forms at `i` and `ρ` (G12) | J/Properties | `ModularForms/LevelOne/*` | Serre Ch. VII §3 |

### Series (need design decisions first)

- **S1. q-expansions at cusp representatives** (QE/*). First rebuild on `translate` (3b.1) and generalise to GL
  (G1). Most of the remaining content is the change-of-representative theory: QE/CuspReps, QE/ChangeRep and
  `qExpansionAt_order_eq_of_cuspOrbit_eq`. Rebase onto master's `OrderAtInfty` first.
- **S2. Laurent q-expansions** (LQE/*). First decide G3 (generic Laurent series of a meromorphic germ versus
  cusp-specific), then bundle (3b.2) and drop `0 < h` (G2).
- **S3. Arithmetic of level 1:** integrality of E₄, E₆ and Δ, τ, j and its integral Laurent expansion, special values,
  and the lattice ↔ curve ↔ analytic j link. It depends on S2 for j's Laurent expansion, and on #15 and #16. Use
  explicit `PowerSeries.mk` definitions (3a).

---

## Recommended Action Plan

### Priority 0: Decide the canonical tree (blocks everything)

Either:

- **(a) Recommended:** make `XYin/ForMathlib` canonical. Have the PhD files import it, delete their duplicate
  declarations, and add the ForMathlib modules to `XYin.lean` or to `globs`, so `lake build` checks them.
  Before deleting PhD copies, port back what the PhD side has and ForMathlib lost: `cuspFunction_apply_of_ne_zero`,
  `cuspFunction_eventuallyEq_comp`, `PeriodPair.j_smul`, `j_congr`, `coe_smulLatticeEquiv_apply`/`_symm_apply`,
  `qjCoeffs_one`/`_two`, and the standalone pole lemmas of `qexp_junk_values`.
- **(b)** Keep ForMathlib as a frozen PR-staging snapshot. In that case put it in the build as a separate target, and
  accept that each change must be made twice.

### Priority 1: Quick wins (mechanical, low risk)

- Fix the 13 deprecations and 2 `letI` lints. Add `module`/`public import` to 10 files. Remove header debris
  (Part 7 §D).
- Delete the exact mathlib duplicate `periodic_comp_ofComplex_of_vadd`, and the internal duplicates in Part 7 §A,
  items 3, 4, 6, 8 and 9.
- Delete the dead chains in Part 7 §B, items 15–18.
- Drop `0 < h` from the Laurent ring-operation lemmas (G2), starting with the three cases checked in Lean. Remove the
  redundant `hmero` via `meromorphicAt_cuspFunction_of_poleOrder_ne_zero` (G18).
- Put LQE/*, J/*, Δ/QExp and `HasCoeffsIn` into namespaces (`UpperHalfPlane`, `ModularForm`, `PowerSeries`). Rename
  the root `j` to avoid the `PeriodPair.j` clash.

### Priority 2: API improvements (high leverage)

- Add `qExpansionAt_eq_qExpansion_translate`, then re-derive or delete about 20 QE wrappers (3b.1).
- Reinstate `cuspFunction_apply_of_ne_zero`. Add `Tendsto.isBoundedAtImInfty`, `deltaOverQ_tendsto_atImInfty`,
  `mapGL_T_zpow` and the `IsArithmetic` conjugation instance (Part 6, items 2–7).
- Redesign `HasCoeffsIn` as `PowerSeries.lifts` (3a, G7). Define `integralE4`, `integralE6` and `integralDelta`
  explicitly, and state `C 1728 * integralDelta = integralE4³ − integralE6²`.
- Bundle `j` as `SlashInvariantForm 𝒮ℒ 0`. Delete `qj` in favour of `poleRemoved 1 j`. Use `𝕢` and `eta_q` in J/QExp.

### Priority 3: Generalisations (need mathematical judgement)

- G1: GL-valued `strictWidthAt`/`qExpansionAt`.
- G11: the cusp-orbit hypothesis form.
- G12: vanishing at elliptic points in general weight.
- G4 and G5: generic meromorphic lemmas.
- G10: GL-level slash lemmas.
- G16: `periodPair` for `τ ∉ ℝ`.

### Priority 4: Structural changes (major refactoring)

- Bundle `laurentqExpansion` as a `RingHom` (3b.2). This removes about 12 lemmas and the private `map_finset_*`
  helpers.
- Decide G3. If generic, introduce the Laurent series of a meromorphic germ and make `laurentqExpansion` its
  specialisation. This is also the point at which to add `laurentqExpansion` at a cusp representative, which
  connects the two pillars (Part 4, cross-pillar observation).
- Rebase onto mathlib master and re-express `poleOrder` through upstream `OrderAtInfty`.

### Priority 5: Mathlib contributions (from the Part 8 triage)

- Start with the cheap, self-contained items in Part 8: #1 (`bernoulli'_six`), #2 (`qParam_add`), #3–#6
  (q-expansion API gaps), #13–#14 (generic HahnSeries and tsum), #9–#11 (meromorphic lemmas).
- Run `/mathlibable` on each before opening a PR, and check master first.
- The three series S1–S3 come after Priorities 0–4.
