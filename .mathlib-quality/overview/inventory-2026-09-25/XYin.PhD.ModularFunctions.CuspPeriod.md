# Inventory: XYin/PhD/ModularFunctions/CuspPeriod.lean  (62 lines)

Shows that a slash-invariant form for a discrete subgroup `Γ ≤ GL₂(ℝ)` with determinants `±1` has a positive real period in every cusp chart: conjugating `Γ` by the scaling matrix transports discreteness (`discreteTopology_conj`) and the determinant condition (`hasDetPlusMinusOne_conj`), so mathlib's `strictWidthInfty` of the conjugate is a positive period of the translated form. Supplies the period needed by Cusps.lean.

## Declarations

### `instance Subgroup.hasDetPlusMinusOne_conj`
- **Type**: `(Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetPlusMinusOne] (g : GL (Fin 2) ℝ) : (ConjAct.toConjAct g • Γ).HasDetPlusMinusOne`
- **What**: conjugate subgroups keep determinants in `{±1}`.
- **How**: destructure membership in the pointwise image, `det (g x g⁻¹) = det x` by `map_mul`, `map_inv`, commutativity.
- **Hypotheses**: `Γ.HasDetPlusMinusOne`.
- **Uses from project**: []
- **Used by**: `SlashInvariantForm.exists_pos_period_at_cusp` (instance resolution for `Γ'.strictWidthInfty_pos_iff`)
- **Visibility**: public
- **Lines**: 21–27, proof body ≈ 4 lines
- **Notes**: no mathlib analogue (grep `ConjAct|conj` in `Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`: none). Mathlib's `IsCusp.smul` (`Cusps.lean:62`) already produces `ConjAct.toConjAct g • 𝒢`, so this instance belongs upstream next to `HasDetPlusMinusOne` (`ArithmeticSubgroups.lean:37`).

### `theorem Subgroup.discreteTopology_conj`
- **Type**: `{G} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G) [DiscreteTopology Γ] (g : G) : DiscreteTopology ↥(ConjAct.toConjAct g • Γ)`
- **What**: conjugates of discrete subgroups of a topological group are discrete.
- **How**: the continuous injection `x ↦ g⁻¹ x g : (g • Γ) → Γ` (membership via `Subgroup.mem_pointwise_smul_iff_inv_smul_mem`) and `DiscreteTopology.of_continuous_injective`; continuity by `fun_prop`.
- **Hypotheses**: `Γ` discrete, `G` topological group.
- **Uses from project**: []
- **Used by**: `SlashInvariantForm.exists_pos_period_at_cusp`
- **Visibility**: public
- **Lines**: 29–42, proof body ≈ 10 lines
- **Notes**: no mathlib analogue (searched `DiscreteTopology` × `ConjAct|pointwise|•` in `Mathlib/Topology/Algebra`, `NumberTheory/ModularForms`). The hand-built map `e` is `(Subgroup.equivSMul (ConjAct.toConjAct g) Γ).symm` (`Mathlib/Algebra/Group/Subgroup/Pointwise.lean:504`); stated as a theorem, not an instance (cannot be an instance since `g` is not inferable — fine). Upstream candidate for `Mathlib/Topology/Algebra/Group/…`.

### `theorem SlashInvariantForm.exists_pos_period_at_cusp`
- **Type**: `{Γ} {k : ℤ} [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] (f : SlashInvariantForm Γ k) {c} (hc : IsCusp c Γ) (g : GL (Fin 2) ℝ) (hg : g • OnePoint.infty = c) : ∃ h : ℝ, 0 < h ∧ Function.Periodic (((f : ℍ → ℂ) ∣[k] g) ∘ ofComplex) h`
- **What**: in the chart `g` at the cusp `c`, the transformed form is periodic with some positive period.
- **How**: `Γ' := g⁻¹ Γ g` is discrete (`discreteTopology_conj`) with `∞` a cusp (`IsCusp.smul`); `h := Γ'.strictWidthInfty`, positive by mathlib `strictWidthInfty_pos_iff`; periodicity of `translate f g` (a `SlashInvariantForm Γ' k`) by `SlashInvariantFormClass.periodic_comp_ofComplex` and `strictWidthInfty_mem_strictPeriods`.
- **Hypotheses**: `Γ` discrete with determinants `±1`; `c` a cusp; `g • ∞ = c`.
- **Uses from project**: `Subgroup.discreteTopology_conj`, `Subgroup.hasDetPlusMinusOne_conj` (instance)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 48–60, proof body ≈ 7 lines
- **Notes**: used by Cusps.lean:67. Works at any weight `k`. Mathlib ingredients: `Cusps.lean:320,357,378`, `SlashInvariantForms.lean:299 translate`, `QExpansion.lean:120`.

## File Summary
- Total declarations: 3 (0 defs, 2 lemmas/theorems, 1 instance, 0 other)
- Key API (used by 3+ others in the file): none
- Unused declarations (not used by anything in this file): `exists_pos_period_at_cusp` (used by Cusps.lean)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations
### Mathlib API candidates
- Both `Subgroup.hasDetPlusMinusOne_conj` (21) and `Subgroup.discreteTopology_conj` (29) are missing in mathlib and are the natural companions of `IsCusp.smul` (`Mathlib/NumberTheory/ModularForms/Cusps.lean:62`); `discreteTopology_conj` should go through `Subgroup.equivSMul` + `DiscreteTopology.of_continuous_injective` (`Mathlib/Topology/Order.lean:392`) or, more generally, via the homeomorphism `Homeomorph.mulLeft g` ∘ `mulRight g⁻¹` restricted (a subgroup homeomorphic to a discrete one is discrete).
- `exists_pos_period_at_cusp` is a clean composition of mathlib's strict-width API; a mathlib-level lemma `SlashInvariantFormClass.exists_pos_period_translate` would be welcome next to `periodic_comp_ofComplex`.
### Missing API / repeated patterns
- An `IsArithmetic`-conjugation instance (`(ConjAct.toConjAct g • Γ).IsArithmetic`) is absent; not needed here but the analogous gap.
### Junk candidates
- `open UpperHalfPlane MatrixGroups ModularForm` (16) and `open scoped MatrixGroups Pointwise` (17): `MatrixGroups` opened twice.
### Moral duplicates within this batch
- none.
### Generalization notes
- `discreteTopology_conj` is already fully general (any topological group). `exists_pos_period_at_cusp` is stated for any weight `k`, although the folder only uses `k = 0`.
