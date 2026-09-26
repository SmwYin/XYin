# Inventory: XYin/PhD/ModularFunctions/Basic.lean  (97 lines)

Defines the bundled structure `ModularFunction Γ` (extending mathlib's `SlashInvariantForm Γ 0`) whose underlying function is the canonical normal-form representative of an element of `MeromorphicField` (MeromorphicField.lean) and has at most exponential growth at every cusp (`OnePoint.IsOfExponentialGrowthAt`, GrowthAtCusp.lean). Provides `FunLike`/`SlashInvariantFormClass` instances, `ext`, the field element `toMeromorphicField`, meromorphy on ℍ, and the derived meromorphy at cusps (via Cusps.lean). Consumed by JInvariant, Congruence and eight Cox files.

## Declarations

### `structure ModularFunction`
- **Type**: `(Γ : Subgroup (GL (Fin 2) ℝ)) : Type` extending `SlashInvariantForm Γ 0` with fields `meromorphic' : ∃ a : MeromorphicField, MeromorphicField.toFun a = toFun` and `bdd_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsOfExponentialGrowthAt toFun`
- **What**: A weight-zero Γ-invariant function on ℍ which is a canonical meromorphic representative and grows at most exponentially at all cusps of Γ.
- **How**: structure extending `SlashInvariantForm Γ 0` (mathlib), mirroring the shape of mathlib's `ModularForm` (`Mathlib/NumberTheory/ModularForms/Basic.lean:75–77`, whose growth field is `c.IsBoundedAt toFun k`).
- **Hypotheses**: none.
- **Uses from project**: `UpperHalfPlane.MeromorphicField`, `MeromorphicField.toFun`, `OnePoint.IsOfExponentialGrowthAt`
- **Used by**: every declaration in the file.
- **Visibility**: public
- **Lines**: 31–35
- **Notes**: `meromorphic'` is an existential over the field; by `MeromorphicField.meromorphicNFOn_iff_exists` it is equivalent to the predicate `MeromorphicNFOn (toFun ∘ ofComplex) upperHalfPlaneSet` — using the predicate directly would avoid `choose` in `toMeromorphicField`. No algebraic instances (Zero/One/Add/Mul/SMul) are declared, so no diamond with `SlashInvariantForm.instAdd/instSMul` (`SlashInvariantForms.lean:114,141`); but see Missing API.

### `instance ModularFunction.instFunLike…` (anonymous `FunLike (ModularFunction Γ) ℍ ℂ`)
- **Type**: `FunLike (ModularFunction Γ) ℍ ℂ`
- **What**: coercion to functions, injective.
- **How**: `coe f := f.toFun`; injectivity by `cases f; cases g; congr; exact DFunLike.ext' h` — verbatim the mathlib pattern (`ModularForm.funLike`, `Basic.lean:106–109`).
- **Hypotheses**: none.
- **Uses from project**: `ModularFunction`
- **Used by**: `SlashInvariantFormClass` instance, `toSlashInvariantForm_coe`, `ext`, `toFun_toMeromorphicField`, `meromorphicNFOn`, `meromorphicOn`, `toMeromorphicField_injective`, `bdd_at_cusps`, `meromorphic_at_cusps`, `meromorphicAt_cuspFunction`
- **Visibility**: public
- **Lines**: 41–43
- **Notes**: mathlib gives these `(priority := 100)`; here default priority.

### `instance ModularFunction.instSlashInvariantFormClass…` (anonymous `SlashInvariantFormClass (ModularFunction Γ) Γ 0`)
- **Type**: `SlashInvariantFormClass (ModularFunction Γ) Γ 0`
- **What**: modular functions are slash-invariant of weight 0.
- **How**: `slash_action_eq f := f.slash_action_eq'`.
- **Hypotheses**: none.
- **Uses from project**: `ModularFunction`, `FunLike` instance
- **Used by**: implicit in `meromorphic_at_cusps` (coercion `f.toSlashInvariantForm`), `meromorphicAt_cuspFunction`.
- **Visibility**: public
- **Lines**: 45–46
- **Notes**: auto-named `instSlashInvariantFormClassOfNatInt` (checked via `#synth`); there is no `ModularFunctionClass` analogue of mathlib's `ModularFormClass`.

### `theorem ModularFunction.toSlashInvariantForm_coe`
- **Type**: `(f : ModularFunction Γ) : (f.toSlashInvariantForm : ℍ → ℂ) = f`
- **What**: the projection to `SlashInvariantForm` has the same underlying function.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `ModularFunction`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 48–50
- **Notes**: `@[simp]`; mirrors `ModularForm.toSlashInvariantForm_coe` (`Basic.lean:155`).

### `theorem ModularFunction.ext`
- **Type**: `{f g : ModularFunction Γ} (h : ∀ τ, f τ = g τ) : f = g`
- **What**: extensionality.
- **How**: `DFunLike.ext`.
- **Hypotheses**: pointwise equality.
- **Uses from project**: `ModularFunction`, `FunLike` instance
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 52–53
- **Notes**: `@[ext]`.

### `def ModularFunction.toMeromorphicField`
- **Type**: `(f : ModularFunction Γ) : MeromorphicField`
- **What**: the ambient field element of a modular function.
- **How**: `f.meromorphic'.choose`.
- **Hypotheses**: none.
- **Uses from project**: `ModularFunction`, `UpperHalfPlane.MeromorphicField`
- **Used by**: `toFun_toMeromorphicField`, `toMeromorphicField_injective`
- **Visibility**: public
- **Lines**: 55–56
- **Notes**: noncomputable via `choose`; the choice is unique by `MeromorphicField.toFun_injective`. Used by Cox/ModularFunctionField.lean and Cox/UpperHalfPlaneFunctionField.lean.

### `theorem ModularFunction.toFun_toMeromorphicField`
- **Type**: `(f : ModularFunction Γ) : MeromorphicField.toFun f.toMeromorphicField = f`
- **What**: the canonical representative of the field element is the bundled function.
- **How**: `choose_spec`.
- **Hypotheses**: none.
- **Uses from project**: `toMeromorphicField`, `MeromorphicField.toFun`
- **Used by**: `toMeromorphicField_injective`
- **Visibility**: public
- **Lines**: 58–61
- **Notes**: `@[simp]`.

### `theorem ModularFunction.meromorphicNFOn`
- **Type**: `(f : ModularFunction Γ) : MeromorphicNFOn (f ∘ ofComplex) upperHalfPlaneSet`
- **What**: modular functions are in meromorphic normal form on ℍ.
- **How**: `MeromorphicField.meromorphicNFOn_iff_exists` backwards with `f.meromorphic'`.
- **Hypotheses**: none.
- **Uses from project**: `MeromorphicField.meromorphicNFOn_iff_exists`, `ModularFunction`
- **Used by**: `meromorphicOn`, `meromorphic_at_cusps`, `meromorphicAt_cuspFunction`
- **Visibility**: public
- **Lines**: 63–66
- **Notes**: used by Cox/ModularFunctionField.lean.

### `theorem ModularFunction.meromorphicOn`
- **Type**: `(f : ModularFunction Γ) : MeromorphicOn (f ∘ ofComplex) upperHalfPlaneSet`
- **What**: modular functions are meromorphic on ℍ.
- **How**: `MeromorphicNFOn.meromorphicOn` (mathlib).
- **Hypotheses**: none.
- **Uses from project**: `meromorphicNFOn`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 68–70
- **Notes**: one-line wrapper; used by Cox/ModularFunctionField.lean and Cox/ModularFunction/CuspData.lean.

### `theorem ModularFunction.toMeromorphicField_injective`
- **Type**: `Function.Injective (toMeromorphicField (Γ := Γ))`
- **What**: modular functions are determined by their field element.
- **How**: `DFunLike.ext'` and `congrArg MeromorphicField.toFun` with `toFun_toMeromorphicField`.
- **Hypotheses**: none.
- **Uses from project**: `toMeromorphicField`, `toFun_toMeromorphicField`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 72–77, proof body ≈ 3 lines
- **Notes**: unused anywhere in the project.

### `theorem ModularFunction.bdd_at_cusps`
- **Type**: `(f : ModularFunction Γ) {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsOfExponentialGrowthAt f`
- **What**: the growth condition at a given cusp.
- **How**: projection of the structure field.
- **Hypotheses**: `c` a cusp of `Γ`.
- **Uses from project**: `ModularFunction`, `OnePoint.IsOfExponentialGrowthAt`
- **Used by**: `meromorphic_at_cusps`, `meromorphicAt_cuspFunction`
- **Visibility**: public
- **Lines**: 79–81
- **Notes**: used by Congruence.lean (`restrict`).

### `theorem ModularFunction.meromorphic_at_cusps`
- **Type**: `[DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] (f : ModularFunction Γ) {c} (hc : IsCusp c Γ) : c.IsMeromorphicAt f`
- **What**: a modular function is meromorphic (in the q-coordinate) at every cusp.
- **How**: `OnePoint.isOfExponentialGrowthAt_iff_isMeromorphicAt` (Cusps.lean) applied to `f.toSlashInvariantForm`, `f.meromorphicNFOn` and `f.bdd_at_cusps`.
- **Hypotheses**: `Γ` discrete with determinants `±1`; `c` a cusp.
- **Uses from project**: `OnePoint.isOfExponentialGrowthAt_iff_isMeromorphicAt`, `OnePoint.IsMeromorphicAt`, `meromorphicNFOn`, `bdd_at_cusps`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 83–87
- **Notes**: unused anywhere in the project.

### `theorem ModularFunction.meromorphicAt_cuspFunction`
- **Type**: `(f : ModularFunction Γ) {c} (hc : IsCusp c Γ) {g : GL (Fin 2) ℝ} (hg : g • OnePoint.infty = c) {h : ℝ} (hh : 0 < h) (hper : Function.Periodic ((f ∣[(0 : ℤ)] g) ∘ ofComplex) h) : MeromorphicAt (cuspFunction h (f ∣[(0 : ℤ)] g)) 0`
- **What**: in any positive-period chart at a cusp, the cusp function of the transformed modular function is meromorphic at 0.
- **How**: `OnePoint.isOfExponentialGrowthAt_iff_meromorphicAt_cuspFunction` (Cusps.lean) with `f.meromorphicNFOn` and `f.bdd_at_cusps`.
- **Hypotheses**: `c` a cusp, `g` a scaling matrix for `c`, `h > 0` a period of the transform.
- **Uses from project**: `OnePoint.isOfExponentialGrowthAt_iff_meromorphicAt_cuspFunction`, `meromorphicNFOn`, `bdd_at_cusps`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 89–95
- **Notes**: no group hypotheses needed (period supplied by the caller); used by Congruence.lean:108.

## File Summary
- Total declarations: 13 (1 structure, 1 def, 9 lemmas/theorems, 2 instances, 0 other)
- Key API (used by 3+ others in the file): `ModularFunction`, `FunLike` instance, `meromorphicNFOn`, `bdd_at_cusps`
- Unused declarations (not used by anything in this file): `toSlashInvariantForm_coe`, `ext`, `meromorphicOn`, `toMeromorphicField_injective`, `meromorphic_at_cusps`, `meromorphicAt_cuspFunction` (of these, `toMeromorphicField_injective` and `meromorphic_at_cusps` are unused project-wide)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations
### Mathlib API candidates
- The structure/`FunLike`/`ext`/`toSlashInvariantForm_coe` block (31–53) is a line-for-line copy of mathlib's `ModularForm` block (`Mathlib/NumberTheory/ModularForms/Basic.lean:75–77,106–109,155`) with `IsBoundedAt` replaced by `IsOfExponentialGrowthAt`; mathlib has no meromorphic modular function structure (searched `ModularFunction`, `IsMeromorphicAt` in `Mathlib/NumberTheory/ModularForms/`).
- `meromorphicOn` (68) is `MeromorphicNFOn.meromorphicOn` (`Mathlib/Analysis/Meromorphic/NormalForm.lean:501`) applied — one-line wrapper.
### Missing API / repeated patterns
- No `ModularFunctionClass` (cf. `ModularFormClass`, `Basic.lean:96`), no `Zero`/`One`/`Add`/`Mul`/`Inv`/`SMul ℂ` on `ModularFunction Γ` — the docstring (19–21) explains that pointwise operations do not preserve canonical representatives, so the natural operations are `toMeromorphicField`-transported: `(f * g).toMeromorphicField = f.toMeromorphicField * g.toMeromorphicField` with `toFun` of the product, plus growth via `IsOfExponentialGrowth.mul` (which does not exist either, see CuspGrowth.md). A `ModularFunction Γ ↪ MeromorphicField` subfield/`Subalgebra` description is what the Cox function-field files need.
- `toMeromorphicField` via `choose` (56): with `meromorphic'` replaced by `MeromorphicNFOn`, it would be `MeromorphicField.ofMeromorphic f f.meromorphicOn` (computable modulo `ofMeromorphic`) and `toFun_toMeromorphicField` would be `MeromorphicField.toFun_ofMeromorphic`.
### Junk candidates
- `toMeromorphicField_injective` (72–77) and `meromorphic_at_cusps` (83–87): unused project-wide (`grep -rlw`).
### Moral duplicates within this batch
- `toMeromorphicField_injective` (72) ~ `MeromorphicField.toFun_injective` (MeromorphicField.lean:626) ~ `holomorphicToMeromorphic_injective` (FieldAction.lean:59): same 3-line skeleton.
- `meromorphic_at_cusps` (83) is `SlashInvariantForm.exponential_growth_at_cusps_iff` (Cusps.lean:79) at one cusp.
### Generalization notes
- `meromorphicAt_cuspFunction` (89) needs no `Γ` hypotheses; `meromorphic_at_cusps` needs `[DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]` only to obtain a positive period (CuspPeriod.lean). Nothing in the file uses `Γ` beyond `SlashInvariantForm`.
