# Inventory: XYin/PhD/Modularforms/IsCuspForm.lean  (152 lines)

Inclusion of cusp forms into modular forms as a ℂ-linear map, the cusp-form submodule and the `IsCuspForm` predicate, extraction of a `CuspForm` from a proof of `IsCuspForm`, constructors of cusp forms from "tends to 0 at i∞" / "vanishing constant term", and the level-one criterion `IsCuspForm ↔ a₀ = 0`. This is a pre-upstream twin of mathlib's `Mathlib/NumberTheory/ModularForms/CuspFormSubmodule.lean` (Birkbeck 2026, present in the pinned mathlib), stated for `Γ(1)` instead of `𝒮ℒ`. Imported by Eisenstein.lean (uses `IsCuspForm`, `cuspFormOfCoeffZero`, `IsCuspForm_iff_coeffZero_eq_zero`) and transitively by DimensionFormulas.lean.

## Declarations

### `def ModForm_mk`
- **Type**: `(Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) : ModularForm Γ k`
- **What**: Forgets the vanishing-at-cusps condition of a cusp form, producing a modular form with the same function.
- **How**: Structure literal reusing `f.slash_action_eq'`, `f.holo'`, and boundedness from mathlib `ModularFormClass.bdd_at_cusps` (`Mathlib/NumberTheory/ModularForms/Basic.lean:96`, via the `CuspFormClass → ModularFormClass` instance).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: ModForm_mk_inj, CuspForm_to_ModularForm, CuspForm_iso_CuspFormSubmodule, instance CuspFormClass (CuspFormSubmodule), IsCuspForm_iff_coeffZero_eq_zero; externally DimensionFormulas.lean (mul_Delta_map, mul_Delta_map_eq_mul, Delta_E4_E6_eq)
- **Visibility**: public
- **Lines**: 27–31, body 4 lines
- **Notes**: mathlib already has the coercion `(f : ModularForm Γ k)` = `ModularFormClass.modularForm f` and `CuspForm.toModularFormₗ_eq_coe` (`CuspFormSubmodule.lean:55`).

### `lemma ModForm_mk_inj`
- **Type**: `(Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) (hf : f ≠ 0) : ModForm_mk _ _ f ≠ 0`
- **What**: `ModForm_mk` sends nonzero cusp forms to nonzero modular forms.
- **How**: `DFunLike.ext` / `DFunLike.congr_fun` pointwise.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: ModForm_mk
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 33–36, body 2 lines
- **Notes**: unused anywhere; mathlib `CuspForm.toModularFormₗ_injective` (`CuspFormSubmodule.lean:58`).

### `def CuspForm_to_ModularForm`
- **Type**: `(Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k`
- **What**: The inclusion of cusp forms into modular forms as a ℂ-linear map.
- **How**: `toFun := ModForm_mk Γ k`; additivity/homogeneity by `simp only [ModForm_mk, …]; rfl`.
- **Hypotheses**: none.
- **Uses from project**: ModForm_mk
- **Used by**: CuspFormSubmodule, CuspForm_iso_CuspFormSubmodule, mem_CuspFormSubmodule, instance CuspFormClass, CuspForm_to_ModularForm_coe, IsCuspForm_iff_coeffZero_eq_zero; externally DimensionFormulas.lean (mul_Delta_IsCuspForm, IsCuspForm_weight_lt_eq_zero)
- **Visibility**: public
- **Lines**: 38–48, body ≈ 8 lines
- **Notes**: = mathlib `CuspForm.toModularFormₗ` (`CuspFormSubmodule.lean:46`, whose proofs are `rfl`).

### `def CuspFormSubmodule`
- **Type**: `(Γ : Subgroup SL(2, ℤ)) (k : ℤ) : Submodule ℂ (ModularForm Γ k)`
- **What**: The submodule of modular forms that are cusp forms, as the range of the inclusion.
- **How**: `LinearMap.range (CuspForm_to_ModularForm Γ k)`.
- **Hypotheses**: none.
- **Uses from project**: CuspForm_to_ModularForm
- **Used by**: CuspForm_iso_CuspFormSubmodule, mem_CuspFormSubmodule, CuspFormSubmodule.funLike, instance CuspFormClass, IsCuspForm, IsCuspForm_to_CuspForm, IsCuspForm_iff_coeffZero_eq_zero, CuspFormSubmodule_mem_iff_coeffZero_eq_zero
- **Visibility**: public
- **Lines**: 50–51, body 1 line
- **Notes**: = mathlib `ModularForm.cuspFormSubmodule` (`CuspFormSubmodule.lean:68`). Not referenced by any other project file.

### `def CuspForm_iso_CuspFormSubmodule`
- **Type**: `(Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspForm Γ k ≃ₗ[ℂ] CuspFormSubmodule Γ k`
- **What**: Cusp forms are linearly isomorphic to the cusp-form submodule.
- **How**: `LinearEquiv.ofInjective` with injectivity via `injective_iff_map_eq_zero`, unfolding `CuspForm_to_ModularForm` by `rw`/`simp` and `congr_arg (·.toFun)`.
- **Hypotheses**: none.
- **Uses from project**: CuspFormSubmodule, CuspForm_to_ModularForm, ModForm_mk
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 53–62, body ≈ 8 lines
- **Notes**: unused anywhere; data built by a tactic block (`apply LinearEquiv.ofInjective`); `rw [CuspForm_to_ModularForm] at hf` unfolds a definition by `rw`. = mathlib `CuspForm.equivCuspFormSubmodule` (`CuspFormSubmodule.lean:81`).

### `lemma mem_CuspFormSubmodule`
- **Type**: `(Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) (hf : f ∈ CuspFormSubmodule Γ k) : ∃ g : CuspForm Γ k, f = CuspForm_to_ModularForm Γ k g`
- **What**: Unpacks membership in the cusp-form submodule as being the image of a cusp form.
- **How**: `LinearMap.mem_range` + `aesop`.
- **Hypotheses**: `f` in the submodule.
- **Uses from project**: CuspFormSubmodule, CuspForm_to_ModularForm
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 64–68, body 2 lines
- **Notes**: unused anywhere; is `LinearMap.mem_range.mp hf` up to `Eq.symm` — junk.

### `instance CuspFormSubmodule.funLike`
- **Type**: `(priority := 100) : FunLike (CuspFormSubmodule Γ k) ℍ ℂ` (Γ, k implicit from `variable` L23)
- **What**: Elements of the cusp-form submodule act as functions `ℍ → ℂ`.
- **How**: `coe f := f.1.toFun`; injectivity by `cases`/`congr`/`DFunLike.ext'`.
- **Hypotheses**: none.
- **Uses from project**: CuspFormSubmodule
- **Used by**: instance CuspFormClass (CuspFormSubmodule)
- **Visibility**: public
- **Lines**: 70–72, body 2 lines
- **Notes**: no mathlib analogue (mathlib's `cuspFormSubmodule` has no `FunLike`); only consumer is the next instance, which is itself unused.

### `instance instCuspFormClassCuspFormSubmodule` (anonymous; `(Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspFormClass (CuspFormSubmodule Γ k) Γ k`)
- **Type**: `CuspFormClass (CuspFormSubmodule Γ k) Γ k`
- **What**: Elements of the cusp-form submodule satisfy the cusp-form axioms.
- **How**: Slash-invariance and holomorphy from the underlying modular form; vanishing at cusps by `rintro ⟨_, ⟨g, rfl⟩⟩` and `g.zero_at_cusps'` after unfolding `CuspForm_to_ModularForm`/`ModForm_mk`.
- **Hypotheses**: none.
- **Uses from project**: CuspFormSubmodule, CuspForm_to_ModularForm, ModForm_mk, CuspFormSubmodule.funLike
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 74–79, body ≈ 4 lines
- **Notes**: unused anywhere; takes `(Γ) (k)` explicitly whereas the FunLike instance takes them implicitly.

### `def IsCuspForm`
- **Type**: `(Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) : Prop`
- **What**: A modular form is a cusp form iff it lies in the cusp-form submodule.
- **How**: `f ∈ CuspFormSubmodule Γ k`.
- **Hypotheses**: none.
- **Uses from project**: CuspFormSubmodule
- **Used by**: IsCuspForm_to_CuspForm, CuspForm_to_ModularForm_coe, CuspForm_to_ModularForm_Fun_coe, IsCuspForm_iff_coeffZero_eq_zero; externally DimensionFormulas.lean (mul_Delta_IsCuspForm, Modform_mul_Delta', IsCuspForm_weight_lt_eq_zero), Eisenstein.lean:422 (modularForm_normalise)
- **Visibility**: public
- **Lines**: 81–82, body 1 line
- **Notes**: = mathlib `ModularForm.IsCuspForm` (`CuspFormSubmodule.lean:73`, Γ and k implicit there); mathlib also has `isCuspForm_iff : IsCuspForm f ↔ ∀ c, IsCusp c Γ → c.IsZeroAt f k` (:92), a general-Γ characterisation this file lacks.

### `def IsCuspForm_to_CuspForm`
- **Type**: `(Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) (hf : IsCuspForm Γ k f) : CuspForm Γ k`
- **What**: Chooses a cusp form underlying a modular form known to be a cusp form.
- **How**: `rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf; exact hf.choose` (classical choice).
- **Hypotheses**: `f` is a cusp form.
- **Uses from project**: IsCuspForm, CuspFormSubmodule
- **Used by**: CuspForm_to_ModularForm_coe, CuspForm_to_ModularForm_Fun_coe; externally DimensionFormulas.lean (Modform_mul_Delta', Modform_mul_Delta_apply)
- **Visibility**: public
- **Lines**: 84–87, body 2 lines
- **Notes**: data defined via `rw … at hf` + `choose` — the term carries `Eq.mpr` casts and is opaque. Preferable: `(CuspForm.equivCuspFormSubmodule Γ k).symm ⟨f, hf⟩`, or the direct structure `⟨f.toSlashInvariantForm, f.holo', (isCuspForm_iff f).mp hf⟩` (mathlib `CuspFormSubmodule.lean:81/:92`), both of which make the coercion lemma below `rfl`.

### `lemma CuspForm_to_ModularForm_coe`
- **Type**: `(Γ) (k) (f : ModularForm Γ k) (hf : IsCuspForm Γ k f) : (IsCuspForm_to_CuspForm Γ k f hf).toSlashInvariantForm = f.toSlashInvariantForm`
- **What**: The chosen cusp form has the same underlying slash-invariant form as `f`.
- **How**: `congrArg ModularForm.toSlashInvariantForm hf.choose_spec`.
- **Hypotheses**: `f` is a cusp form.
- **Uses from project**: IsCuspForm, IsCuspForm_to_CuspForm, CuspForm_to_ModularForm
- **Used by**: CuspForm_to_ModularForm_Fun_coe
- **Visibility**: public
- **Lines**: 89–93, body 2 lines
- **Notes**: name says `CuspForm_to_ModularForm` but it is about `IsCuspForm_to_CuspForm` — misleading.

### `lemma CuspForm_to_ModularForm_Fun_coe`
- **Type**: `(Γ) (k) (f) (hf) : (IsCuspForm_to_CuspForm Γ k f hf).toFun = f.toFun`
- **What**: The chosen cusp form has the same underlying function as `f`.
- **How**: `congrArg SlashInvariantForm.toFun` of the previous lemma.
- **Hypotheses**: `f` is a cusp form.
- **Uses from project**: IsCuspForm, IsCuspForm_to_CuspForm, CuspForm_to_ModularForm_coe
- **Used by**: unused in file; externally DimensionFormulas.lean:95 (Modform_mul_Delta_apply)
- **Visibility**: public
- **Lines**: 95–98, body 1 line
- **Notes**: stated with raw `.toFun` projections; the idiomatic form is `⇑(IsCuspForm_to_CuspForm Γ k f hf) = ⇑f` tagged `@[simp]`.

### `noncomputable def cuspFormOfSIFTendstoZero`
- **Type**: `{k : ℤ} (f_SIF : SlashInvariantForm Γ(1) k) (h_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f_SIF.toFun) (h_zero : Tendsto f_SIF.toFun atImInfty (𝓝 0)) : CuspForm Γ(1) k`
- **What**: A holomorphic `Γ(1)`-invariant function tending to 0 at i∞ is a cusp form.
- **How**: `zero_at_cusps_of_zero_at_infty` reduces vanishing at each cusp to `IsZeroAtImInfty (f ∣[k] A)` for `A ∈ 𝒮ℒ`; `Γ(1)`-invariance (`slash_action_eq'` with `CongruenceSubgroup.mem_Gamma_one`) rewrites `f ∣[k] A = f`, so `h_zero` applies.
- **Hypotheses**: `f` holomorphic on ℍ and `f → 0` at i∞.
- **Uses from project**: zero_at_cusps_of_zero_at_infty (ForMathlib_Cusps.lean)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 100–111, body ≈ 5 lines
- **Notes**: unused anywhere. Has a docstring. Mathlib: `(isCuspForm_iff f).mpr` (`CuspFormSubmodule.lean:92`) gives this for any Γ.

### `private lemma isZeroAtImInfty_of_coeffZero`
- **Type**: `{k : ℤ} (f : ModularForm Γ(1) k) (h : (qExpansion 1 f).coeff 0 = 0) : IsZeroAtImInfty f`
- **What**: A level-one modular form with vanishing constant q-coefficient tends to 0 at i∞.
- **How**: The constant term is `cuspFunction 1 f 0` (mathlib `qExpansion_coeff`, `QExpansion.lean:169`); continuity of the cusp function at 0 (`ModularFormClass.analyticAt_cuspFunction_zero`, `QExpansion.lean:153`) composed with `qParam_tendsto_atImInfty` (:67) via `SlashInvariantFormClass.eq_cuspFunction` (:132).
- **Hypotheses**: `a₀(f) = 0`.
- **Uses from project**: []
- **Used by**: cuspFormOfCoeffZero
- **Visibility**: private
- **Lines**: 113–120, body ≈ 4 lines
- **Notes**: = mathlib `ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero` (`CuspFormSubmodule.lean:97`) + `qExpansion_coeff_zero` (`QExpansion.lean:408`).

### `noncomputable def cuspFormOfCoeffZero`
- **Type**: `{k : ℤ} (f : ModularForm Γ(1) k) (h : (qExpansion 1 f).coeff 0 = 0) : CuspForm Γ(1) k`
- **What**: Builds a cusp form from a level-one modular form whose constant q-coefficient vanishes.
- **How**: Same pattern as `cuspFormOfSIFTendstoZero`, with `isZeroAtImInfty_of_coeffZero` supplying the limit.
- **Hypotheses**: `a₀(f) = 0`.
- **Uses from project**: zero_at_cusps_of_zero_at_infty (ForMathlib_Cusps.lean), isZeroAtImInfty_of_coeffZero
- **Used by**: IsCuspForm_iff_coeffZero_eq_zero; externally Eisenstein.lean:329 (definition of `Delta_E4_E6_aux`)
- **Visibility**: public
- **Lines**: 122–132, body ≈ 5 lines
- **Notes**: = mathlib `ModularForm.toCuspForm` (`CuspFormSubmodule.lean:127`, `toCuspForm_apply` :131). No `_apply` lemma here (users rely on `rfl`).

### `lemma IsCuspForm_iff_coeffZero_eq_zero`
- **Type**: `(k : ℤ) (f : ModularForm Γ(1) k) : IsCuspForm Γ(1) k f ↔ (qExpansion 1 f).coeff 0 = 0`
- **What**: A level-one modular form is a cusp form iff its constant q-coefficient vanishes.
- **How**: (→) unfold `qExpansion_coeff` at index 0 (`iteratedDeriv_zero`), obtain `g` with `CuspForm_to_ModularForm g = f`, apply mathlib `CuspFormClass.cuspFunction_apply_zero` (`QExpansion.lean:402`) to `g`; (←) witness `cuspFormOfCoeffZero f h` with `ext; rfl`.
- **Hypotheses**: none.
- **Uses from project**: IsCuspForm, CuspFormSubmodule, CuspForm_to_ModularForm, ModForm_mk, cuspFormOfCoeffZero
- **Used by**: CuspFormSubmodule_mem_iff_coeffZero_eq_zero; externally Eisenstein.lean:427
- **Visibility**: public
- **Lines**: 134–148, body ≈ 13 lines
- **Notes**: = mathlib `ModularForm.isCuspForm_iff_coeffZero_eq_zero` (`CuspFormSubmodule.lean:136`) for `𝒮ℒ`.

### `lemma CuspFormSubmodule_mem_iff_coeffZero_eq_zero`
- **Type**: `(k : ℤ) (f : ModularForm Γ(1) k) : f ∈ CuspFormSubmodule Γ(1) k ↔ (qExpansion 1 f).coeff 0 = 0`
- **What**: Membership form of the previous lemma.
- **How**: `exact IsCuspForm_iff_coeffZero_eq_zero k f` (definitional).
- **Hypotheses**: none.
- **Uses from project**: CuspFormSubmodule, IsCuspForm_iff_coeffZero_eq_zero
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 150–152, body 1 line
- **Notes**: unused anywhere; `Iff.rfl`-level restatement (mathlib `mem_cuspFormSubmodule_iff` :77 is `@[simp]`).

## File Summary
- Total declarations: 17 (8 defs: ModForm_mk, CuspForm_to_ModularForm, CuspFormSubmodule, CuspForm_iso_CuspFormSubmodule, IsCuspForm, IsCuspForm_to_CuspForm, cuspFormOfSIFTendstoZero, cuspFormOfCoeffZero; 7 lemmas; 2 instances; 0 other)
- Key API (used by 3+ others in the file): CuspFormSubmodule (8), CuspForm_to_ModularForm (6), ModForm_mk (5), IsCuspForm (4)
- Unused declarations (not used by anything in this file): ModForm_mk_inj, CuspForm_iso_CuspFormSubmodule, mem_CuspFormSubmodule, instance CuspFormClass (CuspFormSubmodule), CuspForm_to_ModularForm_Fun_coe (used by DimensionFormulas), cuspFormOfSIFTendstoZero, CuspFormSubmodule_mem_iff_coeffZero_eq_zero
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest: IsCuspForm_iff_coeffZero_eq_zero, 13 lines)

## Observations

### Mathlib API candidates
- **The entire file is now in mathlib** as `Mathlib/NumberTheory/ModularForms/CuspFormSubmodule.lean` (pinned rev), for general `Γ : Subgroup (GL (Fin 2) ℝ)` `[Γ.HasDetOne]` with the level-one part for `𝒮ℒ`. Mapping (project → mathlib): `ModForm_mk` → coercion / `CuspForm.toModularFormₗ_eq_coe` (:55); `ModForm_mk_inj` → `CuspForm.toModularFormₗ_injective` (:58); `CuspForm_to_ModularForm` → `CuspForm.toModularFormₗ` (:46, `toModularFormₗ_apply` :52 is `@[simp]`); `CuspFormSubmodule` → `ModularForm.cuspFormSubmodule` (:68); `CuspForm_iso_CuspFormSubmodule` → `CuspForm.equivCuspFormSubmodule` (:81); `IsCuspForm` → `ModularForm.IsCuspForm` (:73) with `mem_cuspFormSubmodule_iff` (:77) and the general `isCuspForm_iff` (:92); `isZeroAtImInfty_of_coeffZero` → `isZeroAtImInfty_of_valueAtInfty_eq_zero` (:97) / `isZeroAt_of_coeffZero_eq_zero` (:113); `cuspFormOfCoeffZero` → `ModularForm.toCuspForm` (:127) + `toCuspForm_apply` (:131); `IsCuspForm_iff_coeffZero_eq_zero` → `ModularForm.isCuspForm_iff_coeffZero_eq_zero` (:136). Only `IsCuspForm_to_CuspForm`, the two `_coe` lemmas, `cuspFormOfSIFTendstoZero` and the two instances have no named counterpart, and each is composable from `equivCuspFormSubmodule`/`isCuspForm_iff`.
- **Obstacle to a drop-in replacement**: everything here is stated for `Γ(1)` (a `Subgroup SL(2,ℤ)` coerced to `GL`) while mathlib's level-one results are for `𝒮ℒ`; a scratch check this session (`lake env lean`) of `ModularForm.isCuspForm_iff_coeffZero_eq_zero f` at `f : ModularForm Γ(1) k` fails with an `isDefEq` heartbeat timeout, so callers (Eisenstein.lean:329/:422/:427, DimensionFormulas.lean) need either a `Gamma_one_coe_eq_SL` transport or to be restated over `𝒮ℒ`.
- Hand-rolled pattern: `IsCuspForm_to_CuspForm` uses `Classical.choose` on range membership (L86–87) where `LinearEquiv.ofInjective … |>.symm` (already used at L55 for the iso) gives a canonical inverse with `LinearEquiv.apply_symm_apply` for free.

### Missing API / repeated patterns
- L107–111 and L128–132 are the same 4-line fragment (`apply zero_at_cusps_of_zero_at_infty hc; intro A ⟨A', hA'⟩; rw [slash_action_eq' …]; exact _`): a lemma `cuspForm_of_isZeroAtImInfty (f : SlashInvariantForm Γ(1) k) (hf : MDiff f) (h : IsZeroAtImInfty f) : CuspForm Γ(1) k` (which is what `cuspFormOfSIFTendstoZero` *is* — `cuspFormOfCoeffZero` should just call it).
- `cuspFormOfCoeffZero` / `IsCuspForm_to_CuspForm` lack `@[simp]` `_apply`/`coe` lemmas (`CuspForm_to_ModularForm_Fun_coe` is stated with `.toFun`, not `⇑`).
- `IsCuspForm` lacks the general characterisation `IsCuspForm ↔ ∀ cusps, IsZeroAt` (mathlib `isCuspForm_iff`).

### Junk candidates
- Unused anywhere: ModForm_mk_inj (L33), CuspForm_iso_CuspFormSubmodule (L53), mem_CuspFormSubmodule (L64), instance CuspFormClass (L74) and its only consumer `CuspFormSubmodule.funLike` (L70), cuspFormOfSIFTendstoZero (L100), CuspFormSubmodule_mem_iff_coeffZero_eq_zero (L150).
- Stray imports: `Mathlib.Analysis.CStarAlgebra.Module.Defs` (L3) has nothing to do with the content; `XYin.PhD.Modularforms.qExpansion_lems` (L6) — no declaration of that module is referenced by name here (all q-expansion lemmas used are mathlib's), likely droppable.
- Dead `variable` binders: `{α ι : Type*}` (L20), `(n : ℕ) (f : F)` (L23).
- Name mismatch: `CuspForm_to_ModularForm_coe`/`_Fun_coe` (L89/L95) are about `IsCuspForm_to_CuspForm`, not `CuspForm_to_ModularForm`.

### Moral duplicates within this batch
- `cuspFormOfSIFTendstoZero` (L101) and `cuspFormOfCoeffZero` (L123): identical `zero_at_cusps'` proofs; the second is the first applied to `f.toSlashInvariantForm` with `isZeroAtImInfty_of_coeffZero`.
- `IsCuspForm_iff_coeffZero_eq_zero` (L134) ≡ `CuspFormSubmodule_mem_iff_coeffZero_eq_zero` (L150).
- `ModForm_mk_inj` (L33) is the contrapositive of the injectivity proved inline in `CuspForm_iso_CuspFormSubmodule` (L56–62).
- Against DimensionFormulas.lean: `mul_Delta_IsCuspForm`/`Modform_mul_Delta'` there re-derive a cusp form through `IsCuspForm_to_CuspForm` although the witness is explicit.

### Generalization notes
- `ModForm_mk`, `CuspForm_to_ModularForm`, `CuspFormSubmodule`, `CuspForm_iso_CuspFormSubmodule`, `IsCuspForm`, `IsCuspForm_to_CuspForm` and the two `_coe` lemmas take `Γ : Subgroup SL(2, ℤ)`; nothing in their proofs uses `SL(2,ℤ)` — they hold for any `Γ : Subgroup (GL (Fin 2) ℝ)` with `[Γ.HasDetOne]` (exactly mathlib's generality).
- `cuspFormOfSIFTendstoZero`/`cuspFormOfCoeffZero`/`IsCuspForm_iff_coeffZero_eq_zero` genuinely use level one (`mem_Gamma_one`, width 1); mathlib's `isZeroAtImInfty_of_valueAtInfty_eq_zero` (:97) generalises the first step to any Γ with `Fact (IsCusp ∞ Γ)` and discrete topology.
