# Inventory: XYin/PhD/Modularforms/DimensionFormulas.lean  (200 lines)

Level-one dimension theory for the project's `Γ(1)`-flavoured modular/cusp forms: the "multiply by Δ / divide by Δ" isomorphism `CuspForm Γ(1) k ≃ₗ ModularForm Γ(1) (k-12)`, identification of the project's eta-product `Delta` with the E₄/E₆ construction `Delta_E4_E6_aux`, and transports of mathlib's `𝒮ℒ` rank results (weights 2/4/6, `rank M_k = 1 + rank S_k`, the full dimension formula) to `Γ(1)`. Contains the project's ONLY remaining `sorry` (`dim_gen_cong_levels`, L198–199: finite-dimensionality of `ModularForm Γ k` for finite-index `Γ ≤ SL(2,ℤ)`). Nothing outside this file uses any of its declarations (only `XYin.lean` imports it).

## Declarations

### `private lemma modularForm_rank_gamma_one`
- **Type**: `(k : ℤ) : Module.rank ℂ (ModularForm Γ(1) k) = Module.rank ℂ (ModularForm 𝒮ℒ k)`
- **What**: The ℂ-rank of weight-k modular forms for `Γ(1)` (coerced into `GL(2,ℝ)`) equals that for mathlib's `𝒮ℒ`.
- **How**: Abstracts over an arbitrary `G : Subgroup (GL (Fin 2) ℝ)` with `[G.HasDetOne]`, `subst`s `G = 𝒮ℒ` using mathlib `CongruenceSubgroup.Gamma_one_coe_eq_SL`, closes by `rfl`; the abstraction keeps the `HasDetOne` instance (needed for the `Module ℂ` structure) in scope during the subst.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: weight_six_one_dimensional, weight_four_one_dimensional, weight_eight_one_dimensional, dim_modforms_eq_one_add_dim_cuspforms, dim_modforms_lvl_one
- **Visibility**: private
- **Lines**: 34–40, proof body ≈ 5 lines
- **Notes**: L33 comment documents the instance-binding trick. This is the transport that every `Γ(1)` statement in the file needs because mathlib states level-one results for `𝒮ℒ`.

### `private lemma cuspForm_rank_gamma_one`
- **Type**: `(k : ℤ) : Module.rank ℂ (CuspForm Γ(1) k) = Module.rank ℂ (CuspForm 𝒮ℒ k)`
- **What**: Same transport as above for cusp forms.
- **How**: Identical `subst`/`rfl` trick via `Gamma_one_coe_eq_SL`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: cuspform_weight_lt_12_zero, dim_modforms_eq_one_add_dim_cuspforms
- **Visibility**: private
- **Lines**: 42–48, proof body ≈ 5 lines
- **Notes**: verbatim copy of the previous proof with `ModularForm` → `CuspForm`.

### `def mul_Delta_map`
- **Type**: `(k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) : ModularForm (CongruenceSubgroup.Gamma 1) k`
- **What**: The map `f ↦ f · Δ` from weight `k-12` modular forms to weight `k` modular forms.
- **How**: `f.mul (ModForm_mk _ 12 Delta)` has weight `(k-12)+12`; `ModularForm.mcast (by ring)` recasts to weight `k`.
- **Hypotheses**: none.
- **Uses from project**: ModForm_mk (IsCuspForm.lean), Delta (Delta.lean:170)
- **Used by**: mul_Delta_map_eq, mul_Delta_map_eq_mul, mul_Delta_IsCuspForm, Modform_mul_Delta', Modform_mul_Delta_apply
- **Visibility**: public
- **Lines**: 50–54, body ≈ 3 lines
- **Notes**: data defined by a tactic block (`have … exact`) rather than a term; no `@[simp]` `_apply` lemma (mul_Delta_map_eq is untagged). Mathlib has the cusp-form-valued version `CuspForm.ofMulDiscriminant` (`Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean:49`).

### `lemma mcast_apply`
- **Type**: `{a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (h : a = b) (f : ModularForm Γ a) (z : ℍ) : (ModularForm.mcast h f) z = f z`
- **What**: Recasting the weight does not change values.
- **How**: `rfl`.
- **Hypotheses**: `a = b`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 56–58, body 1 line
- **Notes**: mathlib's `ModularForm.mcast` carries `@[simps -fullyApplied coe]` (`Mathlib/NumberTheory/ModularForms/Basic.lean:560–562`), which already generates the coercion lemma; this is redundant and unused anywhere in the project.

### `lemma mul_Delta_map_eq`
- **Type**: `(k : ℤ) (f : ModularForm Γ(1) (k - 12)) (z : ℍ) : (mul_Delta_map k f) z = f z * Delta z`
- **What**: Pointwise formula for `mul_Delta_map`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: mul_Delta_map, Delta
- **Used by**: mul_Delta_IsCuspForm, Modform_mul_Delta_apply
- **Visibility**: public
- **Lines**: 60–62, body 1 line
- **Notes**: should be `@[simp]` and named `mul_Delta_map_apply`.

### `lemma mul_Delta_map_eq_mul`
- **Type**: `(k : ℤ) (f : ModularForm Γ(1) (k - 12)) : ((mul_Delta_map k f) : ℍ → ℂ) = (f.mul (ModForm_mk _ 12 Delta))`
- **What**: As functions, `mul_Delta_map k f` is the product form `f.mul Δ`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: mul_Delta_map, ModForm_mk, Delta
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 64–66, body 1 line
- **Notes**: unused anywhere.

### `lemma qExpansion_coe_smul`
- **Type**: `{n : ℕ} [NeZero n] {k : ℤ} (a : ℂ) (f : ModularForm Γ(n) k) : qExpansion n (⇑(a • f)) = qExpansion n (a • ⇑f)`
- **What**: The coercion of a scalar multiple of a modular form is the scalar multiple of the coercion (under `qExpansion`).
- **How**: `rfl`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 68–69, body 1 line
- **Notes**: unused anywhere; mathlib `ModularForm.coe_smul` (`Basic.lean:257`) / `ModularForm.qExpansion_smul` (`QExpansion.lean:556`) cover the real need.

### `lemma qExpansion_coe_smul_cusp`
- **Type**: `{n : ℕ} [NeZero n] {k : ℤ} (a : ℂ) (f : CuspForm Γ(n) k) : qExpansion n (⇑(a • f)) = qExpansion n (a • ⇑f)`
- **What**: Cusp-form version of the previous lemma.
- **How**: `rfl`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 71–72, body 1 line
- **Notes**: unused anywhere.

### `lemma qExpansion_coe_sub`
- **Type**: `{k : ℤ} (f g : ModularForm Γ(1) k) : qExpansion (1 : ℕ) (⇑(f - g)) = qExpansion (1 : ℕ) (⇑f - ⇑g)`
- **What**: Coercion commutes with subtraction under `qExpansion`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 74–75, body 1 line
- **Notes**: unused anywhere; mathlib `ModularForm.coe_sub` (`Basic.lean:307`).

### `lemma mul_Delta_IsCuspForm`
- **Type**: `(k : ℤ) (f : ModularForm Γ(1) (k - 12)) : IsCuspForm (CongruenceSubgroup.Gamma 1) k (mul_Delta_map k f)`
- **What**: `f · Δ` is a cusp form.
- **How**: Unfolds `IsCuspForm` to range membership and exhibits the witness `CuspForm.mcast (by ring) (Delta.mulModularForm f)` (mathlib `CuspForm.mulModularForm`, `Basic.lean:535`), checking pointwise equality with `mul_comm` after `mul_Delta_map_eq`.
- **Hypotheses**: none.
- **Uses from project**: IsCuspForm, CuspForm_to_ModularForm (IsCuspForm.lean), Delta, mul_Delta_map, mul_Delta_map_eq
- **Used by**: Modform_mul_Delta', Modform_mul_Delta_apply
- **Visibility**: public
- **Lines**: 77–82, body ≈ 4 lines
- **Notes**: uses `change` to unfold `IsCuspForm`; mathlib: `CuspForm.isCuspForm_toModularFormₗ (CuspForm.ofMulDiscriminant f)` (`CuspFormSubmodule.lean:86`).

### `def Modform_mul_Delta'`
- **Type**: `(k : ℤ) (f : ModularForm Γ(1) (k - 12)) : CuspForm (CongruenceSubgroup.Gamma 1) k`
- **What**: `f · Δ` packaged as a cusp form.
- **How**: `IsCuspForm_to_CuspForm` (a `Classical.choose`) applied to `mul_Delta_IsCuspForm`.
- **Hypotheses**: none.
- **Uses from project**: IsCuspForm_to_CuspForm (IsCuspForm.lean), mul_Delta_map, mul_Delta_IsCuspForm
- **Used by**: Modform_mul_Delta_apply, CuspForms_iso_Modforms
- **Visibility**: public
- **Lines**: 84–86, body 1 line
- **Notes**: goes through `choose` although the explicit witness `CuspForm.mcast _ (Delta.mulModularForm f)` was just built inside `mul_Delta_IsCuspForm`; defining it directly as that witness (= mathlib `CuspForm.ofMulDiscriminant`, `DimensionFormula.lean:49`) makes `Modform_mul_Delta_apply` a `rfl`. Primed name with no unprimed version.

### `theorem SlashInvariantForm.mul_apply`
- **Type**: `{k₁ k₂ : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k₁) (g : SlashInvariantForm Γ k₂) (z : ℍ) : (f.mul g) z = f z * g z`
- **What**: Pointwise formula for the product of slash-invariant forms.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 88–90, body 1 line
- **Notes**: unused anywhere; declared into mathlib's `SlashInvariantForm` namespace. Mathlib has `SlashInvariantForm.coe_mul` (`Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean:261`) from which this is `congrFun`.

### `lemma Modform_mul_Delta_apply`
- **Type**: `(k : ℤ) (f : ModularForm Γ(1) (k - 12)) (z : ℍ) : (Modform_mul_Delta' k f) z = f z * Delta z`
- **What**: Pointwise formula for `Modform_mul_Delta'`.
- **How**: `CuspForm_to_ModularForm_Fun_coe` (the `choose_spec`, as an equality of `toFun`s) evaluated at `z`, chained with `mul_Delta_map_eq`.
- **Hypotheses**: none.
- **Uses from project**: Modform_mul_Delta', CuspForm_to_ModularForm_Fun_coe (IsCuspForm.lean), mul_Delta_map, mul_Delta_IsCuspForm, mul_Delta_map_eq, Delta
- **Used by**: CuspForms_iso_Modforms
- **Visibility**: public
- **Lines**: 92–96, body ≈ 3 lines
- **Notes**: would be `rfl` if `Modform_mul_Delta'` were defined by its witness.

### `def CuspForms_iso_Modforms`
- **Type**: `(k : ℤ) : CuspForm (CongruenceSubgroup.Gamma 1) k ≃ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)`
- **What**: Division by Δ is a ℂ-linear isomorphism from weight-k cusp forms to weight-(k−12) modular forms, with inverse multiplication by Δ.
- **How**: `toFun := CuspForm_div_Discriminant k`, additivity `CuspForm_div_Discriminant_Add`, `map_smul'` by `mul_div_assoc` after `CuspForm_div_Discriminant_apply`; `invFun := Modform_mul_Delta' k`; the inverse laws are `div_mul_cancel₀` / `mul_div_cancel_right₀` with `Δ_ne_zero`.
- **Hypotheses**: none.
- **Uses from project**: CuspForm_div_Discriminant, CuspForm_div_Discriminant_Add, CuspForm_div_Discriminant_apply, Δ_ne_zero, Delta_apply (all Delta.lean), Modform_mul_Delta', Modform_mul_Delta_apply
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 98–118, body ≈ 20 lines
- **Notes**: unused anywhere. Mathlib now has exactly this: `CuspForm.discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)` (`LevelOne/DimensionFormula.lean:63`, `discriminantEquiv_apply` :92).

### `theorem Delta_E4_eqn`
- **Type**: `Delta = Delta_E4_E6_aux`
- **What**: The project's eta-product cusp form `Delta` coincides with its E₄/E₆ construction `(E₄³ − E₆²)/1728`.
- **How**: Pointwise: `Delta_eq_eta_pow` rewrites `Delta z` as mathlib's `ModularForm.discriminant z`, then mathlib `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq` (`LevelOne/GradedRing.lean:59`); the right side is unfolded through `DirectSum.of` with `ModularForm.directSum_of_pow` (`Basic.lean:647`) and two `change`s, and closed by `ring`.
- **Hypotheses**: none.
- **Uses from project**: Delta (Delta.lean:170), Delta_E4_E6_aux (Eisenstein.lean:326), Delta_eq_eta_pow (Delta.lean:36); the project's `E₄`, `E₆` (mathlib's are hidden by `open ModularForm hiding E₄ E₆`, L24)
- **Used by**: delta_eq_E4E6_const, Delta_E4_E6_aux_q_one_term
- **Visibility**: public
- **Lines**: 120–129, body ≈ 9 lines
- **Notes**: two `change`s unfold definitions by defeq — brittle; relies on the project's `E₄`/`E₆` being defeq to mathlib's.

### `lemma delta_eq_E4E6_const`
- **Type**: `∃ (c : ℂ), (c • Delta) = Delta_E4_E6_aux`
- **What**: `Delta_E4_E6_aux` is a scalar multiple of `Delta`.
- **How**: `c = 1` via `Delta_E4_eqn`.
- **Hypotheses**: none.
- **Uses from project**: Delta, Delta_E4_E6_aux, Delta_E4_eqn
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 131–132, body 1 line
- **Notes**: unused anywhere; strictly weaker than `Delta_E4_eqn` — junk.

### `lemma cuspform_weight_lt_12_zero`
- **Type**: `(k : ℤ) (hk : k < 12) : Module.rank ℂ (CuspForm Γ(1) k) = 0`
- **What**: There are no nonzero cusp forms of weight < 12 for `Γ(1)`.
- **How**: Transport `cuspForm_rank_gamma_one` then mathlib `CuspForm.rank_eq_zero_of_weight_lt_twelve` (`LevelOne/DimensionFormula.lean:154`).
- **Hypotheses**: `k < 12`.
- **Uses from project**: cuspForm_rank_gamma_one
- **Used by**: IsCuspForm_weight_lt_eq_zero
- **Visibility**: public
- **Lines**: 134–135, body 1 line
- **Notes**: none.

### `lemma IsCuspForm_weight_lt_eq_zero`
- **Type**: `(k : ℤ) (hk : k < 12) (f : ModularForm Γ(1) k) (hf : IsCuspForm Γ(1) k f) : f = 0`
- **What**: A weight-<12 modular form for `Γ(1)` that is a cusp form is zero.
- **How**: `hf` gives `g` with `f = CuspForm_to_ModularForm g`; `g = 0` by `rank_zero_iff_forall_zero` and `cuspform_weight_lt_12_zero`; `map_zero`.
- **Hypotheses**: `k < 12`, `f` cusp form.
- **Uses from project**: IsCuspForm, CuspForm_to_ModularForm (IsCuspForm.lean), cuspform_weight_lt_12_zero
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 137–141, body ≈ 3 lines
- **Notes**: unused anywhere; uses `change` to unfold `IsCuspForm`.

### `lemma Delta_E4_E6_eq`
- **Type**: `ModForm_mk _ _ Delta_E4_E6_aux = ((1/ 1728 : ℂ) • (((DirectSum.of _ 4 E₄)^3 - (DirectSum.of _ 6 E₆)^2) 12 ))`
- **What**: Unfolds the definition of `Delta_E4_E6_aux` (as a modular form) to its graded-ring expression.
- **How**: `ext; rfl`.
- **Hypotheses**: none.
- **Uses from project**: ModForm_mk (IsCuspForm.lean), Delta_E4_E6_aux, project `E₄`/`E₆`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 143–146, body 2 lines
- **Notes**: unused anywhere; a definitional-unfolding lemma — junk.

### `lemma Delta_E4_E6_aux_q_one_term`
- **Type**: `(qExpansion 1 Delta_E4_E6_aux).coeff 1 = 1`
- **What**: The q¹-coefficient of `(E₄³ − E₆²)/1728` is 1.
- **How**: Rewrite with `← Delta_E4_eqn` and use the project's `Delta_q_one_term`.
- **Hypotheses**: none.
- **Uses from project**: Delta_E4_E6_aux, Delta_E4_eqn, Delta_q_one_term (Eisenstein.lean:374)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 148–150, body 2 lines
- **Notes**: unused anywhere; mathlib `ModularForm.discriminant_qExpansion_coeff_one` (`Discriminant.lean:210`).

### `lemma weight_six_one_dimensional`
- **Type**: `Module.rank ℂ (ModularForm Γ(1) 6) = 1`
- **What**: `M₆(Γ(1))` is one-dimensional.
- **How**: transport + mathlib `ModularForm.levelOne_weight_six_rank_one` (`LevelOne/DimensionFormula.lean:198`).
- **Hypotheses**: none.
- **Uses from project**: modularForm_rank_gamma_one
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 152–153, body 1 line
- **Notes**: unused anywhere.

### `lemma weight_four_one_dimensional`
- **Type**: `Module.rank ℂ (ModularForm Γ(1) 4) = 1`
- **What**: `M₄(Γ(1))` is one-dimensional.
- **How**: transport + `ModularForm.levelOne_weight_four_rank_one` (`LevelOne/DimensionFormula.lean:193`).
- **Hypotheses**: none.
- **Uses from project**: modularForm_rank_gamma_one
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 155–156, body 1 line
- **Notes**: unused anywhere.

### `lemma weight_eight_one_dimensional`
- **Type**: `(k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (hk3 : k < 12) : Module.rank ℂ (ModularForm Γ(1) k) = 1`
- **What**: For even `4 ≤ k < 12` (i.e. k ∈ {4,6,8,10}) `M_k(Γ(1))` is one-dimensional.
- **How**: transport + mathlib `ModularForm.dimension_level_one` (`LevelOne/DimensionFormula.lean:249`), `k ≢ 2 [MOD 12]` by `omega`, `Nat.div_eq_of_lt`.
- **Hypotheses**: `3 ≤ k`, `k` even, `k < 12`.
- **Uses from project**: modularForm_rank_gamma_one
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 158–162, body ≈ 3 lines
- **Notes**: unused anywhere; misnamed (not specific to weight 8); subsumes `weight_four/six_one_dimensional`.

### `lemma weight_two_zero`
- **Type**: `(f : ModularForm (CongruenceSubgroup.Gamma 1) 2) : f = 0`
- **What**: There are no nonzero weight-2 modular forms for `Γ(1)`.
- **How**: `rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero` (`LevelOne/DimensionFormula.lean:244`), then `rw [← Gamma_one_coe_eq_SL] at h` to transport the ∀-statement (a different transport than the rank lemmas).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: dim_weight_two
- **Visibility**: public
- **Lines**: 164–167, body 3 lines
- **Notes**: header docstring (L18–19) advertises this as the file's weight-two vanishing result.

### `lemma dim_modforms_eq_one_add_dim_cuspforms`
- **Type**: `(k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) : Module.rank ℂ (ModularForm Γ(1) k) = 1 + Module.rank ℂ (CuspForm Γ(1) k)`
- **What**: `dim M_k = 1 + dim S_k` for even `k ≥ 4`, level one.
- **How**: both transports + mathlib `ModularForm.rank_eq_one_add_rank_cuspForm` (`LevelOne/DimensionFormula.lean:170`).
- **Hypotheses**: `3 ≤ k`, `k` even.
- **Uses from project**: modularForm_rank_gamma_one, cuspForm_rank_gamma_one
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 169–173, body 2 lines
- **Notes**: unused anywhere.

### `theorem dim_weight_two`
- **Type**: `Module.rank ℂ (ModularForm Γ(1) ↑2) = 0`
- **What**: `M₂(Γ(1)) = 0` as a rank statement.
- **How**: `rank_zero_iff_forall_zero.mpr weight_two_zero`.
- **Hypotheses**: none.
- **Uses from project**: weight_two_zero
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 175–176, body 1 line
- **Notes**: unused anywhere; the weight is written `↑2` (ℕ-cast) unlike the rest of the file; direct transport of `levelOne_weight_two_rank_zero` would be shorter.

### `lemma floor_lem1`
- **Type**: `(k a : ℚ) (ha : 0 < a) (hak : a ≤ k) : 1 + Nat.floor ((k - a) / a) = Nat.floor (k / a)`
- **What**: Floor identity `1 + ⌊(k−a)/a⌋ = ⌊k/a⌋` for `0 < a ≤ k`.
- **How**: `div_sub_same`, `Nat.floor_sub_one`, `Nat.le_floor` with `le_div_iff₀`.
- **Hypotheses**: `0 < a ≤ k`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 178–181, body 2 lines
- **Notes**: unused anywhere; stated over ℚ but only uses `LinearOrderedField` + `FloorSemiring` lemmas.

### `lemma dim_modforms_lvl_one`
- **Type**: `(k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) : Module.rank ℂ (ModularForm Γ(1) k) = if 12 ∣ ((k) : ℤ) - 2 then Nat.floor ((k : ℚ)/ 12) else Nat.floor ((k : ℚ) / 12) + 1`
- **What**: The level-one dimension formula in the textbook `⌊k/12⌋` form.
- **How**: transport + `ModularForm.dimension_level_one` (`LevelOne/DimensionFormula.lean:249`), converting `k ≡ 2 [MOD 12]` to `12 ∣ k − 2` by `omega` and `⌊(k:ℚ)/12⌋₊ = k / 12` by `Nat.floor_div_eq_div` (`Mathlib/Algebra/Order/Floor/Semifield.lean:47`).
- **Hypotheses**: `3 ≤ k` (unused by the proof — mathlib's formula needs only `Even k`), `k` even.
- **Uses from project**: modularForm_rank_gamma_one
- **Used by**: ModularForm.dimension_level_one_XYin
- **Visibility**: public
- **Lines**: 183–191, body ≈ 6 lines
- **Notes**: the `hk` hypothesis is dead weight.

### `lemma ModularForm.dimension_level_one_XYin`
- **Type**: identical to `dim_modforms_lvl_one`
- **What**: Verbatim restatement of `dim_modforms_lvl_one` under a mathlib-style name.
- **How**: `apply dim_modforms_lvl_one k hk hk2`.
- **Hypotheses**: as above.
- **Uses from project**: dim_modforms_lvl_one
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 193–196, body 1 line
- **Notes**: unused anywhere; exact duplicate of the previous lemma.

### `lemma dim_gen_cong_levels`
- **Type**: `(k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) : FiniteDimensional ℂ (ModularForm Γ k)`
- **What**: Modular forms of any weight for a finite-index subgroup of `SL(2,ℤ)` form a finite-dimensional ℂ-space.
- **How**: **sorry**. Trailing comment L200: "use the norm to turn it into a level one question."
- **Hypotheses**: `Γ` has finite index in `SL(2,ℤ)`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 198–199
- **Notes**: **the project's only sorry**. Unused anywhere. See Observations for what mathlib provides and what is missing.

## File Summary
- Total declarations: 30 (3 defs: mul_Delta_map, Modform_mul_Delta', CuspForms_iso_Modforms; 27 lemmas/theorems; 0 instances; 0 other)
- Key API (used by 3+ others in the file): modularForm_rank_gamma_one (5), mul_Delta_map (5)
- Unused declarations (not used by anything in this file): mcast_apply, mul_Delta_map_eq_mul, qExpansion_coe_smul, qExpansion_coe_smul_cusp, qExpansion_coe_sub, SlashInvariantForm.mul_apply, CuspForms_iso_Modforms, delta_eq_E4E6_const, IsCuspForm_weight_lt_eq_zero, Delta_E4_E6_eq, Delta_E4_E6_aux_q_one_term, weight_six_one_dimensional, weight_four_one_dimensional, weight_eight_one_dimensional, dim_modforms_eq_one_add_dim_cuspforms, dim_weight_two, floor_lem1, ModularForm.dimension_level_one_XYin, dim_gen_cong_levels — and NONE of the 28 public declarations is referenced by any other project file (grep -rlw over XYin).
- Declarations with sorry: dim_gen_cong_levels (L198–199)
- Declarations with set_option: none
- Proofs >30 lines: none (longest: CuspForms_iso_Modforms, 20 lines)

## Observations

### Mathlib API candidates
- **Whole-file redundancy with `Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`** (pinned mathlib): `CuspForms_iso_Modforms` = `CuspForm.discriminantEquiv` (:63); `mul_Delta_map`/`Modform_mul_Delta'` = `CuspForm.ofMulDiscriminant` (:49, `ofMulDiscriminant_apply` :54); `cuspform_weight_lt_12_zero` = `CuspForm.rank_eq_zero_of_weight_lt_twelve` (:154); `weight_four/six_one_dimensional` = `levelOne_weight_four/six_rank_one` (:193/:198); `weight_two_zero`/`dim_weight_two` = `levelOne_weight_two_rank_zero` (:244); `dim_modforms_eq_one_add_dim_cuspforms` = `rank_eq_one_add_rank_cuspForm` (:170); `dim_modforms_lvl_one`/`dimension_level_one_XYin`/`weight_eight_one_dimensional` = `dimension_level_one` (:249); `Delta_E4_E6_aux_q_one_term` = `discriminant_qExpansion_coeff_one` (`Discriminant.lean:210`). Also `FiniteDimensional ℂ (ModularForm 𝒮ℒ k)` instance for every `k : ℤ` at :273, and `sturm_bound_levelOne` (:306). Everything here is a `Γ(1)`-transport of one of these.
- **The `Γ(1)` vs `𝒮ℒ` friction is real, not cosmetic**: a scratch check (`lake env lean`, this session) of `ModularForm.isCuspForm_iff_coeffZero_eq_zero f` for `f : ModularForm Γ(1) k` fails with a deterministic `isDefEq` heartbeat timeout — mathlib's `𝒮ℒ` lemmas do not unify against the coerced `Γ(1)` without an explicit `Gamma_one_coe_eq_SL` transport (L34–48, L166). Restating the project's level-one API over `𝒮ℒ` (as mathlib does) removes both private transport lemmas and lets every result above become a direct mathlib citation.
- `mcast_apply` (L56): generated already by `@[simps -fullyApplied coe]` on `ModularForm.mcast` (`Basic.lean:560`).
- `SlashInvariantForm.mul_apply` (L88): `congrFun (SlashInvariantForm.coe_mul f g) z` (`SlashInvariantForms.lean:261`).
- `floor_lem1` (L178): no mathlib analogue found (searched `Nat.floor_sub_one`, `floor_div`, `floor_sub_div`); unused anyway.
- **The remaining sorry `dim_gen_cong_levels` (L198)** — what mathlib has and what is missing:
  - Has: `FiniteDimensional ℂ (ModularForm 𝒮ℒ k)` (`LevelOne/DimensionFormula.lean:273`) for level one ONLY; `grep FiniteDimensional|Module.Finite` over `Mathlib/NumberTheory/ModularForms/` finds nothing for general `Γ`. So the statement is a genuine gap, not a lookup.
  - Has the "norm" machinery the trailing comment refers to: `SlashInvariantForm.norm` / `ModularForm.norm ℋ f : ModularForm ℋ (k * Nat.card (ℋ ⧸ 𝒢.subgroupOf ℋ))` (`Mathlib/NumberTheory/ModularForms/NormTrace.lean:62, :98`) with `ModularForm.norm_eq_zero_iff` (:129) and `ModularForm.trace` (:70); these need `[𝒢.IsFiniteRelIndex ℋ]`, which follows from `[Γ.IsArithmetic]`, which for `Γ : Subgroup SL(2,ℤ)` is `Γ.FiniteIndex` (`ArithmeticSubgroups.lean:93 isArithmetic_iff_finiteIndex`, instance :100); the hypothesis `Subgroup.index Γ ≠ 0` is exactly `Γ.FiniteIndex` via `Subgroup.finiteIndex_iff` (`Mathlib/GroupTheory/Index.lean:680`). Suggest restating with `[Γ.FiniteIndex]`.
  - A viable route with current mathlib: (i) Sturm bound for `Γ` via the norm — if `f ∈ M_k(Γ)` has q-expansion order `> k·d/12` (d = index) at every coset translate `f ∣[k] γ⁻¹`, then `ModularForm.norm 𝒮ℒ f` (weight `k·d`) has order `> k·d/12` (needs `ModularForm.qExpansion_mul` `QExpansion.lean:584` iterated over the finite product and `PowerSeries.order_mul` in the domain `ℂ⟦X⟧`), hence vanishes by `sturm_bound_levelOne` (:306), hence `f = 0` by `norm_eq_zero_iff`; (ii) the ℂ-linear map `f ↦ (first ⌊k·d/12⌋+1 q-coefficients of each of the d translates)` into a finite product of `ℂ`s is therefore injective, giving `FiniteDimensional` by `LinearMap.finiteDimensional_of_injective`. Step (i) needs periodicity of each translate with a period in `strictPeriods` (`Cusps.lean:452 strictPeriods_Gamma` for congruence Γ; for a general finite-index Γ use the width from `strictWidthInfty_pos_iff`), which is the main remaining work. Nothing in the project currently builds toward this.

### Missing API / repeated patterns
- The transport `Γ(1) → 𝒮ℒ` is done three different ways (subst trick L34–40 & L42–48; `rw [← Gamma_one_coe_eq_SL] at h` L166): one lemma `ModularForm.rank_Gamma_one_eq_rank_SL`/a `≃ₗ` between `ModularForm Γ(1) k` and `ModularForm 𝒮ℒ k` (or simply restating over `𝒮ℒ`) collapses all of it.
- `mul_Delta_map` lacks a `@[simp]` `_apply` lemma (`mul_Delta_map_eq` is untagged and named like an equation, not an `_apply`).
- `Modform_mul_Delta'` should be defined by the explicit witness (L80) rather than by `Classical.choose`; then `Modform_mul_Delta_apply` is `rfl`.

### Junk candidates
- Unused anywhere (in-file and project-wide): mcast_apply (L56), mul_Delta_map_eq_mul (L64), qExpansion_coe_smul/_cusp/qExpansion_coe_sub (L68–75), SlashInvariantForm.mul_apply (L88), delta_eq_E4E6_const (L131), IsCuspForm_weight_lt_eq_zero (L137), Delta_E4_E6_eq (L143), Delta_E4_E6_aux_q_one_term (L148), weight_six/four/eight_one_dimensional (L152–162), dim_modforms_eq_one_add_dim_cuspforms (L169), dim_weight_two (L175), floor_lem1 (L178), ModularForm.dimension_level_one_XYin (L193).
- Since NO declaration of this file is consumed by any other file and every proved statement is a transport of a pinned-mathlib theorem, the whole file (minus the sorry) is a candidate for deletion once callers (none) are checked; the sorry should move to a dedicated `ForMathlib` file stated over `[Γ.FiniteIndex]`.
- Imports `Mathlib.Data.Rat.Star` and `Mathlib.LinearAlgebra.Dimension.Localization` (L9–10) look unrelated to the content.

### Moral duplicates within this batch
- `dim_modforms_lvl_one` (L183) ≡ `ModularForm.dimension_level_one_XYin` (L193): literally the same statement, the second `apply`s the first.
- `weight_four_one_dimensional` (L155) and `weight_six_one_dimensional` (L152) are instances of `weight_eight_one_dimensional` (L158).
- `weight_two_zero` (L164) ≡ `dim_weight_two` (L175) (∀-form vs rank-form of the same fact).
- `modularForm_rank_gamma_one` (L34) / `cuspForm_rank_gamma_one` (L42): same proof skeleton.
- Across files: `CuspForms_iso_Modforms` (L98) vs mathlib `CuspForm.discriminantEquiv`; `Delta_E4_eqn` (L120) restates mathlib `discriminant_eq_E₄_cube_sub_E₆_sq` for the project's `Delta` — and the project's `Delta` (Delta.lean:170) is itself a twin of mathlib `CuspForm.discriminant` (`Discriminant.lean:235`, `coe_discriminant` :253).

### Generalization notes
- `floor_lem1`: stated over ℚ; proof uses only `div_sub_same`, `Nat.floor_sub_one`, `le_div_iff₀`, `Nat.le_floor` — valid in any `LinearOrderedField` with `FloorSemiring`.
- `dim_modforms_lvl_one` / `dimension_level_one_XYin`: hypothesis `3 ≤ k` is unused (mathlib's `dimension_level_one` needs only `Even k`).
- `dim_gen_cong_levels`: `Subgroup.index Γ ≠ 0` should be the typeclass `[Γ.FiniteIndex]` (or `[Γ.IsArithmetic]`) so that mathlib's norm/trace instances fire.
