# Cleanup report — `XYin/PhD/ModularFunctions/` (worker "mfn", 2026-09-26)

## 1. Final build

`lake build` in SB (both default targets `XYin`, `XYinTest`):

```
✔ [3711/3712] Built XYin (4.7s)
Build completed successfully (3712 jobs).
```

No warnings in any `XYin/PhD/ModularFunctions/*` file (`lake build --no-build | grep ModularFunctions/` → 0).
No `sorry`/`admit`/`axiom`/`native_decide`/`set_option`. Only owned files and one import line in `XYin.lean` changed
(`import XYin.PhD.ModularFunctions.Algebra`). No kernel-computation file touched.

## 2. Files (lines before → after)

| file | before | after | note |
|---|---|---|---|
| Algebra.lean | — | 580 | **new**: field structure on `ModularFunction Γ` (STRETCH, done) |
| MeromorphicField.lean | 658 | 979 | headers merged; +~45 new API lemmas; AddValuation |
| CuspGrowth.lean | 114 | 214 | IsBigO form + closure set; iff proof shortened |
| FieldAction.lean | 149 | 231 | `toFun_precomp`, `precomp_one/mul/symm`, `Algebra ℂ HolomorphicFunction`, `IsDomain` |
| Basic.lean | 97 | 175 | level-one constructors, `toMeromorphicField_eq_iff/_eq_ofMeromorphic` |
| GrowthAtCusp.lean | 73 | 130 | `.slash` in all weights via IsBigO; cusp closure; SL2Z lemmas |
| NormalFormSlash.lean | 97 | 141 | `SL_slash_zero_eq(_iff)`, `inv_slash_zero`, `sl2_det_pos`, `sl2_mdifferentiable` (moved), `slash_eventuallyEq_nhdsNE` |
| Cusps.lean | 88 | 130 | `IsOfExponentialGrowth(At).inv`, `isOfExponentialGrowthAt_of_forall_sl2`, `IsMeromorphicAt.smul_iff` |
| NormalFormGrowth.lean | 66 | 79 | reuses the real predicate; new analyticity lemmas |
| Congruence.lean | 150 | 154 | proofs shortened; `ofGamma0Holomorphic`, `toMeromorphicField_restrict` |
| JInvariant.lean | 57 | 44 | `jModularFunction := ofLevelOneHolomorphic …` |
| CuspPeriod.lean | 62 | 62 | duplicate `open scoped MatrixGroups` removed |
| **total** | 1611 | 2919 | +1308 = new API (≈170 declarations); existing proofs net −60 lines |

## 3. Done items

1. **MeromorphicField.lean hygiene.** Five stacked module docstrings + 5× `open Filter Set Topology` + 5 `variable`
   blocks → one file docstring (main definitions + implementation notes with the ProjectVD provenance) and
   `##` section headers with section-scoped `variable`s. Stale reference to nonexistent
   `eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE` fixed. Root lemma
   `eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE` → `Filter.` namespace (0 external users).
   Authors line now "Stefan Kebekus, The XYin contributors" (the ℍ part is project code). All existing API kept.
2. **AddValuation** promised in the `orderAt_ne_top` docstring built: `orderAtAddValuation` (via `AddValuation.of`,
   import `Mathlib.RingTheory.Valuation.Basic`), docstring now points to it.
3. **Growth predicate** (definition unchanged): `isOfExponentialGrowth_iff_isBigO` + full closure set; manual
   `∃ M A` unpackings removed: CuspGrowth `iff` proof (9 → 3 lines), `IsOfExponentialGrowth.slash` (IsBigO,
   now every weight `k`), NormalFormGrowth (division/continuity argument replaced by a direct bound; statement now
   uses `IsOfExponentialGrowth f` — defeq, 0 external users).
4. **FieldAction**: `sl2_det_pos` replaces 3× `change 0 < …det.val; simp`; `precomp_algebraMap` 9 → 1 line (via
   `precomp_ofMeromorphic`); meromorphy of `f ∘ smulComplex` extracted (used twice).
5. **Congruence**: `conjugate_T_pow_mem_Gamma0` 16 → 6 lines (`Gamma_normal.conj_mem` +
   `ModularGroup_T_pow_mem_Gamma`); `hslash`/`hinv'` fragments → `SL_slash_zero_eq(_iff)`; `ofGamma0CuspData`
   `bdd_at_cusps'` 15 → 4 lines (`isOfExponentialGrowthAt_of_forall_sl2`); redundant `letI : NeZero` removed.
   `periodic_comp_ofComplex_of_vadd` **left private** (orchestrator instruction).
6. **JInvariant**: `jModularFunction` 14 → 3 lines (`ofLevelOneHolomorphic`), `j_periodic` 4 → 1 line; the
   `rintro _ ⟨γ, rfl⟩; exact j_slash_invariant γ` pair is gone; `ModularFunction.j_mdifferentiable` kept (5
   external users) but term-mode; unused `open Complex … Matrix.SpecialLinearGroup` removed.
7. **Injectivity skeleton ×3** → helper `MeromorphicField.injective_of_toFun_eq`;
   `toMeromorphicField_injective` and `holomorphicToMeromorphic_injective` are one-liners; `toFun_injective`
   stays the germ-level base fact.
8. **Constructors**: `ofLevelOneCuspData`, `ofLevelOneHolomorphic` (Basic), `ofGamma0Holomorphic` (Congruence),
   `MDifferentiable.meromorphicNFOn_comp_ofComplex` (MeromorphicField; also used by `ofHolomorphic`).
9. **STRETCH — algebra on `ModularFunction Γ`: done.** `AddCommGroup` (any Γ), `CommRing` (`HasDetPlusMinusOne`),
   `Field` (+ `DiscreteTopology`), `Algebra ℂ` (`HasDetOne`), all transported along `toMeromorphicField`
   (`Function.Injective.addCommGroup/commRing/field`); `toMeromorphicField` as `→+*` and `→ₐ[ℂ]`; the image is the
   subfield `ModularFunction.subfield Γ`. Diamonds checked by `with_reducible_and_instances rfl`
   (`Field.toCommRing`, `toAddCommGroup`); instances resolve for `Γ₀(N)` and `𝒮ℒ`.
   Math: sums/products via normal-form uniqueness (`slash_zero_eq_of_eventuallyEq_codiscrete`) and growth
   transfer near ∞ (`IsOfExponentialGrowthAt.of_eventuallyEq_codiscrete`); inverses are exact
   (`toFun_inv`), growth via periodic cusp charts (`IsOfExponentialGrowthAt.inv`, uses `CuspPeriod.lean`).
10. **Cusps/CuspPeriod** kept; `exponential_growth_at_cusps_iff` term-mode; `IsMeromorphicAt.smul_iff` added.

## 4. New public API (exact statements; `U := upperHalfPlaneSet`, `MF := MeromorphicField`)

### MeromorphicField.lean
- `Filter.eventually_codiscrete_iff_forall_eventually_nhdsNE : (∀ᶠ y in codiscrete X, p y) ↔ ∀ x, ∀ᶠ y in 𝓝[≠] x, p y`
- `MeromorphicNFAt.neg (hf : MeromorphicNFAt f x) : MeromorphicNFAt (-f) x`; `MeromorphicNFOn.neg`
- `MeromorphicOn.GermRing.orderAt_zero (hU : Preperfect U) (hx : x ∈ U) : orderAt (0 : germRing 𝕜 U) x = ⊤` (simp)
- `orderAt_one (hU) (hx) : orderAt 1 x = 0` (simp); `orderAt_algebraMap (hU) (hx) (hc : c ≠ 0) : orderAt (algebraMap 𝕜 _ c) x = 0`
- `orderAt_neg (hU) (hx) a : orderAt (-a) x = orderAt a x`; `orderAt_inv (hU) (hx) a : orderAt a⁻¹ x = -orderAt a x`
- `orderAt_div (hU) (hx) a b : orderAt (a / b) x = orderAt a x - orderAt b x`
- `min_orderAt_le_orderAt_add (hU) (hx) a b : min (orderAt a x) (orderAt b x) ≤ orderAt (a + b) x`
- `orderAtAddValuation (hU : Preperfect U) (hx : x ∈ U) : AddValuation (germRing 𝕜 U) (WithTop ℤ)` + `_apply` (= `orderAt a x`)
- `divisor_zero (hU)`, `divisor_one (hU)`, `divisor_algebraMap (hU) c` : `… = 0` (simp)
- `divisor_div (h₁U : IsPreconnected U) (h₂U : U.Nontrivial) (ha : a ≠ 0) (hb : b ≠ 0) : divisor (a / b) = divisor a - divisor b`
- `UpperHalfPlane.eventually_nhdsNE_comp_ofComplex_iff : (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ w in 𝓝[≠] τ, p w`
- `UpperHalfPlane.eventually_codiscreteWithin_comp_ofComplex_iff : (∀ᶠ z in codiscreteWithin U, p (ofComplex z)) ↔ ∀ᶠ τ in codiscrete ℍ, p τ`
- `UpperHalfPlane.apply_eq_of_eventuallyEq_nhdsNE (hf : MeromorphicNFAt (f ∘ ofComplex) τ) (hg : …) (h : ∀ᶠ w in 𝓝[≠] τ, f w = g w) : f τ = g τ`
- `UpperHalfPlane.eq_of_meromorphicNFOn_of_eventuallyEq (hf : MeromorphicNFOn (f ∘ ofComplex) U) (hg : …) (h : f =ᶠ[codiscrete ℍ] g) : f = g`
- `MDifferentiable.meromorphicNFOn_comp_ofComplex (hf : MDiff f) : MeromorphicNFOn (f ∘ ofComplex) U`
- `MeromorphicField.injective_of_toFun_eq (hf : Injective f) (hF : ∀ a, toFun (F a) = f a) : Injective F`
- `MeromorphicField.coe_ofMeromorphic f hf : ((ofMeromorphic f hf : MF) : Germ _ ℂ) = ((f ∘ ofComplex : ℂ → ℂ) : Germ _ ℂ)` (rfl)
- `ofMeromorphic_eq_iff hf hg : ofMeromorphic f hf = ofMeromorphic g hg ↔ f =ᶠ[codiscrete ℍ] g`; `ofMeromorphic_eq_of_eventuallyEq hf hg h`
- `ofMeromorphic_toFun a : ofMeromorphic (toFun a) (meromorphicNFOn_toFun a).meromorphicOn = a` (simp)
- `toFun_eventuallyEq hf : toFun (ofMeromorphic f hf) =ᶠ[codiscrete ℍ] f`; `eq_iff_toFun_eventuallyEq : a = b ↔ toFun a =ᶠ[codiscrete ℍ] toFun b`
- `ofMeromorphic_zero : ofMeromorphic 0 (MeromorphicOn.const 0) = 0`; `_one`; `ofMeromorphic_const c : ofMeromorphic (fun _ ↦ c) _ = algebraMap ℂ MF c`
- `ofMeromorphic_add hf hg : ofMeromorphic (f + g) (hf.add hg) = ofMeromorphic f hf + ofMeromorphic g hg`; same for `_sub`, `_mul`, `_div`; `ofMeromorphic_neg hf : ofMeromorphic (-f) hf.neg = -ofMeromorphic f hf`; `ofMeromorphic_inv` (all `rfl`)
- `toFun_zero : toFun 0 = 0`, `toFun_one : toFun 1 = 1`, `toFun_algebraMap_complex c : toFun (algebraMap ℂ MF c) = fun _ ↦ c`, `toFun_neg a : toFun (-a) = -toFun a`, `toFun_inv a : toFun a⁻¹ = (toFun a)⁻¹` (all simp, exact)
- `toFun_add_eventuallyEq a b : toFun (a + b) =ᶠ[codiscrete ℍ] toFun a + toFun b`; same `_sub`, `_mul`, `_div`

### CuspGrowth.lean / GrowthAtCusp.lean / NormalFormGrowth.lean
- `isBoundedAtImInfty_exp_mul_iff_isBigO ρ f : IsBoundedAtImInfty (fun τ ↦ (exp (-ρ * τ.im) : ℂ) * f τ) ↔ f =O[atImInfty] fun τ ↦ exp (ρ * τ.im)`
- `isOfExponentialGrowth_iff_isBigO : IsOfExponentialGrowth f ↔ ∃ ρ, 0 ≤ ρ ∧ f =O[atImInfty] fun τ ↦ Real.exp (ρ * τ.im)`
- `exp_mul_im_isBigO_exp_mul_im (h : ρ₁ ≤ ρ₂) : (fun τ : ℍ ↦ exp (ρ₁ * τ.im)) =O[atImInfty] fun τ ↦ exp (ρ₂ * τ.im)`
- `IsOfExponentialGrowth.{of_isBigO_exp, of_isBigO (hf) (h : g =O[atImInfty] f), mono (hf) (h : ∀ᶠ τ in atImInfty, ‖g τ‖ ≤ ‖f τ‖), congr (hf) (h : f =ᶠ[atImInfty] g), of_isBoundedAtImInfty, const c, zero, one, add, neg, sub, mul, smul (c : R) [SeminormedRing R] [Module R ℂ] [IsBoundedSMul R ℂ], const_mul c, pow n}`
- `IsOfExponentialGrowth.slash {k : ℤ} (hf) (hg : g 1 0 = 0) : IsOfExponentialGrowth (f ∣[k] g)` (generalised from weight 0)
- `OnePoint.IsOfExponentialGrowthAt.{add, neg, sub, mul, const_smul a, const a}`
- `OnePoint.isOfExponentialGrowthAt_iff_exists_SL2Z (hc : IsCusp c 𝒮ℒ) : c.IsOfExponentialGrowthAt f ↔ ∃ γ : SL(2,ℤ), mapGL ℝ γ • ∞ = c ∧ IsOfExponentialGrowth (f ∣[(0:ℤ)] γ)`; `_iff_forall_SL2Z`; `isOfExponentialGrowthAt_of_forall_SL2Z (h : ∀ γ : SL(2,ℤ), IsOfExponentialGrowth (f ∣[(0:ℤ)] γ)) (hc : IsCusp c 𝒮ℒ)`
- `eventually_analyticAt_of_eventually_mdifferentiableAt (h : ∀ᶠ τ in atImInfty, MDiffAt f τ) : ∀ᶠ τ : ℍ in atImInfty, AnalyticAt ℂ (f ∘ ofComplex) τ`
- `eventually_analyticAt_of_meromorphicNFOn_of_isOfExponentialGrowth (hf : MeromorphicNFOn (f ∘ ofComplex) U) (hb : IsOfExponentialGrowth f) : ∀ᶠ τ : ℍ in atImInfty, AnalyticAt ℂ (f ∘ ofComplex) τ`

### NormalFormSlash.lean / Cusps.lean
- `ModularForm.SL_slash_zero_eq f γ : f ∣[(0:ℤ)] γ = fun τ ↦ f (γ • τ)`; `SL_slash_zero_eq_iff : f ∣[(0:ℤ)] γ = f ↔ ∀ τ, f (γ • τ) = f τ`
- `ModularForm.inv_slash_zero f g : f⁻¹ ∣[(0:ℤ)] g = (g.det.val ^ 2)⁻¹ • (f ∣[(0:ℤ)] g)⁻¹`
- `UpperHalfPlane.sl2_det_pos δ : 0 < (δ : GL (Fin 2) ℝ).det.val`; `sl2_mdifferentiable` (moved from FieldAction, same statement)
- `UpperHalfPlane.slash_eventuallyEq_nhdsNE k γ (h : ∀ᶠ w in 𝓝[≠] (γ • τ), f w = g w) : ∀ᶠ w in 𝓝[≠] τ, (f ∣[k] γ) w = (g ∣[k] γ) w`
- `IsOfExponentialGrowth.inv (hf) (hNF) (hh : 0 < h) (hper : Periodic (f ∘ ofComplex) h) : IsOfExponentialGrowth f⁻¹`
- `OnePoint.IsOfExponentialGrowthAt.inv [DiscreteTopology Γ] [Γ.HasDetPlusMinusOne] (f : SlashInvariantForm Γ 0) (hf : NF) (hc : IsCusp c Γ) (hg : c.IsOfExponentialGrowthAt f) : c.IsOfExponentialGrowthAt (f : ℍ → ℂ)⁻¹`
- `OnePoint.isOfExponentialGrowthAt_of_forall_sl2 (hh : 0 < h) (hper : ∀ γ : SL(2,ℤ), Periodic ((fun τ ↦ f (γ • τ)) ∘ ofComplex) h) (hcusp : ∀ γ, MeromorphicAt (cuspFunction h (fun τ ↦ f (γ • τ))) 0) (hc : IsCusp c 𝒮ℒ) : c.IsOfExponentialGrowthAt f`
- `OnePoint.IsMeromorphicAt.smul_iff : IsMeromorphicAt (g • c) f ↔ IsMeromorphicAt c (f ∣[(0:ℤ)] g)`

### FieldAction.lean
- `@[ext] HolomorphicFunction.ext (h : ∀ τ, f.1 τ = g.1 τ) : f = g`
- `HolomorphicFunction.constRingHom : ℂ →+* HolomorphicFunction`; `instance : Algebra ℂ HolomorphicFunction`; `HolomorphicFunction.coe_algebraMap c : ((algebraMap ℂ HolomorphicFunction c) : ℍ → ℂ) = fun _ ↦ c` (rfl); `(c • f).1 = fun τ ↦ c * f.1 τ` is `rfl`
- `instance : IsScalarTower ℂ HolomorphicFunction MF`; `instance : IsDomain HolomorphicFunction` (NoZeroDivisors kept)
- `MeromorphicField.algebraMap_eq_ofMeromorphic f : algebraMap HolomorphicFunction MF f = ofMeromorphic f.1 f.2.meromorphicNFOn_comp_ofComplex.meromorphicOn` (rfl)
- `meromorphicOn_comp_sl2_smul (hf : MeromorphicOn (f ∘ ofComplex) U) δ : MeromorphicOn ((fun τ ↦ f (δ • τ)) ∘ ofComplex) U`
- `precomp_ofMeromorphic δ hf : precomp δ (ofMeromorphic f hf) = ofMeromorphic (fun τ ↦ f (δ • τ)) _`
- `toFun_precomp δ a : toFun (precomp δ a) = fun τ ↦ toFun a (δ • τ)` (simp)
- `precomp_one : precomp 1 = RingEquiv.refl MF` (simp); `precomp_mul δ₁ δ₂ : precomp (δ₁ * δ₂) = (precomp δ₁).trans (precomp δ₂)`; `precomp_symm δ : (precomp δ).symm = precomp δ⁻¹`
- `precomp_algebraMap_eq_of_forall δ f g (h : ∀ τ, f.1 (δ • τ) = g.1 τ) : precomp δ (algebraMap _ MF f) = algebraMap _ MF g`

### Basic.lean / Congruence.lean
- `ModularFunction.coe_mk f h₁ h₂ : ⇑(mk f h₁ h₂) = f` (simp)
- `toMeromorphicField_eq_iff : f.toMeromorphicField = a ↔ (f : ℍ → ℂ) = MF.toFun a`; `toMeromorphicField_eq_ofMeromorphic f : f.toMeromorphicField = ofMeromorphic f f.meromorphicOn`
- `UpperHalfPlane.periodic_comp_ofComplex_of_slashInvariant (hinv : ∀ γ : SL(2,ℤ), f ∣[(0:ℤ)] γ = f) : Periodic (f ∘ ofComplex) 1`
- `ModularFunction.ofLevelOneCuspData f (hf : MeromorphicNFOn (f ∘ ofComplex) U) (hinv : ∀ γ : SL(2,ℤ), f ∣[(0:ℤ)] γ = f) (hcusp : MeromorphicAt (cuspFunction 1 f) 0) : ModularFunction 𝒮ℒ` (+ `coe_…` rfl simp)
- `ModularFunction.ofLevelOneHolomorphic f (hf : MDiff f) hinv hcusp : ModularFunction 𝒮ℒ` (+ `coe_…`, `toMeromorphicField_ofLevelOneHolomorphic : … = ofHolomorphic f hf`)
- `ModularFunction.ofGamma0Holomorphic N f (hf : MDiff f) (hinv : ∀ γ : Gamma0 N, f ∣[(0:ℤ)] (γ : SL(2,ℤ)) = f) (hcusp : ∀ γ : SL(2,ℤ), MeromorphicAt (cuspFunction (N:ℝ) (fun τ ↦ f (γ • τ))) 0) : ModularFunction (Gamma0 N)` (+ `coe_…`, `toMeromorphicField_ofGamma0Holomorphic`)
- `toMeromorphicField_restrict f h : (f.restrict h).toMeromorphicField = f.toMeromorphicField` (simp)

### Algebra.lean (new)
- `UpperHalfPlane.slash_eventuallyEq_codiscrete k γ (h : f =ᶠ[codiscrete ℍ] g) : f ∣[k] γ =ᶠ[codiscrete ℍ] g ∣[k] γ`
- `slash_zero_eq_of_eventuallyEq_codiscrete (hf : NF f) (hfg : f =ᶠ[codiscrete ℍ] g) (hg : g ∣[(0:ℤ)] γ = g) : f ∣[(0:ℤ)] γ = f`
- `IsOfExponentialGrowth.of_eventuallyEq_codiscrete (hg : IsOfExponentialGrowth g) (hf : NF f) (hgd : ∀ᶠ τ in atImInfty, MDiffAt g τ) (hfg : f =ᶠ[codiscrete ℍ] g) : IsOfExponentialGrowth f`; cusp version `OnePoint.IsOfExponentialGrowthAt.of_eventuallyEq_codiscrete`, and `.eventually_mdifferentiableAt`
- `MeromorphicField.IsModular Γ a : Prop := (∀ γ ∈ Γ, toFun a ∣[(0:ℤ)] γ = toFun a) ∧ ∀ c, IsCusp c Γ → c.IsOfExponentialGrowthAt (toFun a)`; closure `IsModular.{zero, neg, add, one, mul, inv, algebraMap}` (with the instance hypotheses below)
- `ModularFunction.ofMeromorphicField a (ha : IsModular Γ a) : ModularFunction Γ`; `coe_ofMeromorphicField` (rfl), `toMeromorphicField_ofMeromorphicField`, `ofMeromorphicField_toMeromorphicField`, `isModular_toMeromorphicField`, `isModular_iff_exists : IsModular Γ a ↔ ∃ f : ModularFunction Γ, f.toMeromorphicField = a`
- `ModularFunction.addSubgroup Γ : AddSubgroup MF`; `subring Γ [HasDetPlusMinusOne] : Subring MF`; `subfield Γ [DiscreteTopology Γ] [HasDetPlusMinusOne] : Subfield MF`; `mem_…_iff : a ∈ … ↔ IsModular Γ a`
- **`range_toMeromorphicField : Set.range (toMeromorphicField (Γ := Γ)) = subfield Γ`** (the "modular functions form a subfield" statement for Thm 11.9(ii))
- instances: `Zero Add Neg Sub SMul ℕ SMul ℤ AddCommGroup` (any Γ); `One Mul Pow ℕ NatCast IntCast CommRing` (`[Γ.HasDetPlusMinusOne]`); `Inv Div Pow ℤ NNRatCast RatCast SMul ℚ≥0 SMul ℚ Field` (`[DiscreteTopology Γ] [Γ.HasDetPlusMinusOne]`); `Algebra ℂ` (`[Γ.HasDetOne]`) — all resolve for `Γ₀(N)` and `𝒮ℒ`
- simp: `toMeromorphicField_{zero, add, neg, sub, nsmul, zsmul, one, mul, pow, natCast, intCast, inv, div, zpow, nnratCast, ratCast, nnqsmul, qsmul, algebraMap, smul}`; `coe_zero`, `coe_one`, `coe_neg`, `coe_inv` (exact pointwise), `coe_algebraMap c : ⇑(algebraMap ℂ _ c) = fun _ ↦ c`; `coe_add_eventuallyEq : ⇑(f + g) =ᶠ[codiscrete ℍ] ⇑f + ⇑g`, `coe_mul_eventuallyEq`
- `toMeromorphicFieldRingHom Γ : ModularFunction Γ →+* MF` (+ `_apply`, `_injective`, `range_… = subring Γ`, `fieldRange_… = subfield Γ`); `toMeromorphicFieldAlgHom Γ : ModularFunction Γ →ₐ[ℂ] MF`; `constRingHom : ℂ →+* ModularFunction Γ`
- `precomp_toMeromorphicField f (hδ : (δ : GL (Fin 2) ℝ) ∈ Γ) : precomp δ f.toMeromorphicField = f.toMeromorphicField`

## 5. Kept on purpose (genuine but unused / in-progress)
Valuation/divisor block (`orderAt*`, `divisor*`, `coe_eq_zero_iff`, `out_eventuallyEq`), NeBot lemmas
(`Filter.codiscreteWithin_neBot_iff`, `AccPt/Preperfect/IsPreconnected.codiscreteWithin_neBot`), `isField`,
`isDomain`, `toGermRingHom_surjective`, `coe_div`, `constRingHom_injective`, `algebraMap_eq_constRingHom`,
`toGermRingHom_toNF`, the two `Fact` instances (load-bearing for `instField` on `MeromorphicField`);
`CuspPeriod.lean` (`hasDetPlusMinusOne_conj`, `discreteTopology_conj`, `exists_pos_period_at_cusp` — now used by
`IsOfExponentialGrowthAt.inv`, hence by the `Field` instance), the `Cusps.lean` chain (`IsMeromorphicAt`,
`isOfExponentialGrowthAt_iff_isMeromorphicAt`, `exponential_growth_at_cusps_iff`), `meromorphic_at_cusps`,
`toSlashInvariantForm_coe`, `toFun_algebraMap` (FieldAction), `coe_jModularFunction`, `coe_restrict`,
`coe_ofGamma0CuspData`, `ModularFunction.j_mdifferentiable` (used in 5 Cox places).

## 6. Deferred / follow-ups
Inside the set (skipped, with reason):
- `MulAction`/`MulSemiringAction` of `SL(2,ℤ)` on `MF`: `precomp` is a **right** action
  (`precomp (δ₁*δ₂) = (precomp δ₁).trans (precomp δ₂)`), so an instance must be by `SL(2,ℤ)ᵐᵒᵖ`; left for the
  Galois-theory consumer (diamond-free, `precomp_one/mul` give it in ~8 lines).
- `holomorphicFunctions` stays a `Subring` (Cox depends on it); `Algebra ℂ HolomorphicFunction` added instead
  (checked: no competing `SMul ℂ`/`Algebra` path; Cox builds unchanged).
- `OnePoint.IsMeromorphicAt.infty_iff`/`iff` (chart independence needs a rotation of the cusp parameter) — not cheap.
- Weight-`k` `meromorphicNFOn_slash` (step6 G-15) — not needed here.
- `ModularFunction.meromorphic'` → predicate `MeromorphicNFOn …` (step4 §3.4): changes a structure field used by
  Cox structure literals (Construction.lean:265, LevelJ via `ofGamma0CuspData`) — definition-form change, deferred.
- Naming the 4 anonymous instances in MeromorphicField (step8 #47) — style-only rename, deferred per rules.
- Orchestrator: `ModularFunction.periodic_comp_ofComplex_of_vadd` (Congruence.lean:36) left **private**, to be
  switched to the new root lemma in LaurentQExpansion.lean after merge.

Follow-ups outside the set (exact replacements; the first three were scratch-compiled against this SB):
- `Cox/ModularFunctionField.lean:56–86` `toMeromorphicField_eq_div_of` (31 → 13 lines, **verified**):
  `have hbmap := (map_ne_zero_iff _ holomorphicToMeromorphic_injective).2 hb;
  rw [eq_div_iff hbmap, ← sub_eq_zero, ← mul_eq_zero_iff_right hbmap, f.toMeromorphicField_eq_ofMeromorphic,
  algebraMap_eq_ofMeromorphic, algebraMap_eq_ofMeromorphic, ← ofMeromorphic_mul, ← ofMeromorphic_sub,
  ← ofMeromorphic_mul, ← ofMeromorphic_zero, ofMeromorphic_eq_iff];
  refine Eventually.of_forall fun τ ↦ ?_; by_cases hτ : b.1 τ = 0 · simp [hτ] · simp [hf τ hτ, div_mul_cancel₀ _ hτ]`.
- `Cox/ModularPolynomial/Construction.lean:261–277` (**verified**): `coxPhiFunction_coeff_modularFunction m n :=
  ModularFunction.ofLevelOneHolomorphic _ (coxPhiFunction_coeff_mdifferentiable m n)
  (coxPhiFunction_coeff_slashInvariant m n) (coxPhiFunction_coeff_widthOne_cuspMeromorphicAt m n)`.
- `Cox/ModularPolynomial/AnalyticSupport.lean:83–94` `periodic_comp_of_slashInvariant_one` = (**verified**)
  `UpperHalfPlane.periodic_comp_ofComplex_of_slashInvariant` (delete or make an alias).
- `Cox/ModularFunction/LevelJ.lean:313–319`: `levelJModularFunction N := ModularFunction.ofGamma0Holomorphic N
  (levelJ N) (levelJ_mdifferentiable N) (fun γ ↦ jN_slash_invariant (N : ℕ) γ) (levelJ_meromorphicAt_cusp N)`.
- `Cox/ModularFunctionField.lean:162–169` → `ModularFunction.toMeromorphicField_ofGamma0Holomorphic`;
  `Cox/UpperHalfPlaneFunctionField.lean:48–52` `algebraMap_jElement` → `toMeromorphicField_ofLevelOneHolomorphic`.
- `Cox/ModularFunctionField.lean:120` `modularRepresentatives N` is now `(ModularFunction.subfield (Gamma0 N) : Set _)`
  by `range_toMeromorphicField`; Thm 11.9(ii) can be phrased with `ModularFunction.subfield` / `Field (ModularFunction Γ₀(N))`.
- `Cox/UpperHalfPlaneFunctionField.lean:36–41` `constant` → `algebraMap ℂ HolomorphicFunction`; `evalJ` can become
  `Polynomial.aeval jElement`; `:118–125` `precomp_evalJPoly` and `:252–261` → `precomp_algebraMap_eq_of_forall`.
- `HolomorphicFunction.ext` at UHPFF:122–123, :259–260; Arithmetic.lean:65–66; Interpolation.lean:457–458;
  Irreducibility.lean:35–36. `sl2_det_pos` at Cox/ModularFunction.lean:410, Construction.lean:217,
  Interpolation.lean:84; `sl2_mdifferentiable` now reachable from every file importing `ModularFunctions.Basic`.
- `ModularForm.SL_slash_zero_eq(_iff)` for the `simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one]` idiom at
  Cox/ModularFunction.lean:87/350, CuspData.lean:108/147, Interpolation.lean:258/286, Construction.lean:206,
  LatticeJ.lean:585 (jfunction.lean:78 and jLevelN.lean:88 do not import this folder).

## 7. Perf
No kernel-computation file (`Qj`, `link`, `LevelThree`, `qexp_coeffs`) touched. Full `lake build` ≈ 1:40 as before.
