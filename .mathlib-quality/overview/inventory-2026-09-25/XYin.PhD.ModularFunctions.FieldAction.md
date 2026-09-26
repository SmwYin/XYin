# Inventory: XYin/PhD/ModularFunctions/FieldAction.lean  (149 lines)

Holomorphic functions on ℍ as a subring `holomorphicFunctions` of `ℍ → ℂ`, its embedding `holomorphicToMeromorphic : HolomorphicFunction →+* MeromorphicField` (with `Algebra` and `NoZeroDivisors` consequences), and the action of `SL(2,ℤ)` on `MeromorphicField` by precomposition (`precomp δ : MeromorphicField ≃+* MeromorphicField`), built from `Filter.Germ.compTendsto` after showing the Möbius map preserves the codiscrete filter. Consumed by Cox/UpperHalfPlaneFunctionField.lean and Cox/ModularFunctionField.lean.

## Declarations

### `def UpperHalfPlane.holomorphicFunctions`
- **Type**: `Subring (ℍ → ℂ)`
- **What**: the ring of holomorphic (`MDifferentiable`) functions on ℍ.
- **How**: carrier `{f | MDiff f}`; closure via `mdifferentiable_const`, `MDifferentiable.add/neg/mul`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `HolomorphicFunction`
- **Visibility**: public
- **Lines**: 25–32
- **Notes**: should be a `Subalgebra ℂ (ℍ → ℂ)`: `MDifferentiable.const_smul` exists (`Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:847`), and scratch check confirms `Algebra ℂ HolomorphicFunction` currently FAILS to synthesize. No mathlib subring/subalgebra of `MDifferentiable` functions (searched `Subring|Subalgebra` × `MDifferentiable|ContMDiff` in `Mathlib/Geometry`, `Mathlib/Analysis/Complex`). Used by Cox/UpperHalfPlaneFunctionField.lean.

### `abbrev UpperHalfPlane.HolomorphicFunction`
- **Type**: `Subring (ℍ → ℂ)` (`:= holomorphicFunctions`), used as the type `↥holomorphicFunctions`
- **What**: alias so that `HolomorphicFunction` reads as a type.
- **How**: abbreviation.
- **Hypotheses**: none.
- **Uses from project**: `holomorphicFunctions`
- **Used by**: `holomorphicToMeromorphic`, `toFun_holomorphicToMeromorphic`, `holomorphicToMeromorphic_injective`, `instance Algebra`, `toFun_algebraMap`, `instance NoZeroDivisors`, `precomp_algebraMap`
- **Visibility**: public
- **Lines**: 34–35
- **Notes**: an abbrev of a `Subring` value, not a `Type`; mathlib style would write `↥holomorphicFunctions` or define `abbrev HolomorphicFunction : Type := holomorphicFunctions`. Used by five Cox files.

### `lemma UpperHalfPlane.sl2_mdifferentiable`
- **Type**: `(delta : SL(2, ℤ)) : MDiff (fun tau : ℍ ↦ delta • tau)`
- **What**: the Möbius action of an integral matrix is holomorphic.
- **How**: mathlib `UpperHalfPlane.mdifferentiable_smul` with `det > 0` by `simp`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `precomp_algebraMap`
- **Visibility**: public
- **Lines**: 37–41
- **Notes**: one-line wrapper of `Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean:119`; used by Cox/UpperHalfPlaneFunctionField.lean. ASCII variable names `delta`, `tau` (rest of folder uses `γ`, `τ`).

### `def UpperHalfPlane.MeromorphicField.holomorphicToMeromorphic`
- **Type**: `HolomorphicFunction →+* MeromorphicField`
- **What**: the ring embedding of holomorphic functions into the meromorphic field.
- **How**: `toFun f := ofHolomorphic f f.property`; all homomorphism laws are `rfl` because `ofHolomorphic` unfolds to `toGermRingHom ⟨f ∘ ofComplex, _⟩` and `Germ.coeRingHom` respects operations definitionally.
- **Hypotheses**: none.
- **Uses from project**: `HolomorphicFunction`, `MeromorphicField`, `MeromorphicField.ofHolomorphic`
- **Used by**: `toFun_holomorphicToMeromorphic`, `holomorphicToMeromorphic_injective`, `instance Algebra`, `instance NoZeroDivisors`
- **Visibility**: public
- **Lines**: 45–51
- **Notes**: is `MeromorphicOn.toGermRingHom.comp (restriction of Pi.ringHom (· ∘ ofComplex))`; used by Cox/ModularFunctionField.lean.

### `theorem UpperHalfPlane.MeromorphicField.toFun_holomorphicToMeromorphic`
- **Type**: `(f : HolomorphicFunction) : MeromorphicField.toFun (holomorphicToMeromorphic f) = f`
- **What**: the canonical representative of a holomorphic germ is the function itself.
- **How**: `MeromorphicField.toFun_ofHolomorphic`.
- **Hypotheses**: none.
- **Uses from project**: `holomorphicToMeromorphic`, `MeromorphicField.toFun`, `MeromorphicField.toFun_ofHolomorphic`
- **Used by**: `holomorphicToMeromorphic_injective`, `toFun_algebraMap`
- **Visibility**: public
- **Lines**: 53–57
- **Notes**: `@[simp]`; used by Cox/ModularFunctionField.lean.

### `theorem UpperHalfPlane.MeromorphicField.holomorphicToMeromorphic_injective`
- **Type**: `Function.Injective holomorphicToMeromorphic`
- **What**: the embedding is injective.
- **How**: `Subtype.ext` + `congrArg toFun` + `toFun_holomorphicToMeromorphic`.
- **Hypotheses**: none.
- **Uses from project**: `holomorphicToMeromorphic`, `toFun_holomorphicToMeromorphic`
- **Used by**: `instance NoZeroDivisors`
- **Visibility**: public
- **Lines**: 59–62, proof body ≈ 3 lines
- **Notes**: used by two Cox files; also `RingHom.injective` since the target is a field.

### `instance UpperHalfPlane.MeromorphicField.instAlgebra…` (anonymous `Algebra HolomorphicFunction MeromorphicField`)
- **Type**: `Algebra HolomorphicFunction MeromorphicField`
- **What**: the meromorphic field is an algebra over holomorphic functions.
- **How**: `holomorphicToMeromorphic.toAlgebra`.
- **Hypotheses**: none.
- **Uses from project**: `holomorphicToMeromorphic`, `HolomorphicFunction`, `MeromorphicField`
- **Used by**: `toFun_algebraMap`, `precomp_algebraMap`
- **Visibility**: public
- **Lines**: 64
- **Notes**: `#synth` resolves uniquely; no diamond with the `Algebra ℂ MeromorphicField` instance (different scalar type). No `IsScalarTower ℂ HolomorphicFunction MeromorphicField` can be stated until `Algebra ℂ HolomorphicFunction` exists.

### `theorem UpperHalfPlane.MeromorphicField.toFun_algebraMap`
- **Type**: `(f : HolomorphicFunction) : toFun (algebraMap HolomorphicFunction MeromorphicField f) = f`
- **What**: `algebraMap` form of `toFun_holomorphicToMeromorphic`.
- **How**: same lemma.
- **Hypotheses**: none.
- **Uses from project**: `toFun_holomorphicToMeromorphic`, `instance Algebra`, `MeromorphicField.toFun`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 66–70
- **Notes**: `@[simp]`; unused project-wide.

### `instance UpperHalfPlane.MeromorphicField.instNoZeroDivisors…` (anonymous `NoZeroDivisors HolomorphicFunction`)
- **Type**: `NoZeroDivisors HolomorphicFunction`
- **What**: holomorphic functions on ℍ have no zero divisors (identity theorem, via the field).
- **How**: `Function.Injective.noZeroDivisors` along `holomorphicToMeromorphic`.
- **Hypotheses**: none.
- **Uses from project**: `holomorphicToMeromorphic_injective`, `holomorphicToMeromorphic`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 72–74
- **Notes**: could be the stronger `IsDomain HolomorphicFunction` via `Function.Injective.isDomain` (`Mathlib/Algebra/Ring/Hom/InjSurj.lean:23`); placed in namespace `MeromorphicField` though it is a statement about `HolomorphicFunction`.

### `def UpperHalfPlane.MeromorphicField.smulComplex` (private)
- **Type**: `(delta : SL(2, ℤ)) (z : ℂ) : ℂ := ↑(delta • (ofComplex z : ℍ))`
- **What**: the Möbius map of `δ` as a map `ℂ → ℂ` (junk outside ℍ).
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `smulComplex_tendsto`, `precompGerm`, `precompHom`, `precompHom_inv`, `precomp_algebraMap`
- **Visibility**: private
- **Lines**: 76–77
- **Notes**: —

### `theorem UpperHalfPlane.MeromorphicField.smulComplex_tendsto` (private)
- **Type**: `(delta : SL(2, ℤ)) : Tendsto (smulComplex delta) (codiscreteWithin upperHalfPlaneSet) (codiscreteWithin upperHalfPlaneSet)`
- **What**: the Möbius map pulls codiscrete sets back to codiscrete sets.
- **How**: `eventually_codiscreteWithin_of_forall_eventually_nhdsNE` reduces to punctured neighbourhoods; there the map is a local homeomorphism (`analyticAt_smul`, `deriv_smul_ne_zero`, `HasDerivAt.tendsto_nhdsNE`), and the target set is codiscrete near `δ • z` by `eventually_codiscreteWithin_iff_forall_eventually_nhdsNE`.
- **Hypotheses**: none.
- **Uses from project**: `smulComplex`, `Filter.eventually_codiscreteWithin_of_forall_eventually_nhdsNE`, `Filter.eventually_codiscreteWithin_iff_forall_eventually_nhdsNE`
- **Used by**: `precompGerm`
- **Visibility**: private
- **Lines**: 79–91, proof body ≈ 9 lines
- **Notes**: the general fact "a map that is a local homeomorphism at every point of an open `U` into `U` is `Tendsto` for `codiscreteWithin U`" has no mathlib analogue (searched `tendsto` × `codiscrete` in the decl index; only `Topology.IsEmbedding.image_mem_codiscreteWithin`, `DiscreteSubset.lean:355`). Repeated `(by change 0 < (delta : GL (Fin 2) ℝ).det.val; simp)` at 88, 90, 110.

### `def UpperHalfPlane.MeromorphicField.precompGerm` (private)
- **Type**: `(delta : SL(2, ℤ)) : Germ (codiscreteWithin upperHalfPlaneSet) ℂ →+* Germ (codiscreteWithin upperHalfPlaneSet) ℂ`
- **What**: precomposition by the Möbius map on all codiscrete germs, as a ring hom.
- **How**: `Germ.compTendsto` with `smulComplex_tendsto`; laws by `Germ.inductionOn₂` + `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `smulComplex`, `smulComplex_tendsto`
- **Used by**: `precompHom`, `precompHom_inv`
- **Visibility**: private
- **Lines**: 93–100
- **Notes**: mathlib has `Filter.Germ.compTendsto` (`Mathlib/Order/Filter/Germ/Basic.lean:242`) but no bundled `RingHom`/`AlgHom` version (`Germ.compTendstoRingHom`) — upstream candidate.

### `def UpperHalfPlane.MeromorphicField.precompHom` (private)
- **Type**: `(delta : SL(2, ℤ)) : MeromorphicField →+* MeromorphicField`
- **What**: `precompGerm` restricted to meromorphic germs.
- **How**: representative `f ∘ smulComplex δ` is meromorphic by `MeromorphicAt.comp_analyticAt` with `analyticAt_smul`; laws via `Subtype.ext` and `precompGerm.map_*`.
- **Hypotheses**: none.
- **Uses from project**: `precompGerm`, `smulComplex`, `MeromorphicField`, `MeromorphicOn.mem_germRing_iff`
- **Used by**: `precompHom_inv`, `precomp`
- **Visibility**: private
- **Lines**: 102–116, body ≈ 13 lines
- **Notes**: this is `Subring.map`/`RingHom.restrict` of `precompGerm` to `germRing`; a lemma `MeromorphicOn.germRing.map_le` would remove the manual subtype construction.

### `theorem UpperHalfPlane.MeromorphicField.precompHom_inv` (private)
- **Type**: `(delta : SL(2, ℤ)) (a : MeromorphicField) : precompHom delta⁻¹ (precompHom delta a) = a`
- **What**: precomposition by `δ⁻¹` undoes precomposition by `δ`.
- **How**: on a representative, `Germ.coe_eq` and `filter_upwards [self_mem_codiscreteWithin]`; `simp [smulComplex, ofComplex_apply_of_im_pos]` uses `δ⁻¹ • δ • τ = τ`.
- **Hypotheses**: none.
- **Uses from project**: `precompHom`, `precompGerm`, `smulComplex`, `MeromorphicOn.mem_germRing_iff`
- **Used by**: `precomp`
- **Visibility**: private
- **Lines**: 118–126, proof body ≈ 7 lines
- **Notes**: —

### `def UpperHalfPlane.MeromorphicField.precomp`
- **Type**: `(delta : SL(2, ℤ)) : MeromorphicField ≃+* MeromorphicField`
- **What**: the ring automorphism of the meromorphic field induced by `τ ↦ δ • τ`.
- **How**: `precompHom δ` with inverse `precompHom δ⁻¹`, both inverse laws from `precompHom_inv` (`inv_inv` by `simpa`).
- **Hypotheses**: none.
- **Uses from project**: `precompHom`, `precompHom_inv`, `MeromorphicField`
- **Used by**: `precomp_algebraMap`
- **Visibility**: public
- **Lines**: 128–133
- **Notes**: used by Cox/UpperHalfPlaneFunctionField.lean. Missing: `precomp_one`, `precomp_mul` (a `MonoidHom SL(2,ℤ) →* RingAut MeromorphicField` / `MulDistribMulAction`), `precomp_apply`, and crucially `toFun_precomp` (see NormalFormSlash.md).

### `theorem UpperHalfPlane.MeromorphicField.precomp_algebraMap`
- **Type**: `(delta : SL(2, ℤ)) (f : HolomorphicFunction) : precomp delta (algebraMap HolomorphicFunction MeromorphicField f) = algebraMap … ⟨fun tau ↦ f.1 (delta • tau), f.property.comp (sl2_mdifferentiable delta)⟩`
- **What**: on holomorphic functions, `precomp` is literal precomposition.
- **How**: `Subtype.ext`, `Germ.coe_eq`, `filter_upwards`, `simp [smulComplex]` (uses `ofComplex_apply` on ℍ-points).
- **Hypotheses**: none.
- **Uses from project**: `precomp`, `instance Algebra`, `sl2_mdifferentiable`, `smulComplex`, `HolomorphicFunction`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 135–145, proof body ≈ 5 lines
- **Notes**: `@[simp]`; used by Cox/UpperHalfPlaneFunctionField.lean.

## File Summary
- Total declarations: 16 (7 defs/abbrev, 6 lemmas/theorems, 2 instances, 0 other + 1 abbrev counted in defs)
- Key API (used by 3+ others in the file): `HolomorphicFunction`, `holomorphicToMeromorphic`, `smulComplex`
- Unused declarations (not used by anything in this file): `toFun_algebraMap` (unused project-wide), `instance NoZeroDivisors` (unused project-wide as far as grep shows; instances are implicit), `precomp_algebraMap` (used by Cox)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations
### Mathlib API candidates
- `holomorphicFunctions` (25) → `Subalgebra ℂ (ℍ → ℂ)` using `MDifferentiable.const_smul` (`Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:847`); this unlocks `Algebra ℂ HolomorphicFunction` (currently unsynthesizable) and `IsScalarTower ℂ HolomorphicFunction MeromorphicField`.
- `sl2_mdifferentiable` (37) = `UpperHalfPlane.mdifferentiable_smul` (`Manifold.lean:119`) + `det (mapGL γ) = 1`; one-liner wrapper.
- `precompGerm` (93): bundled `Filter.Germ.compTendsto` (`Germ/Basic.lean:242`) as a ring hom — upstream candidate `Filter.Germ.compTendstoRingHom`.
- `instance NoZeroDivisors` (72): `Function.Injective.noZeroDivisors` (`Mathlib/Algebra/GroupWithZero/InjSurj.lean:54`); `Function.Injective.isDomain` (`Mathlib/Algebra/Ring/Hom/InjSurj.lean:23`) gives `IsDomain` for free.
- `smulComplex_tendsto` (79): candidate general lemma `Filter.Tendsto.codiscreteWithin_of_forall_tendsto_nhdsNE` (local-homeomorphism maps preserve `codiscreteWithin` on open sets).
### Missing API / repeated patterns
- `(by change 0 < (delta : GL (Fin 2) ℝ).det.val; simp)` ×3 (88, 90, 110) and `.analyticAt_smul (g := (delta : GL (Fin 2) ℝ)) …` ×2: add `Matrix.SpecialLinearGroup.det_mapGL_pos`-style lemma or `analyticAt_smul_SL2Z`.
- `precomp` companions: `precomp_one`, `precomp_mul`, `precomp_symm`, `precomp_apply_toFun`/`toFun_precomp` (provable from NormalFormSlash.`meromorphicNFOn_slash_zero` + `eqOn_toNF_of_meromorphicNFOn`), a `MulAction SL(2,ℤ) MeromorphicField` or `SL(2,ℤ) →* MeromorphicField ≃+* MeromorphicField`; `ModularFunction` invariance in field terms (`precomp γ f.toMeromorphicField = f.toMeromorphicField` for `γ ∈ Γ`) — the fixed-field description the Cox files need.
- `ofHolomorphic_add/_mul` are implicitly `rfl` (used at 48–51) but not stated for `MeromorphicField.ofHolomorphic` itself.
### Junk candidates
- `toFun_algebraMap` (66–70): unused project-wide duplicate of `toFun_holomorphicToMeromorphic`.
- ASCII `delta`/`tau` variable names throughout (37–145).
### Moral duplicates within this batch
- `holomorphicToMeromorphic_injective` (59) ~ `MeromorphicField.toFun_injective` (MeromorphicField.lean:626) ~ `ModularFunction.toMeromorphicField_injective` (Basic.lean:72).
- `precompHom`'s meromorphy obligation (106–110) ~ `NormalFormSlash.meromorphicNFOn_slash_zero_of_pos` (54–72) restricted to `SL(2,ℤ)` and weakened to `MeromorphicOn`.
### Generalization notes
- Everything about `precomp` works for any `g ∈ GL₂(ℝ)⁺` (only `det > 0` is used, via `analyticAt_smul`/`deriv_smul_ne_zero`); `SL(2,ℤ)` is a specialisation. With the `J`-trick of NormalFormSlash.lean it extends to all of `GL₂(ℝ)` as a semilinear (conjugate-linear) action.
- `holomorphicFunctions` and `holomorphicToMeromorphic` make sense for any open `U ⊆ ℂ`; nothing uses ℍ beyond `ofComplex`.
