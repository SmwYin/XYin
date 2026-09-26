# Inventory: XYin/PhD/Cox/UpperHalfPlaneFunctionField.lean  (264 lines)

Realizes `ℂ(Y)` (as `RatFunc ℂ`) inside the codiscrete meromorphic field `FunctionField := MeromorphicField` by `Y ↦ j` (through the holomorphic subring `HolomorphicFunction`), installs the resulting `Algebra (RatFunc ℂ) FunctionField`, upgrades `SL₂(ℤ)`-precomposition to a `ℂ(Y)`-algebra automorphism, and proves that the right-coset conjugates `j(mγτ)` are pairwise distinct elements of the field (via injectivity of the Cox-matrix Laurent expansion). This is the algebraic substrate for irreducibility of `Φ_m` (Irreducibility.lean) and the symmetry argument (Arithmetic.lean).

## Declarations

### `abbrev Cox.UpperHalfPlaneFunctionField.FunctionField`
- **Type**: `abbrev FunctionField := MeromorphicField`
- **What**: Local name for the ambient field of meromorphic germs on ℍ (`MeromorphicOn.germRing ℂ upperHalfPlaneSet`).
- **How**: abbreviation; since the 2026-09-21 migration there is no separate `FractionRing HolomorphicFunction` model.
- **Hypotheses**: none.
- **Uses from project**: `UpperHalfPlane.MeromorphicField` (MeromorphicField.lean:592)
- **Used by**: `algebraMap_jElement`, `evalJFracPoly`, `ratFuncEvalJ`, `instance Algebra`, `algebraMap_ratFunc`, `precomp_evalJPoly`, `precomp_ratFunc`, `precompAlgEquiv`, `rightCosetRoot`, `precompAlgEquiv_rightCosetRoot`
- **Visibility**: public
- **Lines**: 34
- **Notes**: Pure alias. External: Arithmetic.lean:80–97, Irreducibility.lean:50–77, ModularFunctionField.lean throughout. Redundant with `MeromorphicField` after migration; retained only as a Cox-namespace name.

### `private def Cox.UpperHalfPlaneFunctionField.constant`
- **Type**: `ℂ →+* HolomorphicFunction`
- **What**: Constant functions as holomorphic functions, as a ring hom.
- **How**: `⟨fun _ ↦ z, mdifferentiable_const⟩`, all axioms `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `HolomorphicFunction` (FieldAction.lean:35)
- **Used by**: `evalJ`, `evalJ_apply`
- **Visibility**: private
- **Lines**: 36–41
- **Notes**: Exists only because `holomorphicFunctions` is a `Subring (ℍ → ℂ)` (FieldAction.lean:26), not a `Subalgebra ℂ (ℍ → ℂ)`; with the latter this is `algebraMap ℂ HolomorphicFunction`.

### `def Cox.UpperHalfPlaneFunctionField.jElement`
- **Type**: `HolomorphicFunction := ⟨j, ModularFunction.j_mdifferentiable⟩`
- **What**: `j` as an element of the holomorphic subring.
- **How**: subtype constructor.
- **Hypotheses**: none.
- **Uses from project**: `HolomorphicFunction`, `j`, `ModularFunction.j_mdifferentiable`
- **Used by**: `algebraMap_jElement`, `evalJ`
- **Visibility**: public
- **Lines**: 44
- **Notes**: No external use.

### `@[simp] theorem Cox.UpperHalfPlaneFunctionField.algebraMap_jElement`
- **Type**: `algebraMap HolomorphicFunction FunctionField jElement = jModularFunction.toMeromorphicField`
- **What**: The holomorphic embedding of `j` is the field element of the bundled `jModularFunction`.
- **How**: `MeromorphicField.toFun_injective` then `simp [jElement]` (`toFun_algebraMap`, `toFun_toMeromorphicField`, `coe_jModularFunction`).
- **Hypotheses**: none.
- **Uses from project**: `jElement`, `FunctionField`, `jModularFunction`, `ModularFunction.toMeromorphicField`, `MeromorphicField.toFun_injective`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 48–52, proof body ≈ 2 lines
- **Notes**: Unused anywhere in the project. The `toFun_injective`-then-`simp` skeleton recurs at ModularFunctionField.lean:66–69 and 164–169.

### `def Cox.UpperHalfPlaneFunctionField.evalJ`
- **Type**: `Polynomial ℂ →+* HolomorphicFunction := Polynomial.eval₂RingHom constant jElement`
- **What**: `P ↦ P(j)` as a ring hom into holomorphic functions.
- **How**: mathlib `Polynomial.eval₂RingHom` (`Mathlib/Algebra/Polynomial/Eval/Defs.lean:213`).
- **Hypotheses**: none.
- **Uses from project**: `constant`, `jElement`, `HolomorphicFunction`
- **Used by**: `evalJ_apply`, `evalJ_injective`, `evalJFracPoly`, `precomp_evalJPoly`
- **Visibility**: public
- **Lines**: 55–56
- **Notes**: Load-bearing externally: Arithmetic.lean:64–91, Interpolation.lean:447–459, Irreducibility.lean:29, 56, ModularFunctionField.lean:33, 41, 107–110. With a `Subalgebra` this is `Polynomial.aeval jElement` (an `AlgHom`), which would give `Polynomial.aeval_def`, `aeval_X`, `aeval_C` for free and make `Cox.polynomialIn P j = (evalJ P).1` a rfl-lemma.

### `def Cox.UpperHalfPlaneFunctionField.evaluation`
- **Type**: `(tau : ℍ) : HolomorphicFunction →+* ℂ := (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) tau).comp holomorphicFunctions.subtype`
- **What**: Evaluation of a holomorphic function at a point, as a ring hom.
- **How**: mathlib `Pi.evalRingHom` (`Mathlib/Algebra/Ring/Pi.lean:158`) composed with `Subring.subtype`.
- **Hypotheses**: none.
- **Uses from project**: `holomorphicFunctions`
- **Used by**: `evalJ_apply`
- **Visibility**: public
- **Lines**: 59–60
- **Notes**: External: Arithmetic.lean:67–73, Irreducibility.lean:40, ModularFunctionField.lean:39–41. Missing companion `evaluation_comp_evalJ : (evaluation τ).comp evalJ = Polynomial.evalRingHom (j τ)` — proved inline at ModularFunctionField.lean:41–42 and Arithmetic.lean:69–72.

### `@[simp] theorem Cox.UpperHalfPlaneFunctionField.evalJ_apply`
- **Type**: `(P : Polynomial ℂ) (tau : ℍ) : (evalJ P).1 tau = P.eval (j tau)`
- **What**: Pointwise, `evalJ P` is `P(j τ)`.
- **How**: View the LHS as `evaluation τ (eval₂ constant jElement P)`, push through with `Polynomial.hom_eval₂` (`Mathlib/Algebra/Polynomial/Eval/Coeff.lean:172`), note `(evaluation τ).comp constant = RingHom.id ℂ` by `rfl`, finish with `Polynomial.eval₂_at_apply`.
- **Hypotheses**: none.
- **Uses from project**: `evalJ`, `evaluation`, `constant`, `jElement`, `j`
- **Used by**: `evalJ_injective`, `precomp_evalJPoly`
- **Visibility**: public
- **Lines**: 63–73, proof body ≈ 9 lines
- **Notes**: External: Arithmetic.lean:72, Interpolation.lean:460, Irreducibility.lean:39, ModularFunctionField.lean:42, 111. With `aeval` this is `Polynomial.aeval_fn_apply`-style (`Mathlib/Algebra/Polynomial/AlgebraMap.lean:480`) plus `Subtype` coercion.

### `theorem Cox.UpperHalfPlaneFunctionField.evalJ_injective`
- **Type**: `Function.Injective evalJ`
- **What**: Distinct polynomials give distinct functions of `j`.
- **How**: `Polynomial.funext` (`Mathlib/Algebra/Polynomial/Roots.lean:452`, needs `Infinite ℂ`) and surjectivity of `j` (`j_surjective`).
- **Hypotheses**: none.
- **Uses from project**: `evalJ`, `evalJ_apply`, `j_surjective` (LatticeJ.lean:626)
- **Used by**: `evalJFracPoly_injective`
- **Visibility**: public
- **Lines**: 76–84, proof body ≈ 8 lines
- **Notes**: External: Interpolation.lean:450, ModularFunctionField.lean:109. This is why `LatticeJ` (the surjectivity of `j`) is a dependency of the whole field layer.

### `def Cox.UpperHalfPlaneFunctionField.evalJFracPoly`
- **Type**: `Polynomial ℂ →+* FunctionField := (algebraMap HolomorphicFunction FunctionField).comp evalJ`
- **What**: `P ↦ P(j)` landing in the meromorphic field.
- **How**: composition.
- **Hypotheses**: none.
- **Uses from project**: `FunctionField`, `HolomorphicFunction`, `evalJ` (and the `Algebra HolomorphicFunction MeromorphicField` instance, FieldAction.lean:64)
- **Used by**: `evalJFracPoly_injective`, `ratFuncEvalJ`, `ratFuncEvalJ_injective`, `ratFuncEvalJ_algebraMap`, `precomp_evalJPoly`
- **Visibility**: public
- **Lines**: 87–88
- **Notes**: External: ModularFunctionField.lean:140 only.

### `theorem Cox.UpperHalfPlaneFunctionField.evalJFracPoly_injective`
- **Type**: `Function.Injective evalJFracPoly`
- **What**: Still injective after embedding.
- **How**: `holomorphicToMeromorphic_injective.comp evalJ_injective`.
- **Hypotheses**: none.
- **Uses from project**: `evalJFracPoly`, `holomorphicToMeromorphic_injective` (FieldAction.lean:59), `evalJ_injective`
- **Used by**: `ratFuncEvalJ`, `ratFuncEvalJ_injective`
- **Visibility**: public
- **Lines**: 91–92
- **Notes**: —

### `def Cox.UpperHalfPlaneFunctionField.ratFuncEvalJ`
- **Type**: `RatFunc ℂ →+* FunctionField := RatFunc.liftRingHom evalJFracPoly (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ evalJFracPoly_injective)`
- **What**: The embedding `ℂ(Y) → FunctionField`, `Y ↦ j`.
- **How**: mathlib `RatFunc.liftRingHom` (`Mathlib/FieldTheory/RatFunc/Basic.lean:437`) with the non-zero-divisor condition from injectivity (`Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:283`).
- **Hypotheses**: none.
- **Uses from project**: `evalJFracPoly`, `evalJFracPoly_injective`, `FunctionField`
- **Used by**: `ratFuncEvalJ_injective`, `instance Algebra (RatFunc ℂ) FunctionField`, `algebraMap_ratFunc`, `ratFuncEvalJ_algebraMap`
- **Visibility**: public
- **Lines**: 95–97
- **Notes**: External: ModularFunctionField.lean:115 (by `change`). Equivalent construction: `IsFractionRing.lift evalJFracPoly_injective` (`Mathlib/RingTheory/Localization/FractionRing.lean:347`) since `RatFunc ℂ` is `IsFractionRing ℂ[X]`.

### `theorem Cox.UpperHalfPlaneFunctionField.ratFuncEvalJ_injective`
- **Type**: `Function.Injective ratFuncEvalJ`
- **What**: `ℂ(Y)` embeds in the function field.
- **How**: mathlib `RatFunc.liftRingHom_injective` (`Mathlib/FieldTheory/RatFunc/Basic.lean:470`).
- **Hypotheses**: none.
- **Uses from project**: `ratFuncEvalJ`, `evalJFracPoly`, `evalJFracPoly_injective`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 100–102, proof body ≈ 2 lines
- **Notes**: Unused anywhere in the project. Also immediate from "a ring hom out of a field into a nontrivial ring is injective" (mathlib has this as `RingHom.injective`; path not re-verified this session).

### `noncomputable instance : Algebra (RatFunc ℂ) FunctionField`
- **Type**: `Algebra (RatFunc ℂ) FunctionField := ratFuncEvalJ.toAlgebra`
- **What**: Makes the meromorphic field a `ℂ(Y)`-algebra via `Y ↦ j`.
- **How**: `RingHom.toAlgebra`.
- **Hypotheses**: none.
- **Uses from project**: `ratFuncEvalJ`, `FunctionField`
- **Used by**: `algebraMap_ratFunc`, `precomp_ratFunc`, `precompAlgEquiv`
- **Visibility**: public (anonymous instance, synthesized name `instAlgebraRatFuncComplexFunctionField`)
- **Lines**: 104
- **Notes**: External: ModularFunctionField.lean (`IntermediateField (RatFunc ℂ) FunctionField`), Irreducibility.lean:51, Arithmetic.lean:80. `FunctionField` now carries three algebra structures — over `ℂ` (MeromorphicField.lean:445 via `constRingHom`), over `HolomorphicFunction` (FieldAction.lean:64), over `RatFunc ℂ` (here) — with no `IsScalarTower` or compatibility lemma between them (e.g. `algebraMap ℂ FunctionField = ratFuncEvalJ ∘ algebraMap ℂ (RatFunc ℂ) = algebraMap HolomorphicFunction FunctionField ∘ constant`). Not a diamond today because none is derived from another, but a latent hazard.

### `@[simp] theorem Cox.UpperHalfPlaneFunctionField.algebraMap_ratFunc`
- **Type**: `(r : RatFunc ℂ) : algebraMap (RatFunc ℂ) FunctionField r = ratFuncEvalJ r`
- **What**: Unfolds the instance.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `ratFuncEvalJ`, `FunctionField`, the `Algebra` instance
- **Used by**: `precomp_ratFunc`
- **Visibility**: public
- **Lines**: 108–109
- **Notes**: —

### `@[simp] theorem Cox.UpperHalfPlaneFunctionField.ratFuncEvalJ_algebraMap`
- **Type**: `(P : Polynomial ℂ) : ratFuncEvalJ (algebraMap (Polynomial ℂ) (RatFunc ℂ) P) = evalJFracPoly P`
- **What**: On polynomials the embedding is `evalJFracPoly`.
- **How**: `simp [ratFuncEvalJ]` (mathlib `RatFunc.liftRingHom_ofFractionRing_algebraMap`, `Mathlib/FieldTheory/RatFunc/Basic.lean:463`).
- **Hypotheses**: none.
- **Uses from project**: `ratFuncEvalJ`, `evalJFracPoly`
- **Used by**: `precomp_ratFunc`
- **Visibility**: public
- **Lines**: 113–116
- **Notes**: External: Arithmetic.lean:87, Irreducibility.lean:60, ModularFunctionField.lean:117, 146.

### `private theorem Cox.UpperHalfPlaneFunctionField.precomp_evalJPoly`
- **Type**: `(delta : SL(2, ℤ)) (P : Polynomial ℂ) : precomp delta (evalJFracPoly P) = evalJFracPoly P`
- **What**: Precomposition by `δ` fixes every `P(j)`.
- **How**: `precomp_algebraMap` (FieldAction.lean:137) reduces to holomorphic functions; `Subtype.ext; funext` and `evalJ_apply` + `j_modularGroup_smul`.
- **Hypotheses**: none.
- **Uses from project**: `precomp`, `precomp_algebraMap`, `evalJFracPoly`, `evalJ_apply`, `j_modularGroup_smul`
- **Used by**: `precomp_ratFunc`
- **Visibility**: private
- **Lines**: 118–125, proof body ≈ 6 lines
- **Notes**: —

### `private theorem Cox.UpperHalfPlaneFunctionField.precomp_ratFunc`
- **Type**: `(delta : SL(2, ℤ)) (r : RatFunc ℂ) : precomp delta (algebraMap (RatFunc ℂ) FunctionField r) = algebraMap (RatFunc ℂ) FunctionField r`
- **What**: Precomposition fixes the embedded `ℂ(Y)`.
- **How**: `RatFunc.induction_on` (`Mathlib/FieldTheory/RatFunc/Basic.lean:712`) and `map_div₀` with `precomp_evalJPoly`.
- **Hypotheses**: none.
- **Uses from project**: `precomp`, `algebraMap_ratFunc`, `ratFuncEvalJ_algebraMap`, `precomp_evalJPoly`
- **Used by**: `precompAlgEquiv`
- **Visibility**: private
- **Lines**: 128–133, proof body ≈ 4 lines
- **Notes**: Instance of the universal property: two ring homs out of a localization agreeing on the base agree (`IsLocalization.ringHom_ext`, `Mathlib/RingTheory/Localization/Defs.lean:548`), applied to `(precomp δ).toRingHom.comp ratFuncEvalJ` and `ratFuncEvalJ`.

### `def Cox.UpperHalfPlaneFunctionField.precompAlgEquiv`
- **Type**: `(delta : SL(2, ℤ)) : FunctionField ≃ₐ[RatFunc ℂ] FunctionField`
- **What**: Precomposition as a `ℂ(Y)`-algebra automorphism.
- **How**: `__ := precomp delta; commutes' := precomp_ratFunc delta`.
- **Hypotheses**: none.
- **Uses from project**: `precomp` (FieldAction.lean:129), `precomp_ratFunc`, `FunctionField`
- **Used by**: `precompAlgEquiv_rightCosetRoot`
- **Visibility**: public
- **Lines**: 136–138
- **Notes**: External: Irreducibility.lean:86 (`minpoly.aeval_algHom`). Exactly mathlib `AlgEquiv.ofRingEquiv` (`Mathlib/Algebra/Algebra/Equiv.lean:622`) applied to `precomp delta` and `precomp_ratFunc`.

### `private lemma Cox.UpperHalfPlaneFunctionField.transformed_leading`
- **Type**: `(m : ℕ+) (sigma : CoxMatrix m) : (transformedJSeries (zeta m) sigma).coeff (-(sigma.a^2)) = zeta m ^ (-(sigma.a * sigma.b))`
- **What**: The leading (most negative, index `-a²`) Laurent coefficient of the transformed `j`-series of a Cox matrix is the phase `ζ^{-ab}`.
- **How**: `transformedJSeries_coeff` with the `if_pos` branch (`a² ∣ -a²`), and `jIntCoeff_neg_one`.
- **Hypotheses**: none.
- **Uses from project**: `transformedJSeries`, `transformedJSeries_coeff`, `jIntCoeff_neg_one`, `zeta` (CoxMatrices/LaurentExpansion.lean:24–66), `CoxMatrix.a_pos`
- **Used by**: `transformed_leading_ne`, `transformed_phase`
- **Visibility**: private
- **Lines**: 140–147, proof body ≈ 5 lines
- **Notes**: Belongs in `CoxMatrices/LaurentExpansion.lean` next to `transformedJSeries_coeff`.

### `private lemma Cox.UpperHalfPlaneFunctionField.transformed_leading_ne`
- **Type**: `(m : ℕ+) (sigma : CoxMatrix m) : (transformedJSeries (zeta m) sigma).coeff (-(sigma.a^2)) ≠ 0`
- **What**: That leading coefficient is nonzero.
- **How**: `transformed_leading` and `zpow_ne_zero` with `zeta_isPrimitiveRoot`.
- **Hypotheses**: none.
- **Uses from project**: `transformed_leading`, `zeta_isPrimitiveRoot`, `zeta`, `transformedJSeries`
- **Used by**: `cox_a_le`
- **Visibility**: private
- **Lines**: 149–152, proof body ≈ 2 lines
- **Notes**: —

### `private lemma Cox.UpperHalfPlaneFunctionField.cox_a_le`
- **Type**: `{m : ℕ+} {sigma tau : CoxMatrix m} (h : transformedJSeries (zeta m) sigma = transformedJSeries (zeta m) tau) : sigma.a ≤ tau.a`
- **What**: Equal transformed series force `a_σ ≤ a_τ` (by comparing the lowest exponent).
- **How**: The coefficient at `-a_σ²` of `τ`'s series is nonzero, so by `transformedJSeries_coeff`'s `if_neg` contrapositive `-a_τ² ≤ -a_σ²`; `nlinarith`.
- **Hypotheses**: series equality.
- **Uses from project**: `transformedJSeries`, `transformedJSeries_coeff`, `transformed_leading_ne`, `zeta`, `CoxMatrix.a_pos`
- **Used by**: `transformed_injective` (twice, symmetric)
- **Visibility**: private
- **Lines**: 154–167, proof body ≈ 11 lines
- **Notes**: Would read better via `HahnSeries.order` (`transformedJSeries.order = -a²`), which the project computes elsewhere (`laurentqExpansion_j_order_widthM`, DiagonalLaurent.lean).

### `private lemma Cox.UpperHalfPlaneFunctionField.transformed_phase`
- **Type**: `… (h : transformedJSeries (zeta m) sigma = transformedJSeries (zeta m) tau) (ha : sigma.a = tau.a) : zeta m ^ (-(sigma.a * sigma.b)) = zeta m ^ (-(sigma.a * tau.b))`
- **What**: With equal `a`, the leading phases agree.
- **How**: `congrArg (coeff (-a²))` and `transformed_leading` twice.
- **Hypotheses**: series equality, `a_σ = a_τ`.
- **Uses from project**: `transformedJSeries`, `transformed_leading`, `zeta`
- **Used by**: `transformed_injective`
- **Visibility**: private
- **Lines**: 169–177, proof body ≈ 4 lines
- **Notes**: —

### `private lemma Cox.UpperHalfPlaneFunctionField.cox_b_eq`
- **Type**: `{m : ℕ+} {sigma tau : CoxMatrix m} (hd : sigma.d = tau.d) (hphase : zeta m ^ (-(sigma.a*sigma.b)) = zeta m ^ (-(sigma.a*tau.b))) : sigma.b = tau.b`
- **What**: Equal phases and equal `d` force equal `b` (since `0 ≤ b < d` and `ζ` has exact order `m = ad`).
- **How**: `IsPrimitiveRoot.zpow_eq_one_iff_dvd` (`Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean:341`) gives `ad ∣ a(b' - b)`, cancel `a` (`mul_dvd_mul_iff_left`), then `Nat.ModEq.eq_of_lt_of_lt` (`Mathlib/Data/Nat/ModEq.lean:374`) with `CoxMatrix.b_lt`.
- **Hypotheses**: `d_σ = d_τ` and the phase equality.
- **Uses from project**: `zeta`, `zeta_isPrimitiveRoot`, `CoxMatrix.determinant`, `CoxMatrix.a_pos`, `CoxMatrix.b_lt`
- **Used by**: `transformed_injective`
- **Visibility**: private
- **Lines**: 179–201, proof body ≈ 18 lines
- **Notes**: —

### `private theorem Cox.UpperHalfPlaneFunctionField.transformed_injective`
- **Type**: `(m : ℕ+) : Function.Injective (transformedJSeries (zeta m) : CoxMatrix m → LaurentSeries ℂ)`
- **What**: Distinct Cox matrices have distinct transformed `j`-series.
- **How**: `a` by `le_antisymm (cox_a_le h) (cox_a_le h.symm)`, `d` by `determinant` cancellation, `b` by `cox_b_eq (transformed_phase h ha)`, then `CoxMatrix.toFin_injective`.
- **Hypotheses**: none.
- **Uses from project**: `transformedJSeries`, `zeta`, `cox_a_le`, `cox_b_eq`, `transformed_phase`, `CoxMatrix.determinant`, `CoxMatrix.toFin`, `CoxMatrix.toFin_injective` (CoxMatrices/Basic.lean:96)
- **Used by**: `conjugate_injective`
- **Visibility**: private
- **Lines**: 203–212, proof body ≈ 8 lines
- **Notes**: —

### `private theorem Cox.UpperHalfPlaneFunctionField.conjugate_injective`
- **Type**: `(m : ℕ+) : Function.Injective (fun sigma : CoxMatrix m ↦ fun tau : ℍ ↦ j (sigma.act tau))`
- **What**: Cox's "the functions `j(στ)` are pairwise distinct" (the analytic input to `Φ_m` having distinct roots).
- **How**: Laurent expansion is injective on these functions: `laurentqExpansion_coxAction` identifies `laurentqExpansion m (j ∘ σ.act)` with `transformedJSeries (zeta m) σ`, then `transformed_injective`.
- **Hypotheses**: none.
- **Uses from project**: `CoxMatrix.act`, `j`, `transformed_injective`, `laurentqExpansion_coxAction` (CoxMatrices/LaurentExpansion.lean:304), `laurentqExpansion`
- **Used by**: `rightCosetFunction_injective`
- **Visibility**: private
- **Lines**: 214–219, proof body ≈ 4 lines
- **Notes**: Mathematically important standalone statement hidden as private in a file about the function field; belongs public in `CoxMatrices/LaurentExpansion.lean`.

### `private lemma Cox.UpperHalfPlaneFunctionField.rightCosetEval_mdifferentiable`
- **Type**: `(m : ℕ+) (c : Gamma0RightCosets m) : MDiff (rightCosetEval m c)`
- **What**: Each right-coset conjugate `j(mγτ)` is holomorphic.
- **How**: `Quotient.inductionOn`, `rightCosetEval_mk`, `(levelJ_mdifferentiable m).comp (sl2_mdifferentiable gamma)`.
- **Hypotheses**: none.
- **Uses from project**: `Gamma0RightCosets`, `rightCosetEval`, `rightCosetEval_mk`, `levelJ_mdifferentiable`, `sl2_mdifferentiable` (FieldAction.lean:38)
- **Used by**: `rightCosetFunction`
- **Visibility**: private
- **Lines**: 221–225, proof body ≈ 3 lines
- **Notes**: Duplicated inline as `hcoset` at Construction.lean:215–218 (with `UpperHalfPlane.mdifferentiable_smul` instead of `sl2_mdifferentiable`). Should be public in CoxMatrices/Basic.lean or AnalyticSupport.lean.

### `def Cox.UpperHalfPlaneFunctionField.rightCosetFunction`
- **Type**: `(m : ℕ+) (c : Gamma0RightCosets m) : HolomorphicFunction := ⟨rightCosetEval m c, rightCosetEval_mdifferentiable m c⟩`
- **What**: The conjugate `j(mγτ)` as a holomorphic-subring element.
- **How**: subtype constructor.
- **Hypotheses**: none.
- **Uses from project**: `HolomorphicFunction`, `Gamma0RightCosets`, `rightCosetEval`, `rightCosetEval_mdifferentiable`
- **Used by**: `rightCosetFunction_injective`, `rightCosetRoot`
- **Visibility**: public
- **Lines**: 228–229
- **Notes**: External: Arithmetic.lean:58, Interpolation.lean:138, 407, 418, Irreducibility.lean:31, 41, 44.

### `theorem Cox.UpperHalfPlaneFunctionField.rightCosetFunction_injective`
- **Type**: `(m : ℕ+) : Function.Injective (rightCosetFunction m)`
- **What**: Distinct right cosets give distinct holomorphic conjugates.
- **How**: Transport along `coxMatrixEquivRightCosets` (surjective), reduce to `conjugate_injective` via `rightCosetEval_equiv`.
- **Hypotheses**: none.
- **Uses from project**: `rightCosetFunction`, `coxMatrixEquivRightCosets` (CoxMatrices/Basic.lean:600), `conjugate_injective`, `rightCosetEval_equiv` (CoxMatrices/Basic.lean:769)
- **Used by**: `rightCosetRoot_injective`
- **Visibility**: public
- **Lines**: 232–241, proof body ≈ 8 lines
- **Notes**: External: Interpolation.lean:429.

### `def Cox.UpperHalfPlaneFunctionField.rightCosetRoot`
- **Type**: `(m : ℕ+) (c : Gamma0RightCosets m) : FunctionField := algebraMap HolomorphicFunction FunctionField (rightCosetFunction m c)`
- **What**: The conjugate as an element of the meromorphic field (a root of `Φ_m(X, j)`).
- **How**: `algebraMap`.
- **Hypotheses**: none.
- **Uses from project**: `FunctionField`, `HolomorphicFunction`, `rightCosetFunction`
- **Used by**: `rightCosetRoot_injective`, `precompAlgEquiv_rightCosetRoot`
- **Visibility**: public
- **Lines**: 244–245
- **Notes**: External: Arithmetic.lean:56, 97, Irreducibility.lean:65–122.

### `theorem Cox.UpperHalfPlaneFunctionField.rightCosetRoot_injective`
- **Type**: `(m : ℕ+) : Function.Injective (rightCosetRoot m)`
- **What**: The roots remain distinct in the field.
- **How**: `holomorphicToMeromorphic_injective.comp (rightCosetFunction_injective m)`.
- **Hypotheses**: none.
- **Uses from project**: `rightCosetRoot`, `holomorphicToMeromorphic_injective`, `rightCosetFunction_injective`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 248–249
- **Notes**: External: Irreducibility.lean:122 (`irreducible_of_card_conjugates`).

### `theorem Cox.UpperHalfPlaneFunctionField.precompAlgEquiv_rightCosetRoot`
- **Type**: `(m : ℕ+) (delta : SL(2, ℤ)) (c : Gamma0RightCosets m) : precompAlgEquiv delta (rightCosetRoot m c) = rightCosetRoot m (rightCosetMul m delta c)`
- **What**: The Galois-type action: precomposition by `δ` permutes the roots by right multiplication of cosets.
- **How**: `precomp_algebraMap` reduces to holomorphic functions; `Subtype.ext; funext` and `rightCosetEval_smul`.
- **Hypotheses**: none.
- **Uses from project**: `precompAlgEquiv`, `rightCosetRoot`, `rightCosetMul` (CoxMatrices/Basic.lean:641), `precomp`, `precomp_algebraMap`, `rightCosetEval_smul` (CoxMatrices/Basic.lean:694)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 252–261, proof body ≈ 7 lines
- **Notes**: External: Irreducibility.lean:85 (`minpoly_aeval_rightCosetRoot`).

## File Summary
- Total declarations: 31 (9 defs/abbrevs, 21 lemmas/theorems, 1 instance, 0 other)
- Key API (used by 3+ others in the file): `FunctionField` (10), `evalJFracPoly` (5), `evalJ` (4), `ratFuncEvalJ` (4), `HolomorphicFunction` (imported, 6), `precomp` (imported, 4)
- Unused declarations (not used by anything in this file): `algebraMap_jElement` (unused everywhere), `ratFuncEvalJ_injective` (unused everywhere), `rightCosetRoot_injective` (external), `precompAlgEquiv_rightCosetRoot` (external)
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none (longest `cox_b_eq` 18)

## Observations

### Mathlib API candidates
- `precompAlgEquiv` (136–138) = `AlgEquiv.ofRingEquiv` (`Mathlib/Algebra/Algebra/Equiv.lean:622`) with `hf := precomp_ratFunc delta`.
- `precomp_ratFunc` (128–133) = `IsLocalization.ringHom_ext` (`Mathlib/RingTheory/Localization/Defs.lean:548`) for `RatFunc ℂ = FractionRing ℂ[X]`, given `precomp_evalJPoly`; the `RatFunc.induction_on` route is fine but the ext-lemma route needs no `map_div₀`.
- `evalJ`/`constant` (36–56): with `holomorphicFunctions : Subalgebra ℂ (ℍ → ℂ)` (mathlib `Pi.algebra`; `algebraMap_mem'` is `mdifferentiable_const`) these become `Polynomial.aeval jElement` and `algebraMap ℂ _`; `evalJ_apply` becomes `Polynomial.aeval_fn_apply` (`Mathlib/Algebra/Polynomial/AlgebraMap.lean:480`) modulo the subtype coercion. Also unlocks `Polynomial.aeval_algHom_apply` for `evaluation`, giving `evaluation_comp_evalJ` for free.
- `ratFuncEvalJ` (95–97): fine as `RatFunc.liftRingHom`; alternative `IsFractionRing.lift` (`Mathlib/RingTheory/Localization/FractionRing.lean:347`). `ratFuncEvalJ_injective` is `RatFunc.liftRingHom_injective` (`Mathlib/FieldTheory/RatFunc/Basic.lean:470`) and is never consumed.
- `cox_a_le` (154–167) hand-compares coefficients where `HahnSeries.order`/`HahnSeries.coeff_order_ne_zero` API (used elsewhere in the project via `laurentqExpansion_j_order_widthM`) would give `order (transformedJSeries σ) = -a²` and a one-line comparison.
- `matrix`/`Laurent` block (140–219): no mathlib analogue for the statement "distinct Cox matrices give distinct `j ∘ σ.act`" (searched: nothing about `j` in mathlib beyond `ModularForm`s); it is Cox-specific but misplaced in this file.

### Missing API / repeated patterns
- `evaluation_comp_evalJ : (evaluation τ).comp evalJ = Polynomial.evalRingHom (j τ)` — proved inline at ModularFunctionField.lean:41–42 and Arithmetic.lean:69–72 (identical 3-line `RingHom.ext`/`DFunLike.ext` + `evalJ_apply`).
- `rightCosetEval_mdifferentiable` (221–225, private) is re-proved inline at Construction.lean:215–218; make it public in CoxMatrices/Basic.lean.
- `conjugate_injective` (214–219, private) should be a public theorem in `CoxMatrices/LaurentExpansion.lean` (it is the headline distinctness result of Cox §11B).
- Compatibility lemmas between the three `Algebra _ FunctionField` structures (ℂ, `HolomorphicFunction`, `RatFunc ℂ`): none exist; suggested `IsScalarTower ℂ (RatFunc ℂ) FunctionField` and `algebraMap_ratFunc_C : algebraMap (RatFunc ℂ) FunctionField (RatFunc.C c) = algebraMap ℂ FunctionField c`.
- `Subtype.ext; funext τ; …` unfolding of `HolomorphicFunction` equalities (lines 121–125, 258–261, Arithmetic.lean:64–66, Irreducibility.lean:32–34, ModularFunctionField.lean:97–100, Interpolation.lean:455–458): a `HolomorphicFunction.ext_iff`/`@[ext]` lemma `HolomorphicFunction.ext (h : ∀ τ, f.1 τ = g.1 τ) : f = g` would shorten each to one `ext τ`.

### Junk candidates
- `algebraMap_jElement` (48–52): unused anywhere. (It is however the natural bridge `jElement ↔ jModularFunction`; the analogous `toMeromorphicField_levelJModularFunction` in ModularFunctionField.lean *is* used.)
- `ratFuncEvalJ_injective` (100–102): unused anywhere.
- `jElement` (44): used only inside `evalJ`; could be inlined.
- File docstring (16–22) claims precomposition "act[s] transitively on the right-coset conjugates" — transitivity is proved in CoxMatrices (`exists_rightCosetMul_baseRightCoset_eq`), not here; only equivariance (`precompAlgEquiv_rightCosetRoot`) is proved here.
- Double blank line at 9–10 between import groups (style).

### Moral duplicates within this batch
- `rightCosetEval_mdifferentiable` (221) ≡ Construction.lean:215–218 (`hcoset`).
- `evalJ_apply`'s inner step `(evaluation τ).comp constant = RingHom.id` (68–70) and ModularFunctionField.lean:41–42 `(evaluation τ).comp evalJ = evalRingHom (j τ)` and Arithmetic.lean:69–72: the same "evaluation commutes with eval₂" step.
- `rightCosetRoot_injective` (248) and `evalJFracPoly_injective` (91): both `holomorphicToMeromorphic_injective.comp _`.
- `precomp_evalJPoly` (118) and `precompAlgEquiv_rightCosetRoot` (252): same `precomp_algebraMap; Subtype.ext; funext` skeleton.

### Generalization notes
- `evalJ_injective` (76–84) uses only `j_surjective` and `Infinite ℂ`: it is "`Polynomial.aeval g` is injective for any surjective `g : X → K`, `K` infinite field" — a general lemma (`Polynomial.funext` + surjectivity) not tied to `j`.
- `transformed_injective`/`cox_b_eq`/`cox_a_le` (154–212) hold for any field `K` with a primitive `m`-th root `ζ` in place of `zeta m : ℂ` (only `IsPrimitiveRoot.zpow_eq_one_iff_dvd`, `zpow_ne_zero`, `HahnSeries.coeff` are used); `transformedJSeries` itself is already generic over `K` (see FormalCoxProduct.lean:75 usage with `{K} [Field K] [CharZero K]`).
- `precomp_ratFunc` is an instance of "any ring endomorphism of `L` fixing `φ(ℂ[X])` fixes `liftRingHom φ` pointwise", valid for any `RatFunc.liftRingHom`.
