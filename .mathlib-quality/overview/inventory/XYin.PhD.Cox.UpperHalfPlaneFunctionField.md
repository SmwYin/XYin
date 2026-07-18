# XYin/PhD/Cox/UpperHalfPlaneFunctionField.lean — project imports: `XYin.PhD.Cox.CoxMatrices` (plus mathlib `Mathlib.FieldTheory.RatFunc.Basic`)

All declarations live in namespace `Cox.UpperHalfPlaneFunctionField`.

### `def holomorphicFunctions`
- **Type**: `def holomorphicFunctions : Subring (ℍ → ℂ)` with carrier `{f | MDiff f}`
- **What**: The subring of the function ring `ℍ → ℂ` consisting of holomorphic (MDifferentiable in the manifold sense) functions on the upper half-plane.
- **How**: Closure axioms from mathlib's `mdifferentiable_const`, `MDifferentiable.add/neg/mul`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `HolomorphicFunction`, `evaluation` (via `holomorphicFunctions.subtype`)
- **Visibility**: public
- **Lines**: 30–36
- **Notes**: `MDiff` is mathlib's scoped notation (Mathlib.Analysis.Complex.UpperHalfPlane.Manifold)

### `abbrev HolomorphicFunction`
- **Type**: `abbrev HolomorphicFunction := holomorphicFunctions` (the subring's coercion to a type)
- **What**: The type of holomorphic functions on ℍ, as elements of the subring — the base ring of the function field.
- **How**: Abbreviation; no proof.
- **Hypotheses**: none.
- **Uses from project**: [`holomorphicFunctions`]
- **Used by**: `NoZeroDivisors` instance, `FunctionField`, `constant`, `jElement`, `evalJ`, `evaluation`, `evalJ_apply`, `evalJ_injective`, `evalJFracPoly`, `precompHolomorphic`, `precomp_evalJPoly`, `rightCosetFunction`, `rightCosetFunction_injective`, `rightCosetRoot`, `precompAlgEquiv_rightCosetRoot`
- **Visibility**: public
- **Lines**: 38–39
- **Notes**: none

### `instance : NoZeroDivisors HolomorphicFunction`
- **Type**: `instance : NoZeroDivisors HolomorphicFunction`
- **What**: The ring of holomorphic functions on ℍ is an integral domain (no zero divisors) — the prerequisite for forming its fraction field.
- **How**: Reduces to mathlib's `UpperHalfPlane.mul_eq_zero_iff` (the identity theorem for MDifferentiable functions on the connected domain ℍ: a product vanishes identically iff a factor does), then `Subtype.ext`.
- **Hypotheses**: both factors are holomorphic (carried by the subtype).
- **Uses from project**: [`HolomorphicFunction`]
- **Used by**: `FunctionField` (needed for `FractionRing`), and implicitly all fraction-field constructions
- **Visibility**: public (anonymous instance)
- **Lines**: 41–49 (proof 8 lines)
- **Notes**: none

### `abbrev FunctionField`
- **Type**: `abbrev FunctionField := FractionRing HolomorphicFunction`
- **What**: The function field of the upper half-plane: the fraction field of the domain of holomorphic functions, in which `ℂ(j)` and the conjugate roots live.
- **How**: Abbreviation over mathlib's `FractionRing`; no proof.
- **Hypotheses**: none (uses the `NoZeroDivisors` instance).
- **Uses from project**: [`HolomorphicFunction`]
- **Used by**: `evalJFracPoly`, `ratFuncEvalJ`, `Algebra (RatFunc ℂ)` instance, `precomp`, `precompAlgEquiv`, `rightCosetRoot`, `rightCosetRoot_injective`, `precompAlgEquiv_rightCosetRoot`, `algebraMap_ratFunc`
- **Visibility**: public
- **Lines**: 51–52
- **Notes**: none

### `def constant`
- **Type**: `private def constant : ℂ →+* HolomorphicFunction`
- **What**: The ring homomorphism sending a complex number to the corresponding constant holomorphic function on ℍ.
- **How**: Constant functions are MDifferentiable (`mdifferentiable_const`); hom laws are `rfl`.
- **Hypotheses**: none.
- **Uses from project**: [`HolomorphicFunction`]
- **Used by**: `evalJ`, `evalJ_apply`
- **Visibility**: private
- **Lines**: 54–59
- **Notes**: none

### `def jElement`
- **Type**: `def jElement : HolomorphicFunction := ⟨j, j_mdifferentiable⟩`
- **What**: The modular function `j` bundled as an element of the ring of holomorphic functions.
- **How**: Packaging with the project's holomorphy proof `j_mdifferentiable`.
- **Hypotheses**: none.
- **Uses from project**: [`HolomorphicFunction`, `j` (XYin.PhD.jFunction.jfunction), `j_mdifferentiable` (XYin.PhD.Cox.ModularFunction)]
- **Used by**: `evalJ`, `evalJ_apply`
- **Visibility**: public
- **Lines**: 61–62
- **Notes**: none

### `def evalJ`
- **Type**: `def evalJ : Polynomial ℂ →+* HolomorphicFunction := Polynomial.eval₂RingHom constant jElement`
- **What**: Evaluation of complex polynomials at the function `j`: the ring homomorphism `P ↦ P(j)` landing in holomorphic functions.
- **How**: mathlib's `Polynomial.eval₂RingHom` applied to the constant embedding and `jElement`.
- **Hypotheses**: none.
- **Uses from project**: [`constant`, `jElement`, `HolomorphicFunction`]
- **Used by**: `evalJ_apply`, `evalJ_injective`, `evalJFracPoly`
- **Visibility**: public
- **Lines**: 64–66
- **Notes**: none

### `def evaluation`
- **Type**: `def evaluation (tau : ℍ) : HolomorphicFunction →+* ℂ := (Pi.evalRingHom _ tau).comp holomorphicFunctions.subtype`
- **What**: Evaluation of a holomorphic function at a fixed point of the upper half-plane, as a ring homomorphism.
- **How**: Composition of the subring inclusion with mathlib's pointwise evaluation `Pi.evalRingHom`.
- **Hypotheses**: none.
- **Uses from project**: [`HolomorphicFunction`, `holomorphicFunctions`]
- **Used by**: `evalJ_apply`
- **Visibility**: public
- **Lines**: 68–70
- **Notes**: none

### `theorem evalJ_apply`
- **Type**: `(P : Polynomial ℂ) (tau : ℍ) : (evalJ P).1 tau = P.eval (j tau)`
- **What**: Pointwise description of polynomial evaluation at `j`: the function `P(j)` evaluated at `τ` equals the number `P(j(τ))`.
- **How**: Commutes evaluation-at-a-point past `eval₂` using mathlib's `Polynomial.hom_eval₂`; the composite `evaluation tau ∘ constant` is the identity of ℂ, and `Polynomial.eval₂_at_apply` finishes.
- **Hypotheses**: none.
- **Uses from project**: [`evalJ`, `constant`, `jElement`, `evaluation`, `HolomorphicFunction`, `j`]
- **Used by**: `evalJ_injective`, `precomp_evalJPoly`
- **Visibility**: public
- **Lines**: 72–83 (proof 10 lines)
- **Notes**: @[simp]

### `theorem evalJ_injective`
- **Type**: `Function.Injective evalJ`
- **What**: Polynomial evaluation at `j` is injective: distinct complex polynomials give distinct holomorphic functions of the form `P(j)`.
- **How**: Since the analytic `j` is surjective onto ℂ (`j_surjective`, Cox Theorem 11.2(iii)), `P(j(τ)) = Q(j(τ))` for all `τ` forces `P(z) = Q(z)` for every `z ∈ ℂ`, and `Polynomial.funext` (infinite field) concludes `P = Q`.
- **Hypotheses**: none.
- **Uses from project**: [`evalJ`, `evalJ_apply`, `j_surjective` (XYin.PhD.Cox.LatticeJ), `HolomorphicFunction`]
- **Used by**: `evalJFracPoly_injective`
- **Visibility**: public
- **Lines**: 85–94 (proof 8 lines)
- **Notes**: none

### `def evalJFracPoly`
- **Type**: `def evalJFracPoly : Polynomial ℂ →+* FunctionField := (algebraMap HolomorphicFunction FunctionField).comp evalJ`
- **What**: Evaluation at `j` followed by the localization map into the function field.
- **How**: Composition of ring homs; no proof.
- **Hypotheses**: none.
- **Uses from project**: [`evalJ`, `FunctionField`, `HolomorphicFunction`]
- **Used by**: `evalJFracPoly_injective`, `ratFuncEvalJ`, `ratFuncEvalJ_injective`, `ratFuncEvalJ_algebraMap`, `precomp_evalJPoly`, `precomp_ratFunc`
- **Visibility**: public
- **Lines**: 96–98
- **Notes**: none

### `theorem evalJFracPoly_injective`
- **Type**: `Function.Injective evalJFracPoly`
- **What**: Evaluation at `j` remains injective after inclusion into the fraction field.
- **How**: Composition of `evalJ_injective` with the injectivity of the localization map of a domain into its fraction field (`IsFractionRing.injective`).
- **Hypotheses**: none.
- **Uses from project**: [`evalJFracPoly`, `evalJ_injective`, `HolomorphicFunction`, `FunctionField`]
- **Used by**: `ratFuncEvalJ`, `ratFuncEvalJ_injective`
- **Visibility**: public
- **Lines**: 100–102 (proof 1 line)
- **Notes**: none

### `def ratFuncEvalJ`
- **Type**: `def ratFuncEvalJ : RatFunc ℂ →+* FunctionField := RatFunc.liftRingHom evalJFracPoly (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ evalJFracPoly_injective)`
- **What**: The field embedding `ℂ(Y) → FunctionField` sending `Y ↦ j`: the realization of the rational function field inside the function field of ℍ.
- **How**: mathlib's `RatFunc.liftRingHom`, legitimate because the injective `evalJFracPoly` maps nonzero polynomials to nonzerodivisors (`nonZeroDivisors_le_comap_nonZeroDivisors_of_injective`).
- **Hypotheses**: none.
- **Uses from project**: [`evalJFracPoly`, `evalJFracPoly_injective`, `FunctionField`]
- **Used by**: `ratFuncEvalJ_injective`, `Algebra (RatFunc ℂ) FunctionField` instance, `algebraMap_ratFunc`, `ratFuncEvalJ_algebraMap`, `precomp_ratFunc`
- **Visibility**: public
- **Lines**: 104–107
- **Notes**: none

### `theorem ratFuncEvalJ_injective`
- **Type**: `Function.Injective ratFuncEvalJ`
- **What**: The embedding of `ℂ(Y)` into the function field is injective (as any field hom, but proved via the lift).
- **How**: mathlib's `RatFunc.liftRingHom_injective` applied to the injective `evalJFracPoly`.
- **Hypotheses**: none.
- **Uses from project**: [`ratFuncEvalJ`, `evalJFracPoly`, `evalJFracPoly_injective`]
- **Used by**: unused in file (API for downstream degree/minimal-polynomial arguments)
- **Visibility**: public
- **Lines**: 109–112 (proof 2 lines)
- **Notes**: none

### `instance : Algebra (RatFunc ℂ) FunctionField`
- **Type**: `noncomputable instance : Algebra (RatFunc ℂ) FunctionField := ratFuncEvalJ.toAlgebra`
- **What**: Endows the function field with the `ℂ(Y)`-algebra structure in which `Y` acts as `j` — the base for viewing conjugate roots as algebraic elements over `ℂ(j)`.
- **How**: `RingHom.toAlgebra` on `ratFuncEvalJ`.
- **Hypotheses**: none.
- **Uses from project**: [`ratFuncEvalJ`, `FunctionField`]
- **Used by**: `algebraMap_ratFunc`, `precomp_ratFunc`, `precompAlgEquiv` (the `≃ₐ[RatFunc ℂ]` structure)
- **Visibility**: public (anonymous instance)
- **Lines**: 114
- **Notes**: noncomputable

### `theorem algebraMap_ratFunc`
- **Type**: `(r : RatFunc ℂ) : algebraMap (RatFunc ℂ) FunctionField r = ratFuncEvalJ r`
- **What**: The algebra-map of the chosen algebra structure is literally `ratFuncEvalJ`.
- **How**: `rfl` — definitional unfolding of `RingHom.toAlgebra`.
- **Hypotheses**: none.
- **Uses from project**: [`ratFuncEvalJ`, `FunctionField`]
- **Used by**: unused in file (simp lemma for downstream files)
- **Visibility**: public
- **Lines**: 116–119 (proof `rfl`)
- **Notes**: @[simp]

### `theorem ratFuncEvalJ_algebraMap`
- **Type**: `(P : Polynomial ℂ) : ratFuncEvalJ (algebraMap (Polynomial ℂ) (RatFunc ℂ) P) = evalJFracPoly P`
- **What**: On polynomials, the embedding of `ℂ(Y)` restricts to evaluation at `j`.
- **How**: `RatFunc.liftRingHom` composed with the polynomial coercion is the original hom; discharged by `simp [ratFuncEvalJ]` (mathlib's `RatFunc.liftRingHom_apply_div`-style simp set).
- **Hypotheses**: none.
- **Uses from project**: [`ratFuncEvalJ`, `evalJFracPoly`]
- **Used by**: `precomp_ratFunc`
- **Visibility**: public
- **Lines**: 121–126 (proof 1 line)
- **Notes**: @[simp]

### `lemma sl2_mdifferentiable`
- **Type**: `private lemma sl2_mdifferentiable (delta : SL(2, ℤ)) : MDiff (fun tau : ℍ ↦ delta • tau)`
- **What**: The Möbius action of any element of `SL₂(ℤ)` is a holomorphic self-map of the upper half-plane.
- **How**: Specializes mathlib's `UpperHalfPlane.mdifferentiable_smul` (holomorphy of the `GL₂(ℝ)⁺` action) to the image of `delta` in `GL₂(ℝ)`, whose determinant is positive.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `precompHolomorphic`, `rightCosetEval_mdifferentiable`
- **Visibility**: private
- **Lines**: 128–131 (proof 2 lines)
- **Notes**: none

### `def precompHolomorphic`
- **Type**: `private def precompHolomorphic (delta : SL(2, ℤ)) : HolomorphicFunction ≃+* HolomorphicFunction`
- **What**: Precomposition `f ↦ f(δ·)` by a modular transformation, as a ring automorphism of the holomorphic functions; the inverse is precomposition by `δ⁻¹`.
- **How**: Holomorphy of composites via `MDifferentiable.comp` with `sl2_mdifferentiable`; the inverse laws are the group action identities `δ⁻¹•(δ•τ) = τ` discharged by `simp`; ring-hom laws are `rfl` since precomposition is pointwise.
- **Hypotheses**: none.
- **Uses from project**: [`HolomorphicFunction`, `sl2_mdifferentiable`]
- **Used by**: `precomp`, `precomp_evalJPoly`
- **Visibility**: private
- **Lines**: 133–148
- **Notes**: none

### `def precomp`
- **Type**: `private def precomp (delta : SL(2, ℤ)) : FunctionField ≃+* FunctionField := IsFractionRing.ringEquivOfRingEquiv (precompHolomorphic delta)`
- **What**: The precomposition automorphism extended from the ring of holomorphic functions to its fraction field.
- **How**: mathlib's `IsFractionRing.ringEquivOfRingEquiv`, the universal extension of a ring automorphism of a domain to its fraction field.
- **Hypotheses**: none.
- **Uses from project**: [`precompHolomorphic`, `FunctionField`]
- **Used by**: `precomp_evalJPoly`, `precomp_ratFunc`, `precompAlgEquiv`, `precompAlgEquiv_rightCosetRoot`
- **Visibility**: private
- **Lines**: 150–153
- **Notes**: none

### `theorem precomp_evalJPoly`
- **Type**: `private theorem precomp_evalJPoly (delta : SL(2, ℤ)) (P : Polynomial ℂ) : precomp delta (evalJFracPoly P) = evalJFracPoly P`
- **What**: Precomposition by a modular transformation fixes every function of the form `P(j)` — because `j` itself is `SL₂(ℤ)`-invariant.
- **How**: Reduce to the subring via `IsFractionRing.ringEquivOfRingEquiv_algebraMap`, then pointwise: `P(j(δτ)) = P(j(τ))` by `evalJ_apply` and the invariance `j_modularGroup_smul`.
- **Hypotheses**: none.
- **Uses from project**: [`precomp`, `precompHolomorphic`, `evalJFracPoly`, `evalJ_apply`, `j_modularGroup_smul` (XYin.PhD.jFunction.jfunction), `HolomorphicFunction`, `FunctionField`]
- **Used by**: `precomp_ratFunc`
- **Visibility**: private
- **Lines**: 155–163 (proof 8 lines)
- **Notes**: none

### `theorem precomp_ratFunc`
- **Type**: `private theorem precomp_ratFunc (delta : SL(2, ℤ)) (r : RatFunc ℂ) : precomp delta (algebraMap (RatFunc ℂ) FunctionField r) = algebraMap (RatFunc ℂ) FunctionField r`
- **What**: Precomposition fixes the whole embedded copy of `ℂ(Y) = ℂ(j)`, not just polynomials in `j`.
- **How**: `RatFunc.induction_on` writes `r = p/q`; the ring equivalence commutes with division (`map_div₀`), and both numerator and denominator are fixed by `precomp_evalJPoly` (via `ratFuncEvalJ_algebraMap`).
- **Hypotheses**: none.
- **Uses from project**: [`precomp`, `precomp_evalJPoly`, `ratFuncEvalJ`, `ratFuncEvalJ_algebraMap`, `FunctionField`]
- **Used by**: `precompAlgEquiv`
- **Visibility**: private
- **Lines**: 165–176 (proof 10 lines)
- **Notes**: none

### `def precompAlgEquiv`
- **Type**: `def precompAlgEquiv (delta : SL(2, ℤ)) : FunctionField ≃ₐ[RatFunc ℂ] FunctionField`
- **What**: Precomposition by `δ ∈ SL₂(ℤ)` bundled as a `ℂ(Y)`-algebra automorphism of the function field — the Galois-type symmetry used to permute the conjugate roots `j(mγτ)`.
- **How**: The ring equivalence `precomp delta` together with the base-fixing property `precomp_ratFunc` as `commutes'`.
- **Hypotheses**: none.
- **Uses from project**: [`precomp`, `precomp_ratFunc`, `FunctionField`]
- **Used by**: `precompAlgEquiv_rightCosetRoot`
- **Visibility**: public
- **Lines**: 178–181
- **Notes**: none

### `lemma transformed_leading`
- **Type**: `private lemma transformed_leading (m : ℕ+) (sigma : CoxMatrix m) : (transformedJSeries (zeta m) sigma).coeff (-((sigma.a : ℤ)^2)) = zeta m ^ (-((sigma.a : ℤ) * (sigma.b : ℤ)))`
- **What**: The leading Laurent coefficient of the transformed `j`-series of a Cox matrix `σ = [[a,b],[0,d]]` sits at exponent `−a²` and equals the phase `ζₘ^(−ab)`.
- **How**: Unfolds `transformedJSeries_coeff` at `k = −a²` (the `if` condition holds since `a² ∣ a²` and `−a² ≤ −a²`) and uses `jIntCoeff_neg_one = 1` (the `q⁻¹` coefficient of the `j`-expansion), leaving only the root-of-unity factor.
- **Hypotheses**: none.
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_coeff`, `jIntCoeff_neg_one` (XYin.PhD.Cox.CoxMatrices.LaurentExpansion), `zeta`, `CoxMatrix` (fields `a`, `b`, `a_pos`)]
- **Used by**: `transformed_leading_ne`, `transformed_phase`
- **Visibility**: private
- **Lines**: 183–190 (proof 5 lines)
- **Notes**: none

### `lemma transformed_leading_ne`
- **Type**: `private lemma transformed_leading_ne (m : ℕ+) (sigma : CoxMatrix m) : (transformedJSeries (zeta m) sigma).coeff (-((sigma.a : ℤ)^2)) ≠ 0`
- **What**: The leading coefficient at exponent `−a²` is nonzero (it is a root of unity).
- **How**: Rewrite by `transformed_leading` and use `zpow_ne_zero` with `ζₘ ≠ 0` from `zeta_isPrimitiveRoot`.
- **Hypotheses**: none.
- **Uses from project**: [`transformed_leading`, `transformedJSeries`, `zeta`, `zeta_isPrimitiveRoot`, `CoxMatrix`]
- **Used by**: `cox_a_le`
- **Visibility**: private
- **Lines**: 192–195 (proof 2 lines)
- **Notes**: none

### `lemma cox_a_le`
- **Type**: `private lemma cox_a_le {m : ℕ+} {sigma tau : CoxMatrix m} (h : transformedJSeries (zeta m) sigma = transformedJSeries (zeta m) tau) : sigma.a ≤ tau.a`
- **What**: If two Cox matrices have equal transformed `j`-series, then `σ.a ≤ τ.a` — comparison of the pole orders `−a²` of the two Laurent expansions.
- **How**: The coefficient of the common series at `−σ.a²` is nonzero (`transformed_leading_ne`); by `transformedJSeries_coeff` its nonvanishing for `τ` forces `τ.a² ∣ σ.a²` and `−τ.a² ≤ −σ.a²`, whence `σ.a ≤ τ.a` by positivity (`a_pos`) and `nlinarith`.
- **Hypotheses**: equality of the two transformed series.
- **Uses from project**: [`transformedJSeries`, `transformedJSeries_coeff`, `transformed_leading_ne`, `zeta`, `CoxMatrix` (field `a_pos`)]
- **Used by**: `transformed_injective`
- **Visibility**: private
- **Lines**: 197–210 (proof 12 lines)
- **Notes**: none

### `lemma transformed_phase`
- **Type**: `private lemma transformed_phase {m : ℕ+} {sigma tau : CoxMatrix m} (h : transformedJSeries (zeta m) sigma = transformedJSeries (zeta m) tau) (ha : sigma.a = tau.a) : zeta m ^ (-(sigma.a * sigma.b : ℤ)) = zeta m ^ (-(sigma.a * tau.b : ℤ))` (exponents as in source)
- **What**: Two Cox matrices with equal series and equal `a` have equal leading phases `ζₘ^(−ab)`.
- **How**: A `calc` chain through the leading coefficients: both sides equal the common series' coefficient at `−a²` by `transformed_leading` applied to `σ` and `τ`.
- **Hypotheses**: equal series; `sigma.a = tau.a`.
- **Uses from project**: [`transformed_leading`, `transformedJSeries`, `zeta`, `CoxMatrix`]
- **Used by**: `transformed_injective`
- **Visibility**: private
- **Lines**: 212–224 (proof 8 lines)
- **Notes**: none

### `lemma cox_b_eq`
- **Type**: `private lemma cox_b_eq {m : ℕ+} {sigma tau : CoxMatrix m} (hd : sigma.d = tau.d) (hphase : zeta m ^ (-(sigma.a*sigma.b : ℤ)) = zeta m ^ (-(sigma.a*tau.b : ℤ))) : sigma.b = tau.b`
- **What**: Equal leading phases and equal `d` force equal `b`-entries: the phase `ζₘ^(−ab)` determines `b` within its range `0 ≤ b < d`.
- **How**: The phase equality gives `ζₘ^(x−y) = 1`, so `m ∣ a(τ.b − σ.b)` by `IsPrimitiveRoot.zpow_eq_one_iff_dvd`; since `m = a·d` (the `determinant` field) and `a ≠ 0`, cancellation (`mul_dvd_mul_iff_left`) yields `d ∣ τ.b − σ.b`, and the bounds `0 ≤ b < d` (fields `b_lt`, `d_pos`) force the quotient to be `0` by a sign/size case analysis with `omega`.
- **Hypotheses**: `sigma.d = tau.d`; equal phases.
- **Uses from project**: [`zeta`, `zeta_isPrimitiveRoot`, `CoxMatrix` (fields `a_pos`, `b_lt`, `d_pos`, `determinant`)]
- **Used by**: `transformed_injective`
- **Visibility**: private
- **Lines**: 226–268 (proof 41 lines)
- **Notes**: proof >30 lines (41)

### `theorem transformed_injective`
- **Type**: `private theorem transformed_injective (m : ℕ+) : Function.Injective (transformedJSeries (zeta m) : CoxMatrix m → LaurentSeries ℂ)`
- **What**: Distinct Cox matrices of level `m` have distinct transformed `j`-expansions — the Laurent-series-level distinctness of the conjugates (Cox's argument that the `Φₘ` factors are distinct).
- **How**: From equal series: `a` agrees by antisymmetry of `cox_a_le` in both directions; `d` agrees since `a·d = m` (field `determinant`, `Nat.eq_of_mul_eq_mul_left`); `b` agrees by `cox_b_eq` fed with `transformed_phase`. Conclude with `CoxMatrix.toFin_injective`.
- **Hypotheses**: none.
- **Uses from project**: [`transformedJSeries`, `cox_a_le`, `cox_b_eq`, `transformed_phase`, `zeta`, `CoxMatrix.toFin`, `CoxMatrix.toFin_injective` (XYin.PhD.Cox.CoxMatrices.Basic), `CoxMatrix` (fields `a_pos`, `determinant`)]
- **Used by**: `conjugate_injective`
- **Visibility**: private
- **Lines**: 270–279 (proof 9 lines)
- **Notes**: none

### `theorem conjugate_injective`
- **Type**: `private theorem conjugate_injective (m : ℕ+) : Function.Injective (fun sigma : CoxMatrix m ↦ fun tau : ℍ ↦ j (sigma.act tau))`
- **What**: Distinct Cox matrices give distinct conjugate functions `τ ↦ j(στ)` on the upper half-plane — distinctness at the level of functions (specializations can collide at CM points, hence the functional formulation).
- **How**: Apply the Laurent `q`-expansion functor: `laurentqExpansion_coxAction` identifies the expansion of `j ∘ σ.act` (with period `m`) with `transformedJSeries (zeta m) σ`, so equal functions give equal series, and `transformed_injective` finishes.
- **Hypotheses**: none.
- **Uses from project**: [`transformed_injective`, `laurentqExpansion_coxAction` (XYin.PhD.Cox.CoxMatrices.LaurentExpansion), `UpperHalfPlane.laurentqExpansion` (XYin.PhD.LaurentQExpansion.LaurentQExpansion), `j`, `CoxMatrix.act`, `CoxMatrix`]
- **Used by**: `rightCosetFunction_injective`
- **Visibility**: private
- **Lines**: 281–286 (proof 5 lines)
- **Notes**: none

### `lemma rightCosetEval_mdifferentiable`
- **Type**: `private lemma rightCosetEval_mdifferentiable (m : ℕ+) (c : Gamma0RightCosets m) : MDiff (rightCosetEval m c)`
- **What**: Each right-coset conjugate `τ ↦ j_m(γτ)` (with `j_m = levelJ m` the level-`m` function `j(mτ)`) is holomorphic on ℍ.
- **How**: `levelJ m` is MDifferentiable via `jN_differentiableAt` transported through `UpperHalfPlane.mdifferentiable_iff`; composing with the holomorphic Möbius action `sl2_mdifferentiable` and inducting over the coset (`Quotient.inductionOn`, `rightCosetEval_mk`) gives the claim.
- **Hypotheses**: none.
- **Uses from project**: [`Gamma0RightCosets`, `rightCosetEval`, `rightCosetEval_mk` (XYin.PhD.Cox.CoxMatrices.Basic), `levelJ` (XYin.PhD.Cox.ModularFunction), `jN_differentiableAt` (XYin.PhD.jFunction.jLevelN), `sl2_mdifferentiable`]
- **Used by**: `rightCosetFunction`
- **Visibility**: private
- **Lines**: 288–295 (proof 7 lines)
- **Notes**: none

### `def rightCosetFunction`
- **Type**: `def rightCosetFunction (m : ℕ+) (c : Gamma0RightCosets m) : HolomorphicFunction := ⟨rightCosetEval m c, rightCosetEval_mdifferentiable m c⟩`
- **What**: The conjugate function indexed by a right coset of `Γ₀(m)`, bundled as a holomorphic function — a well-defined root of the modular polynomial viewed in the function ring.
- **How**: Subtype packaging with the holomorphy lemma.
- **Hypotheses**: none.
- **Uses from project**: [`HolomorphicFunction`, `rightCosetEval`, `rightCosetEval_mdifferentiable`, `Gamma0RightCosets`]
- **Used by**: `rightCosetFunction_injective`, `rightCosetRoot`
- **Visibility**: public
- **Lines**: 297–299
- **Notes**: none

### `theorem rightCosetFunction_injective`
- **Type**: `(m : ℕ+) : Function.Injective (rightCosetFunction m)`
- **What**: Distinct right cosets of `Γ₀(m)` give distinct holomorphic conjugate functions — the function-level separation of the `deg Φₘ` roots.
- **How**: Transport both cosets back to Cox matrices along the surjection underlying `coxMatrixEquivRightCosets`; `rightCosetEval_equiv` rewrites the coset evaluation as `j(σ·)`, and `conjugate_injective` separates the matrices, hence the cosets.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetFunction`, `conjugate_injective`, `coxMatrixEquivRightCosets`, `rightCosetEval_equiv` (XYin.PhD.Cox.CoxMatrices.Basic), `HolomorphicFunction`, `Gamma0RightCosets`, `CoxMatrix`]
- **Used by**: `rightCosetRoot_injective`
- **Visibility**: public
- **Lines**: 301–311 (proof 10 lines)
- **Notes**: none

### `def rightCosetRoot`
- **Type**: `def rightCosetRoot (m : ℕ+) (c : Gamma0RightCosets m) : FunctionField := algebraMap HolomorphicFunction FunctionField (rightCosetFunction m c)`
- **What**: A right-coset conjugate viewed as an element of the function field — the incarnation of a root of `Φₘ(Y, ·)` over `ℂ(j)`.
- **How**: Image of `rightCosetFunction` under the localization map.
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetFunction`, `FunctionField`, `HolomorphicFunction`, `Gamma0RightCosets`]
- **Used by**: `rightCosetRoot_injective`, `precompAlgEquiv_rightCosetRoot`
- **Visibility**: public
- **Lines**: 313–315
- **Notes**: none

### `theorem rightCosetRoot_injective`
- **Type**: `(m : ℕ+) : Function.Injective (rightCosetRoot m)`
- **What**: Distinct right cosets remain distinct as function-field elements: the modular polynomial has `[SL₂(ℤ) : Γ₀(m)]` distinct roots in the function field.
- **How**: Compose `rightCosetFunction_injective` with injectivity of the fraction-field inclusion (`IsFractionRing.injective`).
- **Hypotheses**: none.
- **Uses from project**: [`rightCosetRoot`, `rightCosetFunction_injective`, `HolomorphicFunction`, `FunctionField`]
- **Used by**: unused in file (API for irreducibility/Galois arguments downstream)
- **Visibility**: public
- **Lines**: 317–320 (proof 2 lines)
- **Notes**: none

### `theorem precompAlgEquiv_rightCosetRoot`
- **Type**: `(m : ℕ+) (delta : SL(2, ℤ)) (c : Gamma0RightCosets m) : precompAlgEquiv delta (rightCosetRoot m c) = rightCosetRoot m (rightCosetMul m delta c)`
- **What**: The `ℂ(j)`-automorphism of precomposition by `δ` permutes the conjugate roots by right multiplication on `Γ₀(m)`-cosets — the transitive Galois-type action on the roots of the modular polynomial.
- **How**: Reduce to the subring via `IsFractionRing.ringEquivOfRingEquiv_algebraMap`, then pointwise the claim is exactly `rightCosetEval_smul`: `(j_m ∘ γ)(δτ) = j_m((γδ)τ)`.
- **Hypotheses**: none.
- **Uses from project**: [`precompAlgEquiv`, `precomp`, `rightCosetRoot`, `rightCosetMul`, `rightCosetEval_smul` (XYin.PhD.Cox.CoxMatrices.Basic), `HolomorphicFunction`, `FunctionField`, `Gamma0RightCosets`]
- **Used by**: unused in file (terminal API; consumed by the irreducibility development)
- **Visibility**: public
- **Lines**: 322–333 (proof 8 lines)
- **Notes**: none

### File Summary
- Total declarations: 30 (13 defs [incl. 2 abbrevs], 15 lemmas/theorems, 2 instances, 0 tactic/meta decls)
- Key API (used by 3+ others): `HolomorphicFunction` (15+ users), `FunctionField` (9 users), `evalJFracPoly` (6 users), `ratFuncEvalJ` (5 users), `precomp` (4 users), `transformedJSeries`-based lemmas chain, `Gamma0RightCosets` (external, used by 6), `rightCosetRoot`/`rightCosetFunction` (2–3 users each)
- Unused declarations (not used by anything in this file): `ratFuncEvalJ_injective`, `algebraMap_ratFunc`, `rightCosetRoot_injective`, `precompAlgEquiv_rightCosetRoot` (all terminal/downstream API)
- Declarations with sorry: []
- Declarations with set_option: []
- Proofs >30 lines: [`cox_b_eq` (41 proof lines)]
