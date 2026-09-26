# Inventory: XYin/PhD/IntegralPowerSeries/IntegralPowerSeries.lean  (229 lines)

Defines the predicate `HasCoeffsIn R A x` — a power series `x ∈ A⟦X⟧` lies in the image of `R⟦X⟧` under coefficientwise `algebraMap R A` — as membership in the range subalgebra of `PowerSeries.mapAlgHom`, with closure lemmas and a coefficientwise characterisation; then specialises through three abbrev layers to `IntegralPowerSeries.IsIntegralPowerSeries` (complex power series with integer coefficients), used by `jFunction/jfunction.lean`, `jFunction/Deltaqexpansions.lean` and `qExpansion_tactic/link.lean`. Also contains an (unused) `R`-submodule of modular forms with `R`-integral q-expansions and a scoped `Module R (ModularForm Γ k)` instance. Imported by `XYin.lean`, `jfunction.lean`, `Deltaqexpansions.lean`.

## Declarations

### `def powerSeriesMapAlgHom`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] : PowerSeries R →ₐ[R] PowerSeries A := PowerSeries.mapAlgHom (Algebra.ofId R A)`
- **What**: Coefficientwise base change `R⟦X⟧ → A⟦X⟧` as an `R`-algebra hom.
- **How**: mathlib `PowerSeries.mapAlgHom` (RingTheory/PowerSeries/Basic.lean:728) applied to `Algebra.ofId R A`.
- **Hypotheses**: `A` an `R`-algebra.
- **Uses from project**: []
- **Used by**: powerSeriesMapAlgHom_apply, powerSeriesMapSubalgebra, coeToComplexPowerSeries.ringHom, map_toHasCoeffsInPowerSeries; externally link.lean:159, 165, 371 (always unfolded by `simpa [… , powerSeriesMapAlgHom]`)
- **Visibility**: public
- **Lines**: 33–35
- **Notes**: one-line wrapper around a single mathlib call; external users immediately unfold it — evidence it adds friction.

### `@[simp] lemma powerSeriesMapAlgHom_apply`
- **Type**: `(R A) … (f : PowerSeries R) : powerSeriesMapAlgHom R A f = f.map (algebraMap R A)`
- **What**: Unfolds the alg hom to `PowerSeries.map`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: powerSeriesMapAlgHom
- **Used by**: hasCoeffsIn_iff_coeff, hasCoeffsIn_C_algebraMap (via `simp`)
- **Visibility**: public
- **Lines**: 38–40
- **Notes**: `@[simp]`; 0 external references.

### `noncomputable def powerSeriesMapSubalgebra`
- **Type**: `(R A) … : Subalgebra R (PowerSeries A) := (powerSeriesMapAlgHom R A).range`
- **What**: The `R`-subalgebra of `A⟦X⟧` of base-changed series.
- **How**: `AlgHom.range`.
- **Hypotheses**: none.
- **Uses from project**: powerSeriesMapAlgHom
- **Used by**: powerSeriesMapSubmodule, HasCoeffsIn, hasCoeffsIn_zero/one/add/mul/smul/neg/sub, RIntegralCPowerSeriesSubring
- **Visibility**: public
- **Lines**: 43–44
- **Notes**: 0 external references. Mathlib polynomial analogue: `Polynomial.lifts f : Subsemiring S[X]` (Algebra/Polynomial/Lifts.lean:60) and `liftsRing` (:209); no `PowerSeries.lifts` in mathlib (grep `PowerSeries.*lifts`: none).

### `noncomputable def powerSeriesMapSubmodule`
- **Type**: `(R A) … : Submodule R (PowerSeries A) := (powerSeriesMapSubalgebra R A).toSubmodule`
- **What**: The same set as an `R`-submodule.
- **How**: `Subalgebra.toSubmodule`.
- **Hypotheses**: none.
- **Uses from project**: powerSeriesMapSubalgebra
- **Used by**: mem_powerSeriesMapSubmodule_iff (only)
- **Visibility**: public
- **Lines**: 47–48
- **Notes**: 0 external references; junk candidate (its only user is itself unused).

### `def HasCoeffsIn`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] (x : PowerSeries A) : Prop := x ∈ powerSeriesMapSubalgebra R A`
- **What**: `x` has all coefficients in the image of `algebraMap R A` (as a membership predicate).
- **How**: definition.
- **Hypotheses**: none.
- **Uses from project**: powerSeriesMapSubalgebra
- **Used by**: hasCoeffsIn_iff_coeff, mem_powerSeriesMapSubmodule_iff, hasCoeffsIn_zero/one/add/mul/smul/neg/sub/C_algebraMap, IsRIntegralCPowerSeries, IsIntegralCPowerSeries, toHasCoeffsInPowerSeries, map_toHasCoeffsInPowerSeries, modularFormQExpansionSubmodule
- **Visibility**: public
- **Lines**: 51–52
- **Notes**: 0 direct external references (all external use goes through the `IsIntegralPowerSeries` abbrev). Being a `def` (not `abbrev`) over a `Subalgebra` membership means every closure lemma below is a one-line re-export of `Subalgebra.*_mem`.

### `lemma hasCoeffsIn_iff_coeff`
- **Type**: `(R A) … (f : PowerSeries A) : HasCoeffsIn R A f ↔ ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n f = algebraMap R A r`
- **What**: Coefficientwise characterisation of `HasCoeffsIn`.
- **How**: `→`: from a preimage `g`, `PowerSeries.coeff_map`; `←`: `choose` the coefficients, build `PowerSeries.mk r`, `PowerSeries.ext`.
- **Hypotheses**: none.
- **Uses from project**: HasCoeffsIn, powerSeriesMapAlgHom_apply (simp)
- **Used by**: isRIntegralCPowerSeries_iff_coeff
- **Visibility**: public
- **Lines**: 56–64, proof ≈ 6 lines
- **Notes**: exact `PowerSeries` analogue of mathlib `Polynomial.lifts_iff_coeff_lifts` (Lifts.lean:72: `p ∈ lifts f ↔ ∀ n, p.coeff n ∈ Set.range f`); the `Set.range` phrasing is the mathlib-idiomatic one.

### `lemma mem_powerSeriesMapSubmodule_iff`
- **Type**: `(R A) … (x : PowerSeries A) : x ∈ powerSeriesMapSubmodule R A ↔ HasCoeffsIn R A x`
- **What**: Submodule membership is the predicate.
- **How**: `Iff.rfl`.
- **Hypotheses**: none.
- **Uses from project**: powerSeriesMapSubmodule, HasCoeffsIn
- **Used by**: unused in file; 0 external
- **Visibility**: public
- **Lines**: 66–69
- **Notes**: junk candidate.

### `lemma hasCoeffsIn_zero`
- **Type**: `(R A) … : HasCoeffsIn R A 0`
- **What**: `0` has coefficients in `R`.
- **How**: `Subalgebra.zero_mem`.
- **Hypotheses**: none.
- **Uses from project**: HasCoeffsIn, powerSeriesMapSubalgebra
- **Used by**: modularFormQExpansionSubmodule
- **Visibility**: public
- **Lines**: 71–73
- **Notes**: one-liner; 0 external.

### `lemma hasCoeffsIn_one`
- **Type**: `(R A) … : HasCoeffsIn R A 1`
- **What**: `1` has coefficients in `R`.
- **How**: `Subalgebra.one_mem`.
- **Hypotheses**: none.
- **Uses from project**: HasCoeffsIn, powerSeriesMapSubalgebra
- **Used by**: unused in file; 0 external
- **Visibility**: public
- **Lines**: 75–77
- **Notes**: one-liner.

### `lemma hasCoeffsIn_add`
- **Type**: `(R A) … {x y} (hx : HasCoeffsIn R A x) (hy : HasCoeffsIn R A y) : HasCoeffsIn R A (x + y)`
- **What**: closure under addition.
- **How**: `Subalgebra.add_mem`.
- **Hypotheses**: both summands have coefficients in `R`.
- **Uses from project**: HasCoeffsIn, powerSeriesMapSubalgebra
- **Used by**: modularFormQExpansionSubmodule
- **Visibility**: public
- **Lines**: 79–82
- **Notes**: one-liner; 0 external.

### `lemma hasCoeffsIn_mul`
- **Type**: `(R A) … {x y} (hx) (hy) : HasCoeffsIn R A (x * y)`
- **What**: closure under multiplication.
- **How**: `Subalgebra.mul_mem`.
- **Hypotheses**: both factors have coefficients in `R`.
- **Uses from project**: HasCoeffsIn, powerSeriesMapSubalgebra
- **Used by**: unused in file; externally jfunction.lean:311
- **Visibility**: public
- **Lines**: 84–87
- **Notes**: one-liner.

### `lemma hasCoeffsIn_smul`
- **Type**: `(R A) … (r : R) {x} (hx : HasCoeffsIn R A x) : HasCoeffsIn R A (r • x)`
- **What**: closure under `R`-scalars.
- **How**: `Subalgebra.smul_mem`.
- **Hypotheses**: `x` has coefficients in `R`.
- **Uses from project**: HasCoeffsIn, powerSeriesMapSubalgebra
- **Used by**: modularFormQExpansionSubmodule
- **Visibility**: public
- **Lines**: 89–92
- **Notes**: one-liner; 0 external.

### `lemma hasCoeffsIn_neg`
- **Type**: `(R A) [CommRing R] [Ring A] [Algebra R A] {x} (hx) : HasCoeffsIn R A (-x)`
- **What**: closure under negation.
- **How**: `Subalgebra.neg_mem`.
- **Hypotheses**: ring setting.
- **Uses from project**: HasCoeffsIn, powerSeriesMapSubalgebra
- **Used by**: unused in file; 0 external
- **Visibility**: public
- **Lines**: 94–96
- **Notes**: one-liner.

### `lemma hasCoeffsIn_sub`
- **Type**: `(R A) [CommRing R] [Ring A] [Algebra R A] {x y} (hx) (hy) : HasCoeffsIn R A (x - y)`
- **What**: closure under subtraction.
- **How**: `Subalgebra.sub_mem`.
- **Hypotheses**: ring setting.
- **Uses from project**: HasCoeffsIn, powerSeriesMapSubalgebra
- **Used by**: unused in file; 0 external
- **Visibility**: public
- **Lines**: 98–100
- **Notes**: one-liner.

### `lemma hasCoeffsIn_C_algebraMap`
- **Type**: `(R A) … (r : R) : HasCoeffsIn R A (PowerSeries.C (algebraMap R A r))`
- **What**: Constants from `R` have coefficients in `R`.
- **How**: witness `PowerSeries.C r`, `PowerSeries.map_C` (Basic.lean:459).
- **Hypotheses**: none.
- **Uses from project**: HasCoeffsIn, powerSeriesMapAlgHom_apply (simp)
- **Used by**: unused in file; 0 external
- **Visibility**: public
- **Lines**: 102–104
- **Notes**: junk candidate; also the natural `hasCoeffsIn_algebraMap : HasCoeffsIn R A (algebraMap R A⟦X⟧ r)` (= `Subalgebra.algebraMap_mem`) is what one wants.

### `abbrev coeToComplexPowerSeries.ringHom`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] : PowerSeries R →+* PowerSeries ℂ := (powerSeriesMapAlgHom R ℂ).toRingHom`
- **What**: The coefficientwise coercion `R⟦X⟧ → ℂ⟦X⟧` as a ring hom.
- **How**: `AlgHom.toRingHom`.
- **Hypotheses**: `ℂ` an `R`-algebra.
- **Uses from project**: powerSeriesMapAlgHom
- **Used by**: coeToComplexPowerSeries_of_toRIntegralCPowerSeries, coeTo_of_toIntegralPowerSeries; externally 10 refs (link.lean, jfunction.lean, Deltaqexpansions.lean)
- **Visibility**: public
- **Lines**: 107–108
- **Notes**: definitionally `PowerSeries.map (algebraMap R ℂ)` (mathlib `PowerSeries.map : R⟦X⟧ →+* S⟦X⟧`, Basic.lean:444) — a pure rename; external callers unfold it (`simpa [coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom]`, link.lean:159/165/371). The name is a dotted `coeToComplexPowerSeries.ringHom` with no `coeToComplexPowerSeries` declaration — flagged SHORT collision (`ringHom`) in `_mathlib-collisions.tsv`.

### `noncomputable abbrev RIntegralCPowerSeriesSubring`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] : Subring (PowerSeries ℂ) := (powerSeriesMapSubalgebra R ℂ).toSubring`
- **What**: Subring of `ℂ⟦X⟧` of `R`-integral series.
- **How**: `Subalgebra.toSubring`.
- **Hypotheses**: none.
- **Uses from project**: powerSeriesMapSubalgebra
- **Used by**: IntegralPowerSeriesSubring
- **Visibility**: public
- **Lines**: 111–112
- **Notes**: 0 external.

### `abbrev IsRIntegralCPowerSeries`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] (x : PowerSeries ℂ) : Prop := HasCoeffsIn R ℂ x`
- **What**: `R`-integral complex power series.
- **How**: abbrev.
- **Hypotheses**: none.
- **Uses from project**: HasCoeffsIn
- **Used by**: isRIntegralCPowerSeries_iff_coeff, toRIntegralCPowerSeries, coeToComplexPowerSeries_of_toRIntegralCPowerSeries
- **Visibility**: public
- **Lines**: 115–116
- **Notes**: 0 external; intermediate layer.

### `abbrev IsIntegralCPowerSeries`
- **Type**: `(x : PowerSeries ℂ) : Prop := HasCoeffsIn ℤ ℂ x`
- **What**: ℤ-integral complex power series.
- **How**: abbrev.
- **Hypotheses**: none.
- **Uses from project**: HasCoeffsIn
- **Used by**: IntegralPowerSeries.IsIntegralPowerSeries
- **Visibility**: public
- **Lines**: 119–120
- **Notes**: 0 external; intermediate layer (note it bypasses `IsRIntegralCPowerSeries ℤ`, so `int_iff` needs a `simpa` to reconnect).

### `lemma isRIntegralCPowerSeries_iff_coeff`
- **Type**: `(R) … (f : PowerSeries ℂ) : IsRIntegralCPowerSeries R f ↔ ∀ n, ∃ r : R, PowerSeries.coeff n f = algebraMap R ℂ r`
- **What**: coefficientwise characterisation, ℂ-specialised.
- **How**: `simpa` from `hasCoeffsIn_iff_coeff`.
- **Hypotheses**: none.
- **Uses from project**: IsRIntegralCPowerSeries, hasCoeffsIn_iff_coeff
- **Used by**: IntegralPowerSeries.int_iff
- **Visibility**: public
- **Lines**: 122–125
- **Notes**: 0 external; pure re-export.

### `noncomputable def toHasCoeffsInPowerSeries`
- **Type**: `(R A) … {f : PowerSeries A} (hf : HasCoeffsIn R A f) : PowerSeries R := Classical.choose hf`
- **What**: A (noncanonical) lift of `f` to `R⟦X⟧`.
- **How**: `Classical.choose` on the range membership.
- **Hypotheses**: `f` has coefficients in `R`.
- **Uses from project**: HasCoeffsIn
- **Used by**: map_toHasCoeffsInPowerSeries, toRIntegralCPowerSeries
- **Visibility**: public
- **Lines**: 128–130
- **Notes**: 0 external. When `algebraMap R A` is injective the lift is canonical: `PowerSeries.mk fun n ↦ (hasCoeffsIn_iff_coeff …).1 hf n |>.choose` — or better, no `choose` at all via `PowerSeries.map` injectivity (`PowerSeries.map_injective`). No `coeff_toHasCoeffsInPowerSeries` lemma.

### `lemma map_toHasCoeffsInPowerSeries`
- **Type**: `(R A) … {f} (hf : HasCoeffsIn R A f) : powerSeriesMapAlgHom R A (toHasCoeffsInPowerSeries R A hf) = f`
- **What**: The lift maps back to `f`.
- **How**: `Classical.choose_spec`.
- **Hypotheses**: as above.
- **Uses from project**: powerSeriesMapAlgHom, toHasCoeffsInPowerSeries, HasCoeffsIn
- **Used by**: coeToComplexPowerSeries_of_toRIntegralCPowerSeries
- **Visibility**: public
- **Lines**: 132–135
- **Notes**: 0 external.

### `noncomputable def toRIntegralCPowerSeries`
- **Type**: `(R) [CommRing R] [Algebra R ℂ] {f : PowerSeries ℂ} (hf : IsRIntegralCPowerSeries R f) : PowerSeries R := toHasCoeffsInPowerSeries R ℂ hf`
- **What**: ℂ-specialised lift.
- **How**: delegation.
- **Hypotheses**: as above.
- **Uses from project**: IsRIntegralCPowerSeries, toHasCoeffsInPowerSeries
- **Used by**: coeToComplexPowerSeries_of_toRIntegralCPowerSeries, IntegralPowerSeries.toIntegralPowerSeries
- **Visibility**: public
- **Lines**: 138–140
- **Notes**: 0 external; intermediate layer.

### `lemma coeToComplexPowerSeries_of_toRIntegralCPowerSeries`
- **Type**: `(R) … {f} (hf : IsRIntegralCPowerSeries R f) : coeToComplexPowerSeries.ringHom R (toRIntegralCPowerSeries R hf) = f`
- **What**: ℂ-specialised round trip.
- **How**: `map_toHasCoeffsInPowerSeries`.
- **Hypotheses**: as above.
- **Uses from project**: coeToComplexPowerSeries.ringHom, toRIntegralCPowerSeries, IsRIntegralCPowerSeries, map_toHasCoeffsInPowerSeries
- **Used by**: IntegralPowerSeries.coeTo_of_toIntegralPowerSeries
- **Visibility**: public
- **Lines**: 142–145
- **Notes**: 0 external; intermediate layer.

### `noncomputable abbrev IntegralPowerSeries.IntegralPowerSeriesSubring`
- **Type**: `Subring (PowerSeries ℂ) := RIntegralCPowerSeriesSubring ℤ`
- **What**: Subring of complex power series with integer coefficients.
- **How**: specialisation.
- **Hypotheses**: none.
- **Uses from project**: RIntegralCPowerSeriesSubring
- **Used by**: unused in file; externally Deltaqexpansions.lean:80 (`IntegralPowerSeriesSubring.pow_mem`)
- **Visibility**: public
- **Lines**: 150–151
- **Notes**: its only use is to get `pow_mem` — i.e. `hasCoeffsIn_pow` is missing.

### `abbrev IntegralPowerSeries.IsIntegralPowerSeries`
- **Type**: `(x : PowerSeries ℂ) : Prop := IsIntegralCPowerSeries x`
- **What**: complex power series with integer coefficients (the name used throughout the project).
- **How**: abbrev.
- **Hypotheses**: none.
- **Uses from project**: IsIntegralCPowerSeries
- **Used by**: int_iff, toIntegralPowerSeries, coeTo_of_toIntegralPowerSeries, IsIntegralPowerSeriesmod; externally 10 refs (jfunction, Deltaqexpansions, link)
- **Visibility**: public
- **Lines**: 154–155
- **Notes**: third abbrev layer over `HasCoeffsIn ℤ ℂ`.

### `lemma IntegralPowerSeries.int_iff`
- **Type**: `(f : PowerSeries ℂ) : IsIntegralPowerSeries f ↔ ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = z`
- **What**: Integrality ⇔ every coefficient is an integer cast.
- **How**: `simpa` from `isRIntegralCPowerSeries_iff_coeff ℤ` (uses `Int.cast` = `algebraMap ℤ ℂ`).
- **Hypotheses**: none.
- **Uses from project**: IsIntegralPowerSeries, isRIntegralCPowerSeries_iff_coeff
- **Used by**: IsIntegralPowerSeriesmod; externally Deltaqexpansions.lean:55, 63, jfunction.lean:206
- **Visibility**: public
- **Lines**: 158–160
- **Notes**: name too short/unqualified for mathlib (`isIntegralPowerSeries_iff_coeff`).

### `noncomputable abbrev IntegralPowerSeries.toIntegralPowerSeries`
- **Type**: `{f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) : PowerSeries ℤ := toRIntegralCPowerSeries ℤ hf`
- **What**: integer-coefficient lift.
- **How**: specialisation.
- **Hypotheses**: `f` integral.
- **Uses from project**: IsIntegralPowerSeries, toRIntegralCPowerSeries
- **Used by**: coeTo_of_toIntegralPowerSeries, IsIntegralPowerSeriesmod; externally 9 refs
- **Visibility**: public
- **Lines**: 163–165
- **Notes**: none.

### `lemma IntegralPowerSeries.coeTo_of_toIntegralPowerSeries`
- **Type**: `{f} (hf : IsIntegralPowerSeries f) : coeToComplexPowerSeries.ringHom ℤ (toIntegralPowerSeries hf) = f`
- **What**: round trip for the integer lift.
- **How**: `simpa` from `coeToComplexPowerSeries_of_toRIntegralCPowerSeries ℤ`.
- **Hypotheses**: as above.
- **Uses from project**: coeToComplexPowerSeries.ringHom, toIntegralPowerSeries, IsIntegralPowerSeries, coeToComplexPowerSeries_of_toRIntegralCPowerSeries
- **Used by**: IsIntegralPowerSeriesmod; externally 10 refs
- **Visibility**: public
- **Lines**: 167–169
- **Notes**: the coefficient form `((toIntegralPowerSeries hf).coeff n : ℂ) = f.coeff n` is what callers need (derived inline at L180–181 via `congrArg`); a `coeff_toIntegralPowerSeries` simp lemma is missing.

### `lemma IntegralPowerSeries.IsIntegralPowerSeriesmod`
- **Type**: `{c : ℤ} (hc : c ≠ 0) {f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) (hmod : ∀ n, Int.ModEq c ((toIntegralPowerSeries hf).coeff n) 0) : IsIntegralPowerSeries ((1 / c : ℂ) • f)`
- **What**: Divisibility descent: if every integer coefficient of an integral series is divisible by `c ≠ 0`, then `f / c` is again integral.
- **How**: `int_iff`; for each `n`, `Int.modEq_zero_iff_dvd` yields `coeff n g = c * t`; transport to `ℂ` via `coeTo_of_toIntegralPowerSeries` (`congrArg (PowerSeries.coeff n)`); `simp` with `hc` cancels `c`.
- **Hypotheses**: `c ≠ 0`; `f` integral; all lifted coefficients `≡ 0 [ZMOD c]`.
- **Uses from project**: int_iff, toIntegralPowerSeries, coeTo_of_toIntegralPowerSeries, IsIntegralPowerSeries
- **Used by**: unused in file; externally Deltaqexpansions.lean:288
- **Visibility**: public
- **Lines**: 173–182, proof ≈ 7 lines
- **Notes**: name is not mathlib-style (`isIntegralPowerSeries_inv_smul_of_dvd`); hypothesis phrased as `Int.ModEq c _ 0` where `c ∣ _` is idiomatic; `(1 / c : ℂ) • f` should be `(c : ℂ)⁻¹ • f`.

### `noncomputable scoped instance IntegralPowerSeries.modularFormModuleofIsScalarTower`
- **Type**: `(R : Type*) [Semiring R] [Module R ℂ] [IsScalarTower R ℂ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [Γ.HasDetOne] : Module R (ModularForm Γ k)`
- **What**: `R`-module structure on modular forms by restriction of scalars along `R → ℂ`.
- **How**: `Function.Injective.module R ModularForm.coeHom DFunLike.coe_injective (fun _ _ => rfl)` on top of mathlib's `SMul α (ModularForm Γ k)` (`instSMulℂ`, NumberTheory/ModularForms/Basic.lean:270) — verbatim the pattern of mathlib's `Module ℂ` instance (Basic.lean:327).
- **Hypotheses**: `R` acts on `ℂ` compatibly; `Γ` has determinant one.
- **Uses from project**: []
- **Used by**: modularFormQExpansionSubmodule (instance resolution for `Submodule R (ModularForm Γ k)`)
- **Visibility**: scoped (`IntegralPowerSeries`)
- **Lines**: 191–194
- **Notes**: mathlib has only `Module ℝ` and `Module ℂ` (Basic.lean:324, 327) although it already has the general `SMul α`; this generic `Module α` is a genuine mathlib gap (docstring's diamond worry for `ℕ`/`ℤ` is real — mathlib avoids it the same way). 0 external references.

### `lemma IntegralPowerSeries.qExpansion_smul_algebra`
- **Type**: `(R : Type*) [CommSemiring R] [Algebra R ℂ] {Γ} {k} [Γ.HasDetOne] {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (r : R) (f : ModularForm Γ k) : qExpansion h (r • f) = algebraMap R ℂ r • qExpansion h f`
- **What**: q-expansion commutes with `R`-scalars acting through `algebraMap`.
- **How**: `simpa` from mathlib `ModularForm.qExpansion_smul` (QExpansion.lean:556) at `a := algebraMap R ℂ r` (uses `algebraMap_smul`).
- **Hypotheses**: `0 < h`, `h` a strict period of `Γ`.
- **Uses from project**: []
- **Used by**: modularFormQExpansionSubmodule
- **Visibility**: public
- **Lines**: 198–202
- **Notes**: 0 external.

### `def IntegralPowerSeries.modularFormQExpansionSubmodule`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] {Γ} [Γ.HasDetOne] (k : ℤ) (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) : Submodule R (ModularForm Γ k)` with carrier `{f | HasCoeffsIn R ℂ (qExpansion h f)}`
- **What**: The `R`-submodule of weight-`k` modular forms whose period-`h` q-expansion has all coefficients in `R`.
- **How**: `zero_mem'` via `UpperHalfPlane.qExpansion_zero` (QExpansion.lean:500) + `hasCoeffsIn_zero`; `add_mem'` via `ModularForm.qExpansion_add` (:564) + `hasCoeffsIn_add`; `smul_mem'` via `qExpansion_smul_algebra` + `hasCoeffsIn_smul` + `Algebra.smul_def`/`PowerSeries.algebraMap_apply` (Basic.lean:721).
- **Hypotheses**: `0 < h`, `h ∈ Γ.strictPeriods`.
- **Uses from project**: HasCoeffsIn, hasCoeffsIn_zero, hasCoeffsIn_add, hasCoeffsIn_smul, qExpansion_smul_algebra, modularFormModuleofIsScalarTower (instance)
- **Used by**: unused in file; 0 external
- **Visibility**: public
- **Lines**: 206–225, proof ≈ 16 lines
- **Notes**: junk/park candidate (unused). Structurally it is `Submodule.comap (qExpansion as R-linear map) (powerSeriesMapSubmodule R ℂ)`; mathlib bundles `qExpansionAddHom` (QExpansion.lean:613) and `qExpansionRingHom` (:621) but no `LinearMap`, which is why the three membership proofs are written by hand.

## File Summary
- Total declarations: 33 (7 defs, 18 lemmas, 1 instance, 7 abbrevs)
- Key API (used by 3+ others in the file): `HasCoeffsIn` (≈17), `powerSeriesMapSubalgebra` (10), `powerSeriesMapAlgHom` (4), `IsIntegralPowerSeries` (4), `coeToComplexPowerSeries.ringHom` (2 in-file, 10 external), `toIntegralPowerSeries` (2 in-file, 9 external)
- Unused declarations (not used by anything in this file): `mem_powerSeriesMapSubmodule_iff`, `hasCoeffsIn_one`, `hasCoeffsIn_mul` (ext 1), `hasCoeffsIn_neg`, `hasCoeffsIn_sub`, `hasCoeffsIn_C_algebraMap`, `IntegralPowerSeriesSubring` (ext 1), `IsIntegralPowerSeriesmod` (ext 1), `modularFormQExpansionSubmodule` (ext 0); zero-external AND zero-in-file: `mem_powerSeriesMapSubmodule_iff`, `hasCoeffsIn_one`, `hasCoeffsIn_neg`, `hasCoeffsIn_sub`, `hasCoeffsIn_C_algebraMap`, `modularFormQExpansionSubmodule`
- Declarations with sorry: none
- Declarations with set_option: none
- Proofs >30 lines: none

## Observations (evidence for the analysis phases — be concrete, cite line numbers)
### Mathlib API candidates
- `HasCoeffsIn R A` (L51) ≡ `x ∈ (PowerSeries.mapAlgHom (Algebra.ofId R A)).range`; the mathlib design for polynomials is `Polynomial.lifts (f : R →+* S) : Subsemiring S[X]` with `mem_lifts` (:63), `lifts_iff_set_range` (:66), `lifts_iff_ringHom_rangeS` (:69), `lifts_iff_coeff_lifts` (:72), `liftsRing` (:209), `mem_lifts_iff_mem_alg` (:224) — all in `Mathlib/Algebra/Polynomial/Lifts.lean`. There is NO `PowerSeries.lifts` in mathlib (grep `lifts` × `PowerSeries`: none). This file is the seed of a `Mathlib/RingTheory/PowerSeries/Lifts.lean`; `hasCoeffsIn_iff_coeff` (L56–64) is `PowerSeries.lifts_iff_coeff_lifts`.
- `coeToComplexPowerSeries.ringHom R` (L107) = `PowerSeries.map (algebraMap R ℂ)` (mathlib `PowerSeries.map : R⟦X⟧ →+* S⟦X⟧`, RingTheory/PowerSeries/Basic.lean:444) — all 10 external uses would work with the mathlib name directly (link.lean:159/165/371 already `simpa [coeToComplexPowerSeries.ringHom, powerSeriesMapAlgHom]` to get there).
- `hasCoeffsIn_zero/one/add/mul/smul/neg/sub` (L71–100): each is `Subalgebra.{zero,one,add,mul,smul,neg,sub}_mem` — if `HasCoeffsIn` were an `abbrev` for the membership these would be unnecessary (`(powerSeriesMapSubalgebra R A).add_mem hx hy` already typechecks against `HasCoeffsIn`).
- `modularFormModuleofIsScalarTower` (L191): mathlib has `SMul α (ModularForm Γ k)` for `[SMul α ℂ] [IsScalarTower α ℂ ℂ] [Γ.HasDetOne]` (ModularForms/Basic.lean:270) but `Module` only for `ℝ`, `ℂ` (:324, :327); the generic `Module α` instance (with `[Module α ℂ] [IsScalarTower α ℂ ℂ]`) is upstreamable verbatim (keep it non-scoped there? mathlib would face the same `ℕ`/`ℤ` diamond, so it would need the same care).
- `qExpansion_smul_algebra` (L198): trivial consequence of `ModularForm.qExpansion_smul` (QExpansion.lean:556); fine as a `simp`-normal-form lemma but no mathlib gap.
- `modularFormQExpansionSubmodule` (L206): would be `Submodule.comap` of an `R`-linear `qExpansion` map if mathlib bundled `qExpansionₗ : ModularForm Γ k →ₗ[ℂ] PowerSeries ℂ` (it has `qExpansionAddHom` :613, `qExpansionRingHom` :621 only).
### Missing API / repeated patterns
- No `hasCoeffsIn_pow` (Deltaqexpansions.lean:80 works around via `IntegralPowerSeriesSubring.pow_mem`), no `hasCoeffsIn_X`, `hasCoeffsIn_algebraMap`, `hasCoeffsIn_map`, `hasCoeffsIn_finset_sum/prod`, `hasCoeffsIn_coeff : HasCoeffsIn R A f → ∃ r, coeff n f = algebraMap r` (the `.1` direction of `hasCoeffsIn_iff_coeff` as a standalone), `hasCoeffsIn_mk`, `hasCoeffsIn_of_injective`-style uniqueness of the lift.
- `toHasCoeffsInPowerSeries` lacks `coeff_toHasCoeffsInPowerSeries : algebraMap R A ((lift).coeff n) = f.coeff n` — re-derived inline at L180–181 (`congrArg (PowerSeries.coeff n) (coeTo_of_toIntegralPowerSeries hf)`), and again in the external users (9 refs to `toIntegralPowerSeries`, 10 to `coeTo_of_toIntegralPowerSeries` — every one of them is presumably this coefficient extraction).
- Three-layer abbrev tower (`HasCoeffsIn ℤ ℂ` → `IsIntegralCPowerSeries` → `IsIntegralPowerSeries`; `toHasCoeffsInPowerSeries` → `toRIntegralCPowerSeries` → `toIntegralPowerSeries`; `map_toHasCoeffsInPowerSeries` → `coeToComplexPowerSeries_of_toRIntegralCPowerSeries` → `coeTo_of_toIntegralPowerSeries`; `hasCoeffsIn_iff_coeff` → `isRIntegralCPowerSeries_iff_coeff` → `int_iff`): the middle layer (`IsRIntegralCPowerSeries`, `RIntegralCPowerSeriesSubring`, `isRIntegralCPowerSeries_iff_coeff`, `toRIntegralCPowerSeries`, `coeToComplexPowerSeries_of_toRIntegralCPowerSeries`, `IsIntegralCPowerSeries`, L107–145, L119–120) has 0 external users and exists only to be re-specialised — collapse to one generic + one `ℤ`-specialised layer.
- `IsIntegralPowerSeriesmod` (L173): statement should use `(c : ℂ)⁻¹ • f` and `c ∣ coeff n`, and generalise to any injective `algebraMap R A` into a field.
### Junk candidates
- `powerSeriesMapSubmodule` + `mem_powerSeriesMapSubmodule_iff` (L47–48, L66–69): no users anywhere.
- `hasCoeffsIn_one`, `hasCoeffsIn_neg`, `hasCoeffsIn_sub`, `hasCoeffsIn_C_algebraMap` (L75–77, 94–104): no users anywhere; one-liners over `Subalgebra` API.
- `modularFormQExpansionSubmodule` + `qExpansion_smul_algebra` + `modularFormModuleofIsScalarTower` (L184–227, the whole `ModularForms` section, 44 lines): no users anywhere in the project.
- `powerSeriesMapAlgHom` (L33–35) and `coeToComplexPowerSeries.ringHom` (L107–108): one-line renames of mathlib `PowerSeries.mapAlgHom`/`PowerSeries.map`.
- Header: "Released under Apache 2.0 license as described in the file LICENSE. Authors: The XYin contributors" (L2–4) is a template placeholder shared by the other PhD files; the `## Main definitions` docstring (L16–22) lists `powerSeriesMapAlgHom` and `modularFormQExpansionSubmodule`, both effectively dead.
### Moral duplicates within this batch
- `hasCoeffsIn_iff_coeff` (L56) / `isRIntegralCPowerSeries_iff_coeff` (L122) / `int_iff` (L158): the same statement at three levels of specialisation, each a `simpa` of the previous.
- `map_toHasCoeffsInPowerSeries` (L132) / `coeToComplexPowerSeries_of_toRIntegralCPowerSeries` (L142) / `coeTo_of_toIntegralPowerSeries` (L167): same.
- `powerSeriesMapSubalgebra` (L43) / `RIntegralCPowerSeriesSubring` (L111) / `IntegralPowerSeriesSubring` (L150): same set as `Subalgebra`, `Subring`, `Subring`.
### Generalization notes
- `hasCoeffsIn_*` (L71–104) are already at the right generality (`CommSemiring R`, `Semiring A`; ring versions for `neg`/`sub`).
- `IsIntegralPowerSeriesmod` (L173–182): the proof uses only `Int.modEq_zero_iff_dvd`, cast injectivity and `hc`; it holds for `[CommRing R] [Field A] [Algebra R A] {c : R} (hc : algebraMap R A c ≠ 0)` with hypothesis `∀ n, c ∣ (lift).coeff n`, conclusion `HasCoeffsIn R A ((algebraMap R A c)⁻¹ • f)`.
- `toHasCoeffsInPowerSeries`'s `Classical.choose` (L130) is avoidable whenever `algebraMap R A` is injective (then the lift is unique and computable coefficientwise), which is the only case used (`ℤ → ℂ`).
- `modularFormModuleofIsScalarTower` (L191) needs only `[Semiring R] [Module R ℂ] [IsScalarTower R ℂ ℂ]` — already the maximal generality mathlib's `instSMulℂ` supports.
