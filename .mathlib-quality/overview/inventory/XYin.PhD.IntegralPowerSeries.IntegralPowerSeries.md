# Source: /Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/IntegralPowerSeries/IntegralPowerSeries.lean
Project-internal imports (XYin): [] (only `Mathlib.NumberTheory.ModularForms.QExpansion`)

### `def powerSeriesMapAlgHom`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] : PowerSeries R →ₐ[R] PowerSeries A`
- **What**: The coefficientwise base-change map on formal power series, `PowerSeries.map (algebraMap R A)`, packaged as an `R`-algebra homomorphism `R⟦X⟧ →ₐ[R] A⟦X⟧`.
- **How**: Bundles the mathlib ring hom `PowerSeries.map` with a `commutes'` proof done coefficientwise via `ext` and `PowerSeries.algebraMap_apply` (the algebra map into a power series ring is `C ∘ algebraMap`).
- **Hypotheses**: `R` a commutative semiring, `A` a semiring with an `R`-algebra structure.
- **Uses from project**: []
- **Used by**: `powerSeriesMapSubalgebra`, `powerSeriesMapAlgHom_injective`, `coeToComplexPowerSeries.ringHom`, `map_toHasCoeffsInPowerSeries`
- **Visibility**: public
- **Lines**: 5–11, 7-line definition
- **Notes**: file has `set_option linter.style.header false` (line 3) and a trailing `#min_imports` (line 238)

### `def powerSeriesMapSubalgebra`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] : Subalgebra R (PowerSeries A)`
- **What**: The `R`-subalgebra of `A⟦X⟧` consisting of power series that arise as base changes of series in `R⟦X⟧`, i.e. series "with coefficients in (the image of) `R`".
- **How**: Defined as `AlgHom.range` of `powerSeriesMapAlgHom R A`.
- **Hypotheses**: `R` commutative semiring, `A` a semiring, `Algebra R A`.
- **Uses from project**: [`powerSeriesMapAlgHom`]
- **Used by**: `powerSeriesMapSubmodule`, `HasCoeffsIn`, `mem_powerSeriesMapSubmodule_iff`, `hasCoeffsIn_zero`, `hasCoeffsIn_one`, `hasCoeffsIn_add`, `hasCoeffsIn_mul`, `hasCoeffsIn_smul`, `hasCoeffsIn_neg`, `hasCoeffsIn_sub`, `RIntegralCPowerSeriesSubring`
- **Visibility**: public (noncomputable)
- **Lines**: 13–14, 1-line definition
- **Notes**: none

### `def powerSeriesMapSubmodule`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] : Submodule R (PowerSeries A)`
- **What**: The same set of `R`-integral power series in `A⟦X⟧` viewed as an `R`-submodule (forgetting the multiplicative structure).
- **How**: `Subalgebra.toSubmodule` applied to `powerSeriesMapSubalgebra R A`.
- **Hypotheses**: as for `powerSeriesMapSubalgebra`.
- **Uses from project**: [`powerSeriesMapSubalgebra`]
- **Used by**: `mem_powerSeriesMapSubmodule_iff`, `mem_powerSeriesMapSubmodule_iff_coeff`, `modularFormQExpansionLinearMap`
- **Visibility**: public (noncomputable)
- **Lines**: 16–17, 1-line definition
- **Notes**: none

### `def HasCoeffsIn`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] (x : PowerSeries A) : Prop`
- **What**: The predicate "the power series `x ∈ A⟦X⟧` has all its coefficients in the image of `R`", stated as membership in `powerSeriesMapSubalgebra R A`.
- **How**: Direct definition `x ∈ powerSeriesMapSubalgebra R A`.
- **Hypotheses**: as above.
- **Uses from project**: [`powerSeriesMapSubalgebra`]
- **Used by**: `hasCoeffsIn_iff_coeff`, `mem_powerSeriesMapSubmodule_iff`, `hasCoeffsIn_zero`, `hasCoeffsIn_one`, `hasCoeffsIn_add`, `hasCoeffsIn_mul`, `hasCoeffsIn_smul`, `hasCoeffsIn_neg`, `hasCoeffsIn_sub`, `hasCoeffsIn_C_algebraMap`, `IsRIntegralCPowerSeries`, `IsIntegralCPowerSeries`, `toHasCoeffsInPowerSeries`, `map_toHasCoeffsInPowerSeries`, `modularFormQExpansionSubmodule`
- **Visibility**: public
- **Lines**: 19–20, 1-line definition
- **Notes**: none

### `lemma hasCoeffsIn_iff_coeff`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] (f : PowerSeries A) : HasCoeffsIn R A f ↔ ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n f = algebraMap R A r`
- **What**: Coefficientwise characterisation of `HasCoeffsIn`: a series lies in the base-change subalgebra iff every individual coefficient lies in the image of `algebraMap R A`.
- **How**: Forward direction: a preimage `g` in `R⟦X⟧` yields coefficient preimages via `PowerSeries.coeff_map`. Backward: `choose` a coefficient lift `r : ℕ → R` and assemble the preimage series as `PowerSeries.mk r`, verified coefficientwise with `PowerSeries.coeff_map` and a `calc`.
- **Hypotheses**: `R` commutative semiring, `A` semiring, `Algebra R A`. No injectivity assumed (the lift need not be unique).
- **Uses from project**: [`HasCoeffsIn`, `powerSeriesMapSubalgebra` (via the membership unfold)]
- **Used by**: `mem_powerSeriesMapSubmodule_iff_coeff`, `isRIntegralCPowerSeries_iff_coeff`, `mem_modularFormQExpansionSubmodule_iff_coeff`
- **Visibility**: public
- **Lines**: 22–40, 19-line proof
- **Notes**: none

### `lemma mem_powerSeriesMapSubmodule_iff`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] (x : PowerSeries A) : x ∈ powerSeriesMapSubmodule R A ↔ HasCoeffsIn R A x`
- **What**: Membership in the submodule version coincides with the `HasCoeffsIn` predicate (submodule and subalgebra have the same carrier).
- **How**: `simp` unfolding both definitions (`Subalgebra.toSubmodule` membership is definitionally subalgebra membership).
- **Hypotheses**: as above.
- **Uses from project**: [`powerSeriesMapSubmodule`, `HasCoeffsIn`]
- **Used by**: `mem_powerSeriesMapSubmodule_iff_coeff`, `modularFormQExpansionLinearMap`
- **Visibility**: public
- **Lines**: 42–45, 1-line proof
- **Notes**: none

### `lemma mem_powerSeriesMapSubmodule_iff_coeff`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] (x : PowerSeries A) : x ∈ powerSeriesMapSubmodule R A ↔ ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n x = algebraMap R A r`
- **What**: Coefficientwise membership criterion for the submodule, composing the previous two lemmas.
- **How**: `simpa` chaining `mem_powerSeriesMapSubmodule_iff` with `hasCoeffsIn_iff_coeff`.
- **Hypotheses**: as above.
- **Uses from project**: [`powerSeriesMapSubmodule`, `mem_powerSeriesMapSubmodule_iff`, `hasCoeffsIn_iff_coeff`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 47–50, 1-line proof
- **Notes**: none

### `lemma hasCoeffsIn_zero`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] : HasCoeffsIn R A (0 : PowerSeries A)`
- **What**: The zero series has coefficients in `R`.
- **How**: `Subalgebra.zero_mem` of the range subalgebra.
- **Hypotheses**: as above.
- **Uses from project**: [`HasCoeffsIn`, `powerSeriesMapSubalgebra`]
- **Used by**: `modularFormQExpansionSubmodule`
- **Visibility**: public
- **Lines**: 52–54, term-mode 1-liner
- **Notes**: none

### `lemma hasCoeffsIn_one`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] : HasCoeffsIn R A (1 : PowerSeries A)`
- **What**: The constant series 1 has coefficients in `R`.
- **How**: `Subalgebra.one_mem`.
- **Hypotheses**: as above.
- **Uses from project**: [`HasCoeffsIn`, `powerSeriesMapSubalgebra`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 56–58, term-mode 1-liner
- **Notes**: none

### `lemma hasCoeffsIn_add`
- **Type**: `{x y : PowerSeries A} (hx : HasCoeffsIn R A x) (hy : HasCoeffsIn R A y) : HasCoeffsIn R A (x + y)` (with `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]` explicit)
- **What**: `HasCoeffsIn` is closed under addition.
- **How**: `Subalgebra.add_mem`.
- **Hypotheses**: both summands have coefficients in `R`.
- **Uses from project**: [`HasCoeffsIn`, `powerSeriesMapSubalgebra`]
- **Used by**: `modularFormQExpansionSubmodule`
- **Visibility**: public
- **Lines**: 60–63, term-mode 1-liner
- **Notes**: none

### `lemma hasCoeffsIn_mul`
- **Type**: `{x y : PowerSeries A} (hx : HasCoeffsIn R A x) (hy : HasCoeffsIn R A y) : HasCoeffsIn R A (x * y)` (same explicit prefix)
- **What**: `HasCoeffsIn` is closed under multiplication (Cauchy product).
- **How**: `Subalgebra.mul_mem`.
- **Hypotheses**: both factors have coefficients in `R`.
- **Uses from project**: [`HasCoeffsIn`, `powerSeriesMapSubalgebra`]
- **Used by**: unused in file (the sibling file uses `IntegralPowerSeriesSubring.mul_mem` directly instead)
- **Visibility**: public
- **Lines**: 65–68, term-mode 1-liner
- **Notes**: none

### `lemma hasCoeffsIn_smul`
- **Type**: `(r : R) {x : PowerSeries A} (hx : HasCoeffsIn R A x) : HasCoeffsIn R A (r • x)` (same explicit prefix)
- **What**: `HasCoeffsIn` is closed under scalar multiplication by elements of `R`.
- **How**: `Subalgebra.smul_mem`.
- **Hypotheses**: `x` has coefficients in `R`.
- **Uses from project**: [`HasCoeffsIn`, `powerSeriesMapSubalgebra`]
- **Used by**: `modularFormQExpansionSubmodule`
- **Visibility**: public
- **Lines**: 70–73, term-mode 1-liner
- **Notes**: none

### `lemma hasCoeffsIn_neg`
- **Type**: `(R A : Type*) [CommRing R] [Ring A] [Algebra R A] {x : PowerSeries A} (hx : HasCoeffsIn R A x) : HasCoeffsIn R A (-x)`
- **What**: In the ring setting, `HasCoeffsIn` is closed under negation.
- **How**: `Subalgebra.neg_mem`.
- **Hypotheses**: `R` a commutative ring, `A` a ring (needed for negation to exist).
- **Uses from project**: [`HasCoeffsIn`, `powerSeriesMapSubalgebra`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 75–77, term-mode 1-liner
- **Notes**: none

### `lemma hasCoeffsIn_sub`
- **Type**: `(R A : Type*) [CommRing R] [Ring A] [Algebra R A] {x y : PowerSeries A} (hx : HasCoeffsIn R A x) (hy : HasCoeffsIn R A y) : HasCoeffsIn R A (x - y)`
- **What**: In the ring setting, `HasCoeffsIn` is closed under subtraction.
- **How**: `Subalgebra.sub_mem`.
- **Hypotheses**: ring setting; both operands have coefficients in `R`.
- **Uses from project**: [`HasCoeffsIn`, `powerSeriesMapSubalgebra`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 79–81, term-mode 1-liner
- **Notes**: none

### `lemma hasCoeffsIn_C_algebraMap`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] (r : R) : HasCoeffsIn R A (PowerSeries.C (algebraMap R A r))`
- **What**: A constant series whose constant is in the image of `R` has coefficients in `R`.
- **How**: Exhibits the explicit preimage `PowerSeries.C r` and closes with the mathlib lemma `PowerSeries.map_C` (map commutes with the constant embedding).
- **Hypotheses**: as above.
- **Uses from project**: [`HasCoeffsIn`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 83–87, 3-line proof
- **Notes**: none

### `lemma powerSeriesMapAlgHom_injective`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A] : Function.Injective (powerSeriesMapAlgHom R A)`
- **What**: When `algebraMap R A` is injective (faithful scalar action), the base-change map on power series is injective — so integral lifts are unique.
- **How**: Reduces to injectivity of `PowerSeries.map` via the mathlib lemmas `PowerSeries.map_injective` and `FaithfulSMul.algebraMap_injective`.
- **Hypotheses**: `FaithfulSMul R A`, i.e. `algebraMap R A` injective.
- **Uses from project**: [`powerSeriesMapAlgHom`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 89–93, 4-line proof
- **Notes**: none

### `abbrev coeToComplexPowerSeries.ringHom`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] : PowerSeries R →+* PowerSeries ℂ`
- **What**: The coefficientwise coercion `R⟦X⟧ → ℂ⟦X⟧` as a ring homomorphism, specialising the alg hom to target `ℂ`.
- **How**: `AlgHom.toRingHom` of `powerSeriesMapAlgHom R ℂ`.
- **Hypotheses**: `R` a commutative ring mapping into `ℂ`.
- **Uses from project**: [`powerSeriesMapAlgHom`]
- **Used by**: `coeToComplexPowerSeries_of_toRIntegralCPowerSeries`, `coeTo_of_toIntegralPowerSeries`, `IsIntegralPowerSeriesmod`
- **Visibility**: public
- **Lines**: 95–96, 1-line abbrev
- **Notes**: dot-name `coeToComplexPowerSeries.ringHom` declared outside any namespace (unconventional naming)

### `abbrev RIntegralCPowerSeriesSubring`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] : Subring (PowerSeries ℂ)`
- **What**: The subring of `ℂ⟦X⟧` of series with coefficients in (the image of) `R`.
- **How**: `Subalgebra.toSubring` of `powerSeriesMapSubalgebra R ℂ`.
- **Hypotheses**: `R` commutative ring with `Algebra R ℂ`.
- **Uses from project**: [`powerSeriesMapSubalgebra`]
- **Used by**: `IntegralPowerSeriesSubring`
- **Visibility**: public (noncomputable abbrev)
- **Lines**: 98–99, 1-line abbrev
- **Notes**: none

### `abbrev IsRIntegralCPowerSeries`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] (x : PowerSeries ℂ) : Prop`
- **What**: Predicate that a complex power series has all coefficients in `R`; abbreviation for `HasCoeffsIn R ℂ x`.
- **How**: Direct abbreviation.
- **Hypotheses**: as above.
- **Uses from project**: [`HasCoeffsIn`]
- **Used by**: `isRIntegralCPowerSeries_iff_coeff`, `toRIntegralCPowerSeries`, `coeToComplexPowerSeries_of_toRIntegralCPowerSeries`
- **Visibility**: public
- **Lines**: 101–102, 1-line abbrev
- **Notes**: none

### `abbrev IsIntegralCPowerSeries`
- **Type**: `(x : PowerSeries ℂ) : Prop`
- **What**: Predicate that a complex power series has all coefficients in `ℤ` (rational-integer coefficients); abbreviation for `HasCoeffsIn ℤ ℂ x`.
- **How**: Direct abbreviation.
- **Hypotheses**: none.
- **Uses from project**: [`HasCoeffsIn`]
- **Used by**: `IsIntegralPowerSeries`
- **Visibility**: public
- **Lines**: 104–105, 1-line abbrev
- **Notes**: none

### `lemma isRIntegralCPowerSeries_iff_coeff`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] (f : PowerSeries ℂ) : IsRIntegralCPowerSeries R f ↔ ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n f = algebraMap R ℂ r`
- **What**: Coefficientwise characterisation of `R`-integrality for complex power series.
- **How**: Direct specialisation of `hasCoeffsIn_iff_coeff` to `A = ℂ`.
- **Hypotheses**: as above.
- **Uses from project**: [`IsRIntegralCPowerSeries`, `hasCoeffsIn_iff_coeff`]
- **Used by**: `IntegralPowerSeries.int_iff`
- **Visibility**: public
- **Lines**: 107–110, 1-line proof
- **Notes**: none

### `def toHasCoeffsInPowerSeries`
- **Type**: `(R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] {f : PowerSeries A} (hf : HasCoeffsIn R A f) : PowerSeries R`
- **What**: A (noncanonical) lift of an `R`-integral series in `A⟦X⟧` back to `R⟦X⟧`, extracted from the existence witness.
- **How**: `Classical.choose` on the range-membership proof.
- **Hypotheses**: `f` has coefficients in `R`.
- **Uses from project**: [`HasCoeffsIn`]
- **Used by**: `map_toHasCoeffsInPowerSeries`, `toRIntegralCPowerSeries`
- **Visibility**: public (noncomputable)
- **Lines**: 112–114, 1-line definition
- **Notes**: lift is unique only when `algebraMap R A` is injective (cf. `powerSeriesMapAlgHom_injective`), which is not required here

### `lemma map_toHasCoeffsInPowerSeries`
- **Type**: `(R A : Type*) … {f : PowerSeries A} (hf : HasCoeffsIn R A f) : (powerSeriesMapAlgHom R A) (toHasCoeffsInPowerSeries R A hf) = f`
- **What**: The chosen lift indeed maps back to `f` under base change (the defining property of the lift).
- **How**: `Classical.choose_spec`.
- **Hypotheses**: `f` has coefficients in `R`.
- **Uses from project**: [`powerSeriesMapAlgHom`, `toHasCoeffsInPowerSeries`, `HasCoeffsIn`]
- **Used by**: `coeToComplexPowerSeries_of_toRIntegralCPowerSeries`
- **Visibility**: public
- **Lines**: 116–119, term-mode 1-liner
- **Notes**: none

### `def toRIntegralCPowerSeries`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] {f : PowerSeries ℂ} (hf : IsRIntegralCPowerSeries R f) : PowerSeries R`
- **What**: The lift to `R⟦X⟧` of an `R`-integral complex power series, specialising `toHasCoeffsInPowerSeries` to `A = ℂ`.
- **How**: Direct application of `toHasCoeffsInPowerSeries R ℂ`.
- **Hypotheses**: `f` is `R`-integral.
- **Uses from project**: [`toHasCoeffsInPowerSeries`, `IsRIntegralCPowerSeries`]
- **Used by**: `coeToComplexPowerSeries_of_toRIntegralCPowerSeries`, `IntegralPowerSeries.toIntegralPowerSeries`
- **Visibility**: public (noncomputable)
- **Lines**: 121–123, 1-line definition
- **Notes**: none

### `lemma coeToComplexPowerSeries_of_toRIntegralCPowerSeries`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] {f : PowerSeries ℂ} (hf : IsRIntegralCPowerSeries R f) : (coeToComplexPowerSeries.ringHom R) (toRIntegralCPowerSeries R hf) = f`
- **What**: Round-trip identity: coercing the chosen `R`-lift back to `ℂ⟦X⟧` recovers `f`.
- **How**: Immediate from `map_toHasCoeffsInPowerSeries` (the ring hom is the same underlying map as the alg hom).
- **Hypotheses**: `f` is `R`-integral.
- **Uses from project**: [`coeToComplexPowerSeries.ringHom`, `toRIntegralCPowerSeries`, `map_toHasCoeffsInPowerSeries`, `IsRIntegralCPowerSeries`]
- **Used by**: `IntegralPowerSeries.coeTo_of_toIntegralPowerSeries`
- **Visibility**: public
- **Lines**: 125–128, term-mode 1-liner
- **Notes**: none

### `abbrev IntegralPowerSeries.IntegralPowerSeriesSubring`
- **Type**: `Subring (PowerSeries ℂ)`
- **What**: The subring of complex power series with integer coefficients (`R = ℤ` case).
- **How**: `RIntegralCPowerSeriesSubring ℤ`.
- **Hypotheses**: none.
- **Uses from project**: [`RIntegralCPowerSeriesSubring`]
- **Used by**: unused in this file (used in `HasIntegralQExpansion.lean` via `IntegralPowerSeriesSubring.mul_mem`)
- **Visibility**: public (in namespace `IntegralPowerSeries`), noncomputable abbrev
- **Lines**: 132–133, 1-line abbrev
- **Notes**: none

### `abbrev IntegralPowerSeries.IsIntegralPowerSeries`
- **Type**: `(x : PowerSeries ℂ) : Prop`
- **What**: The predicate "complex power series with integer coefficients", the file's headline notion; abbreviation for `IsIntegralCPowerSeries x` (= `HasCoeffsIn ℤ ℂ x`).
- **How**: Direct abbreviation.
- **Hypotheses**: none.
- **Uses from project**: [`IsIntegralCPowerSeries`]
- **Used by**: `int_iff`, `toIntegralPowerSeries`, `coeTo_of_toIntegralPowerSeries`, `IsIntegralPowerSeriesmod` (and heavily by `HasIntegralQExpansion.lean`)
- **Visibility**: public (namespace `IntegralPowerSeries`)
- **Lines**: 135–136, 1-line abbrev
- **Notes**: none

### `lemma IntegralPowerSeries.int_iff`
- **Type**: `(f : PowerSeries ℂ) : IsIntegralPowerSeries f ↔ ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = z`
- **What**: A complex power series is integral iff every coefficient is (the coercion of) an integer.
- **How**: Specialisation of `isRIntegralCPowerSeries_iff_coeff` at `R = ℤ` (using `algebraMap ℤ ℂ = Int.cast`).
- **Hypotheses**: none.
- **Uses from project**: [`IsIntegralPowerSeries`, `isRIntegralCPowerSeries_iff_coeff`]
- **Used by**: `IsIntegralPowerSeriesmod` (and `IsIntegralPowerSeries_X_pow` in the sibling file)
- **Visibility**: public (namespace `IntegralPowerSeries`)
- **Lines**: 138–140, 1-line proof
- **Notes**: none

### `abbrev IntegralPowerSeries.toIntegralPowerSeries`
- **Type**: `{f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) : PowerSeries ℤ`
- **What**: The integer-coefficient lift of an integral complex power series.
- **How**: `toRIntegralCPowerSeries ℤ hf`.
- **Hypotheses**: `f` integral.
- **Uses from project**: [`toRIntegralCPowerSeries`, `IsIntegralPowerSeries`]
- **Used by**: `coeTo_of_toIntegralPowerSeries`, `IsIntegralPowerSeriesmod`
- **Visibility**: public (namespace `IntegralPowerSeries`), noncomputable abbrev
- **Lines**: 142–144, 1-line abbrev
- **Notes**: none

### `lemma IntegralPowerSeries.coeTo_of_toIntegralPowerSeries`
- **Type**: `{f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) : (coeToComplexPowerSeries.ringHom ℤ) (toIntegralPowerSeries hf) = f`
- **What**: Round-trip identity at `R = ℤ`: coercing the integer lift back to `ℂ⟦X⟧` gives `f`.
- **How**: `simpa` from `coeToComplexPowerSeries_of_toRIntegralCPowerSeries ℤ`.
- **Hypotheses**: `f` integral.
- **Uses from project**: [`coeToComplexPowerSeries.ringHom`, `toIntegralPowerSeries`, `coeToComplexPowerSeries_of_toRIntegralCPowerSeries`, `IsIntegralPowerSeries`]
- **Used by**: `IsIntegralPowerSeriesmod`
- **Visibility**: public (namespace `IntegralPowerSeries`)
- **Lines**: 146–148, 1-line proof
- **Notes**: none

### `lemma IntegralPowerSeries.IsIntegralPowerSeriesmod`
- **Type**: `{c : ℤ} (hc : c ≠ 0) {f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) (hmod : ∀ n : ℕ, Int.ModEq c ((toIntegralPowerSeries hf).coeff n) 0) : IsIntegralPowerSeries ((1 / c : ℂ) • f)`
- **What**: Divisibility descent: if all integer coefficients of an integral series are divisible by `c ≠ 0`, then `f / c` is again an integral power series. This is the key congruence tool (e.g. for `j = E₄³/Δ`-style arguments where a series divisible by a constant stays integral after division).
- **How**: For each `n`, converts the congruence `coeff ≡ 0 (mod c)` to divisibility via the mathlib lemmas `Int.modEq_iff_dvd` and `Int.dvd_neg`, writes `coeff = c·t`, and computes `(1/c)·(c·t) = t` in `ℂ` by a `calc` chain using `hc` to cancel `c`; the bridge between `ℤ`- and `ℂ`-coefficients is `coeTo_of_toIntegralPowerSeries`.
- **Hypotheses**: `c ≠ 0` in `ℤ`; `f` integral; every coefficient of its integer lift is `≡ 0 mod c`.
- **Uses from project**: [`IsIntegralPowerSeries`, `int_iff`, `toIntegralPowerSeries`, `coeToComplexPowerSeries.ringHom`, `coeTo_of_toIntegralPowerSeries`]
- **Used by**: unused in file
- **Visibility**: public (namespace `IntegralPowerSeries`)
- **Lines**: 150–171, 20-line proof
- **Notes**: statement depends on the noncanonical lift `toIntegralPowerSeries hf` in hypothesis `hmod` (fine since the lift is unique for `ℤ ↪ ℂ`, but the uniqueness is not invoked); name lacks a separator (`IsIntegralPowerSeriesmod` vs `IsIntegralPowerSeries_mod`)

### `instance modularFormModuleofIsScalarTower`
- **Type**: `(R : Type*) [Semiring R] [Module R ℂ] [IsScalarTower R ℂ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [Γ.HasDetOne] : Module R (ModularForm Γ k)`
- **What**: Gives the space of modular forms of weight `k` for `Γ` an `R`-module structure for any scalar ring `R` acting compatibly on `ℂ` (e.g. `R = ℤ, ℚ`, number rings), by restricting the `ℂ`-action.
- **How**: Transport of module structure along the injective coefficient map `ModularForm.coeHom` via mathlib's `Function.Injective.module`, with `DFunLike.coe_injective`.
- **Hypotheses**: `R` a semiring acting on `ℂ` with `IsScalarTower R ℂ ℂ`; `Γ ≤ GL₂(ℝ)` with `Γ.HasDetOne`.
- **Uses from project**: []
- **Used by**: `qExpansion_smul_algebra`, `modularFormQExpansionSubmodule`, `modularFormQExpansionLinearMap` (all implicitly, via the `r • f` notation)
- **Visibility**: public instance (noncomputable)
- **Lines**: 179–182, 1-line body
- **Notes**: instance defined for a generic `R` — potential diamond risk against existing `ℂ`- or `ℤ`-module instances on `ModularForm` should be checked

### `lemma qExpansion_smul_algebra`
- **Type**: `(R : Type*) [CommSemiring R] [Algebra R ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [Γ.HasDetOne] {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (r : R) (f : ModularForm Γ k) : qExpansion h (r • f) = (algebraMap R ℂ r) • qExpansion h f`
- **What**: Taking `q`-expansions commutes with scalar multiplication by elements of `R` (acting through `algebraMap R ℂ`).
- **How**: Reduces to the mathlib lemma `ModularForm.qExpansion_smul` for the `ℂ`-scalar `algebraMap R ℂ r`, using that the `R`-action on modular forms is defined via restriction.
- **Hypotheses**: `h > 0` is a strict period of `Γ` (so `q`-expansions exist).
- **Uses from project**: [`modularFormModuleofIsScalarTower` (implicitly, for `r • f`)]
- **Used by**: `modularFormQExpansionSubmodule`, `modularFormQExpansionLinearMap`
- **Visibility**: public
- **Lines**: 184–188, 1-line proof
- **Notes**: none

### `def modularFormQExpansionSubmodule`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] (k : ℤ) (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) : Submodule R (ModularForm Γ k)`
- **What**: The `R`-submodule of modular forms of weight `k` whose `q`-expansion (with period `h`) has all coefficients in `R` — e.g. for `R = ℤ` the forms with integral `q`-expansion.
- **How**: Carrier is `{f | HasCoeffsIn R ℂ (qExpansion h f)}`; closure under 0, +, • follows from `UpperHalfPlane.qExpansion_zero`, `ModularForm.qExpansion_add`, and `qExpansion_smul_algebra` combined with `hasCoeffsIn_zero/add/smul` (the `smul` case rewrites `algebraMap R ℂ r • x` to `r • x` via `Algebra.smul_def`).
- **Hypotheses**: `R` commutative ring in `ℂ`; `h > 0` a strict period of `Γ`.
- **Uses from project**: [`HasCoeffsIn`, `hasCoeffsIn_zero`, `hasCoeffsIn_add`, `hasCoeffsIn_smul`, `qExpansion_smul_algebra`, `modularFormModuleofIsScalarTower` (implicit)]
- **Used by**: `mem_modularFormQExpansionSubmodule_iff_coeff`, `modularFormQExpansionLinearMap`
- **Visibility**: public
- **Lines**: 190–209, 20-line definition (three membership proofs)
- **Notes**: none

### `lemma mem_modularFormQExpansionSubmodule_iff_coeff`
- **Type**: `… (f : ModularForm Γ k) : f ∈ modularFormQExpansionSubmodule R k h hh hΓ ↔ ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n (qExpansion h f) = algebraMap R ℂ r`
- **What**: Membership criterion: a form is in the `q`-integrality submodule iff each `q`-expansion coefficient lies in the image of `R`.
- **How**: Unfolds the carrier and applies `hasCoeffsIn_iff_coeff` for the series `qExpansion h f`.
- **Hypotheses**: `h > 0` a strict period of `Γ`.
- **Uses from project**: [`modularFormQExpansionSubmodule`, `hasCoeffsIn_iff_coeff`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 211–216, 1-line proof
- **Notes**: none

### `def modularFormQExpansionLinearMap`
- **Type**: `(R : Type*) [CommRing R] [Algebra R ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] (k : ℤ) (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) : modularFormQExpansionSubmodule R k h hh hΓ →ₗ[R] powerSeriesMapSubmodule R ℂ`
- **What**: The `q`-expansion map as an `R`-linear map from the submodule of forms with `R`-integral expansions to the submodule of `R`-integral complex power series.
- **How**: On elements, sends `f ↦ qExpansion h f` (membership by `mem_powerSeriesMapSubmodule_iff`); additivity is `ModularForm.qExpansion_add`, and `R`-linearity is `qExpansion_smul_algebra` translated through `Algebra.smul_def` / `PowerSeries.algebraMap_apply`.
- **Hypotheses**: `h > 0` a strict period of `Γ`.
- **Uses from project**: [`modularFormQExpansionSubmodule`, `powerSeriesMapSubmodule`, `mem_powerSeriesMapSubmodule_iff`, `qExpansion_smul_algebra`, `modularFormModuleofIsScalarTower` (implicit)]
- **Used by**: unused in file
- **Visibility**: public (noncomputable)
- **Lines**: 218–234, 17-line definition
- **Notes**: none

### File Summary
- Total declarations: 30 (7 defs, 15 lemmas/theorems, 1 instance, 7 abbrevs, 0 tactic/meta decls)
- Key API (used by 3+ others): `powerSeriesMapAlgHom` (4), `powerSeriesMapSubalgebra` (11), `powerSeriesMapSubmodule` (3), `HasCoeffsIn` (15), `hasCoeffsIn_iff_coeff` (3), `coeToComplexPowerSeries.ringHom` (3), `IsRIntegralCPowerSeries` (3), `IsIntegralPowerSeries` (4+), `qExpansion_smul_algebra` (2, plus implicit instance use)
- Unused declarations (not used by anything in this file): `mem_powerSeriesMapSubmodule_iff_coeff`, `hasCoeffsIn_one`, `hasCoeffsIn_mul`, `hasCoeffsIn_neg`, `hasCoeffsIn_sub`, `hasCoeffsIn_C_algebraMap`, `powerSeriesMapAlgHom_injective`, `IntegralPowerSeriesSubring` (used by sibling file), `IsIntegralPowerSeriesmod`, `mem_modularFormQExpansionSubmodule_iff_coeff`, `modularFormQExpansionLinearMap`
- Declarations with sorry: []
- Declarations with set_option: [] (file-level `set_option linter.style.header false` at line 3; `#min_imports` at line 238)
- Proofs >30 lines: [] (longest: `hasCoeffsIn_iff_coeff` 19 lines, `IsIntegralPowerSeriesmod` 20 lines, `modularFormQExpansionSubmodule` 20 lines)
