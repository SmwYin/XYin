/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Power series with coefficients in a base ring

This file develops the predicate `HasCoeffsIn R A x`: a formal power series `x ∈ A⟦X⟧` arises by
base change from `R⟦X⟧` along `algebraMap R A`.  Specialised to `R = ℤ` and `A = ℂ` this yields
`IntegralPowerSeries.IsIntegralPowerSeries`, the notion of a complex power series with integer
coefficients used throughout the q-expansion development.

## Main definitions

* `powerSeriesMapAlgHom`: coefficientwise base change `R⟦X⟧ →ₐ[R] A⟦X⟧`.
* `HasCoeffsIn`: membership in the range subalgebra of `powerSeriesMapAlgHom`.
* `toHasCoeffsInPowerSeries`: a lift to `R⟦X⟧` of a power series with coefficients in `R`.
* `IntegralPowerSeries.IsIntegralPowerSeries`, `IntegralPowerSeries.toIntegralPowerSeries`:
  complex power series with integer coefficients, and their integer lifts.
* `IntegralPowerSeries.modularFormQExpansionSubmodule`: the `R`-submodule of modular forms whose
  `q`-expansion has all coefficients in `R`.

## Main results

* `hasCoeffsIn_iff_coeff`: coefficientwise characterisation of `HasCoeffsIn`.
* `IntegralPowerSeries.coeff_toIntegralPowerSeries_cast`: the integer lift has the expected
  coefficients.
* `IntegralPowerSeries.IsIntegralPowerSeriesmod`: an integral power series all of whose integer
  coefficients are divisible by `c ≠ 0` remains integral after division by `c`.
-/

/-- The coefficientwise base-change map on formal power series, packaged as an `R`-algebra
homomorphism `R⟦X⟧ →ₐ[R] A⟦X⟧`. -/
def powerSeriesMapAlgHom (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : PowerSeries R →ₐ[R] PowerSeries A :=
  PowerSeries.mapAlgHom (Algebra.ofId R A)

@[simp]
lemma powerSeriesMapAlgHom_apply (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (f : PowerSeries R) : powerSeriesMapAlgHom R A f = f.map (algebraMap R A) :=
  rfl

lemma coeff_powerSeriesMapAlgHom (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (f : PowerSeries R) (n : ℕ) :
    (powerSeriesMapAlgHom R A f).coeff n = algebraMap R A (f.coeff n) := by
  simp

/-- The coefficients of the base change of an integer power series to `ℂ` are the casts of its
coefficients. -/
@[simp]
lemma coeff_mapAlgHom_ofId_int (F : PowerSeries ℤ) (n : ℕ) :
    (PowerSeries.mapAlgHom (Algebra.ofId ℤ ℂ) F).coeff n = (F.coeff n : ℂ) := by
  rw [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map]
  rfl

/-- The `R`-subalgebra of `A⟦X⟧` of power series arising by base change from `R⟦X⟧`. -/
noncomputable def powerSeriesMapSubalgebra (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Subalgebra R (PowerSeries A) := (powerSeriesMapAlgHom R A).range

/-- The power series `x ∈ A⟦X⟧` has all its coefficients in the image of `algebraMap R A`. -/
def HasCoeffsIn (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (x : PowerSeries A) : Prop := x ∈ powerSeriesMapSubalgebra R A

/-- A power series lies in the base-change subalgebra iff every coefficient lies in the image of
`algebraMap R A`. -/
lemma hasCoeffsIn_iff_coeff (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (f : PowerSeries A) : HasCoeffsIn R A f ↔
      ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n f = algebraMap R A r := by
  constructor
  · rintro ⟨g, rfl⟩ n
    exact ⟨PowerSeries.coeff n g, by simp⟩
  · intro h
    choose r hr using h
    exact ⟨PowerSeries.mk r, PowerSeries.ext fun n => by simp [(hr n).symm]⟩

section Closure

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

lemma hasCoeffsIn_zero : HasCoeffsIn R A (0 : PowerSeries A) :=
  (powerSeriesMapSubalgebra R A).zero_mem

lemma hasCoeffsIn_one : HasCoeffsIn R A (1 : PowerSeries A) :=
  (powerSeriesMapSubalgebra R A).one_mem

lemma hasCoeffsIn_add {x y : PowerSeries A} (hx : HasCoeffsIn R A x) (hy : HasCoeffsIn R A y) :
    HasCoeffsIn R A (x + y) :=
  (powerSeriesMapSubalgebra R A).add_mem hx hy

lemma hasCoeffsIn_mul {x y : PowerSeries A} (hx : HasCoeffsIn R A x) (hy : HasCoeffsIn R A y) :
    HasCoeffsIn R A (x * y) :=
  (powerSeriesMapSubalgebra R A).mul_mem hx hy

lemma hasCoeffsIn_pow {x : PowerSeries A} (hx : HasCoeffsIn R A x) (n : ℕ) :
    HasCoeffsIn R A (x ^ n) :=
  (powerSeriesMapSubalgebra R A).pow_mem hx n

lemma hasCoeffsIn_smul (r : R) {x : PowerSeries A} (hx : HasCoeffsIn R A x) :
    HasCoeffsIn R A (r • x) :=
  (powerSeriesMapSubalgebra R A).smul_mem hx r

lemma hasCoeffsIn_algebraMap (r : R) : HasCoeffsIn R A (algebraMap R (PowerSeries A) r) :=
  (powerSeriesMapSubalgebra R A).algebraMap_mem r

lemma hasCoeffsIn_C_algebraMap (r : R) : HasCoeffsIn R A (PowerSeries.C (algebraMap R A r)) :=
  ⟨PowerSeries.C r, by simp [PowerSeries.map_C]⟩

lemma hasCoeffsIn_X : HasCoeffsIn R A (PowerSeries.X : PowerSeries A) :=
  ⟨PowerSeries.X, by simp⟩

lemma hasCoeffsIn_finset_sum {ι : Type*} {s : Finset ι} {x : ι → PowerSeries A}
    (hx : ∀ i ∈ s, HasCoeffsIn R A (x i)) : HasCoeffsIn R A (∑ i ∈ s, x i) :=
  (powerSeriesMapSubalgebra R A).sum_mem hx

lemma hasCoeffsIn_finset_prod {A : Type*} [CommSemiring A] [Algebra R A] {ι : Type*}
    {s : Finset ι} {x : ι → PowerSeries A} (hx : ∀ i ∈ s, HasCoeffsIn R A (x i)) :
    HasCoeffsIn R A (∏ i ∈ s, x i) :=
  (powerSeriesMapSubalgebra R A).prod_mem hx

end Closure

lemma hasCoeffsIn_neg (R A : Type*) [CommRing R] [Ring A] [Algebra R A] {x : PowerSeries A}
    (hx : HasCoeffsIn R A x) : HasCoeffsIn R A (-x) :=
  (powerSeriesMapSubalgebra R A).neg_mem hx

lemma hasCoeffsIn_sub (R A : Type*) [CommRing R] [Ring A] [Algebra R A] {x y : PowerSeries A}
    (hx : HasCoeffsIn R A x) (hy : HasCoeffsIn R A y) : HasCoeffsIn R A (x - y) :=
  (powerSeriesMapSubalgebra R A).sub_mem hx hy

/-- The coefficientwise coercion `R⟦X⟧ → ℂ⟦X⟧` as a ring homomorphism. -/
abbrev coeToComplexPowerSeries.ringHom (R : Type*) [CommRing R] [Algebra R ℂ] :
    PowerSeries R →+* PowerSeries ℂ := (powerSeriesMapAlgHom R ℂ).toRingHom

@[simp]
lemma coeToComplexPowerSeries.ringHom_apply (R : Type*) [CommRing R] [Algebra R ℂ]
    (f : PowerSeries R) : coeToComplexPowerSeries.ringHom R f = f.map (algebraMap R ℂ) :=
  rfl

lemma coeToComplexPowerSeries.coeff_ringHom (R : Type*) [CommRing R] [Algebra R ℂ]
    (f : PowerSeries R) (n : ℕ) :
    (coeToComplexPowerSeries.ringHom R f).coeff n = algebraMap R ℂ (f.coeff n) :=
  coeff_powerSeriesMapAlgHom R ℂ f n

/-- The coefficients of the complexification of an integer power series are the casts of its
coefficients. -/
lemma coeToComplexPowerSeries.coeff_ringHom_int (f : PowerSeries ℤ) (n : ℕ) :
    (coeToComplexPowerSeries.ringHom ℤ f).coeff n = (f.coeff n : ℂ) :=
  coeff_mapAlgHom_ofId_int f n

/-- A (noncanonical) lift to `R⟦X⟧` of a power series with coefficients in `R`. -/
noncomputable def toHasCoeffsInPowerSeries (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] {f : PowerSeries A} (hf : HasCoeffsIn R A f) : PowerSeries R :=
  Classical.choose hf

lemma map_toHasCoeffsInPowerSeries (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    {f : PowerSeries A} (hf : HasCoeffsIn R A f) :
    (powerSeriesMapAlgHom R A) (toHasCoeffsInPowerSeries R A hf) = f :=
  Classical.choose_spec hf

/-- The lift `toHasCoeffsInPowerSeries` has the expected coefficients. (Not `@[simp]`: it would
collapse the specification `map_toHasCoeffsInPowerSeries` to `True` under `simpa`.) -/
lemma coeff_toHasCoeffsInPowerSeries (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    {f : PowerSeries A} (hf : HasCoeffsIn R A f) (n : ℕ) :
    algebraMap R A ((toHasCoeffsInPowerSeries R A hf).coeff n) = f.coeff n := by
  rw [← coeff_powerSeriesMapAlgHom, map_toHasCoeffsInPowerSeries]

namespace IntegralPowerSeries

/-- The subring of complex power series with integer coefficients. -/
noncomputable abbrev IntegralPowerSeriesSubring : Subring (PowerSeries ℂ) :=
  (powerSeriesMapSubalgebra ℤ ℂ).toSubring

/-- A complex power series has integer coefficients. -/
abbrev IsIntegralPowerSeries (x : PowerSeries ℂ) : Prop :=
  HasCoeffsIn ℤ ℂ x

/-- A complex power series is integral iff every coefficient is the coercion of an integer. -/
lemma int_iff (f : PowerSeries ℂ) : IsIntegralPowerSeries f ↔
    ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = z := by
  simpa using hasCoeffsIn_iff_coeff ℤ ℂ f

/-- The integer-coefficient lift of an integral complex power series. -/
noncomputable abbrev toIntegralPowerSeries {f : PowerSeries ℂ}
    (hf : IsIntegralPowerSeries f) : PowerSeries ℤ :=
  toHasCoeffsInPowerSeries ℤ ℂ hf

lemma coeTo_of_toIntegralPowerSeries {f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) :
    (coeToComplexPowerSeries.ringHom ℤ) (toIntegralPowerSeries hf) = f :=
  map_toHasCoeffsInPowerSeries ℤ ℂ hf

/-- `coeTo_of_toIntegralPowerSeries` stated with mathlib's `PowerSeries.mapAlgHom`. -/
lemma mapAlgHom_ofId_toIntegralPowerSeries {f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) :
    PowerSeries.mapAlgHom (Algebra.ofId ℤ ℂ) (toIntegralPowerSeries hf) = f :=
  map_toHasCoeffsInPowerSeries ℤ ℂ hf

/-- The coefficients of the integer lift, cast back to `ℂ`, are the original coefficients. -/
lemma coeff_toIntegralPowerSeries_cast {f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f)
    (n : ℕ) : ((toIntegralPowerSeries hf).coeff n : ℂ) = f.coeff n := by
  simpa using coeff_toHasCoeffsInPowerSeries ℤ ℂ hf n

/-- The integer lift is the unique integer power series whose base change is `f`. -/
lemma toIntegralPowerSeries_eq_of_map_eq {f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f)
    {g : PowerSeries ℤ} (hg : coeToComplexPowerSeries.ringHom ℤ g = f) :
    toIntegralPowerSeries hf = g :=
  PowerSeries.map_injective (algebraMap ℤ ℂ) Int.cast_injective
    ((coeTo_of_toIntegralPowerSeries hf).trans hg.symm)

/-- Divisibility descent: if all integer coefficients of an integral power series are divisible
by `c ≠ 0`, then `(1 / c) • f` is again an integral power series. -/
lemma IsIntegralPowerSeriesmod {c : ℤ} (hc : c ≠ 0) {f : PowerSeries ℂ}
    (hf : IsIntegralPowerSeries f) (hmod : ∀ n : ℕ, Int.ModEq c
    ((toIntegralPowerSeries hf).coeff n) 0) : IsIntegralPowerSeries ((1 / c : ℂ) • f) := by
  rw [int_iff]
  intro n
  obtain ⟨t, ht⟩ := Int.modEq_zero_iff_dvd.mp (hmod n)
  refine ⟨t, ?_⟩
  simp [← coeff_toIntegralPowerSeries_cast hf, ht, hc]

section ModularForms

open UpperHalfPlane ModularFormClass

/-- The `R`-module structure on modular forms obtained by restricting the `ℂ`-action along a
scalar tower `R → ℂ`.  Scoped: at `R = ℕ, ℤ, ℝ, ℂ` it would form non-defeq diamonds with the
module instances provided by mathlib. -/
noncomputable scoped instance modularFormModuleofIsScalarTower (R : Type*) [Semiring R]
    [Module R ℂ] [IsScalarTower R ℂ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [Γ.HasDetOne] :
    Module R (ModularForm Γ k) :=
  Function.Injective.module R (FunLike.coeAddMonoidHom (ModularForm Γ k) ℍ ℂ)
    DFunLike.coe_injective fun _ _ ↦ rfl

/-- Taking `q`-expansions commutes with scalar multiplication by elements of `R`, acting through
`algebraMap R ℂ`. -/
lemma qExpansion_smul_algebra (R : Type*) [CommSemiring R] [Algebra R ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [Γ.HasDetOne] {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (r : R) (f : ModularForm Γ k) :
    qExpansion h (r • f) = (algebraMap R ℂ r) • qExpansion h f := by
  simpa using ModularForm.qExpansion_smul (F := ModularForm Γ k) hh hΓ (algebraMap R ℂ r) f

/-- The `R`-submodule of modular forms of weight `k` whose `q`-expansion with period `h` has all
coefficients in `R`. -/
def modularFormQExpansionSubmodule (R : Type*) [CommRing R] [Algebra R ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] (k : ℤ) (h : ℝ) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) : Submodule R (ModularForm Γ k) where
  carrier := {f | HasCoeffsIn R ℂ (qExpansion h f)}
  zero_mem' := by
    change HasCoeffsIn R ℂ (qExpansion h (0 : ModularForm Γ k))
    rw [ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero]
    exact hasCoeffsIn_zero R ℂ
  add_mem' := by
    intro f g hf hg
    change HasCoeffsIn R ℂ (qExpansion h (f + g))
    rw [ModularForm.qExpansion_add hh hΓ]
    simpa [ModularForm.coe_add] using hasCoeffsIn_add R ℂ hf hg
  smul_mem' := by
    intro r f hf
    change HasCoeffsIn R ℂ (qExpansion h ((r • f : ModularForm Γ k)))
    have hs : qExpansion h ((r • f : ModularForm Γ k)) = (algebraMap R ℂ r) • qExpansion h f := by
      simpa using qExpansion_smul_algebra R hh hΓ r f
    rw [hs]
    simpa [Algebra.smul_def, PowerSeries.algebraMap_apply] using hasCoeffsIn_smul R ℂ r hf

end ModularForms

end IntegralPowerSeries
