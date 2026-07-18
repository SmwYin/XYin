/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
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
* `IntegralPowerSeries.IsIntegralPowerSeries`: complex power series with integer coefficients.
* `IntegralPowerSeries.modularFormQExpansionSubmodule`: the `R`-submodule of modular forms whose
  `q`-expansion has all coefficients in `R`.

## Main results

* `hasCoeffsIn_iff_coeff`: coefficientwise characterisation of `HasCoeffsIn`.
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

/-- The `R`-subalgebra of `A⟦X⟧` of power series arising by base change from `R⟦X⟧`. -/
noncomputable def powerSeriesMapSubalgebra (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Subalgebra R (PowerSeries A) := (powerSeriesMapAlgHom R A).range

/-- `powerSeriesMapSubalgebra` viewed as an `R`-submodule of `A⟦X⟧`. -/
noncomputable def powerSeriesMapSubmodule (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Submodule R (PowerSeries A) := (powerSeriesMapSubalgebra R A).toSubmodule

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

lemma mem_powerSeriesMapSubmodule_iff (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] (x : PowerSeries A) :
    x ∈ powerSeriesMapSubmodule R A ↔ HasCoeffsIn R A x :=
  Iff.rfl

lemma hasCoeffsIn_zero (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    HasCoeffsIn R A (0 : PowerSeries A) :=
  (powerSeriesMapSubalgebra R A).zero_mem

lemma hasCoeffsIn_one (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    HasCoeffsIn R A (1 : PowerSeries A) :=
  (powerSeriesMapSubalgebra R A).one_mem

lemma hasCoeffsIn_add (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    {x y : PowerSeries A} (hx : HasCoeffsIn R A x) (hy : HasCoeffsIn R A y) :
    HasCoeffsIn R A (x + y) :=
  (powerSeriesMapSubalgebra R A).add_mem hx hy

lemma hasCoeffsIn_mul (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    {x y : PowerSeries A} (hx : HasCoeffsIn R A x) (hy : HasCoeffsIn R A y) :
    HasCoeffsIn R A (x * y) :=
  (powerSeriesMapSubalgebra R A).mul_mem hx hy

lemma hasCoeffsIn_smul (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (r : R) {x : PowerSeries A} (hx : HasCoeffsIn R A x) :
    HasCoeffsIn R A (r • x) :=
  (powerSeriesMapSubalgebra R A).smul_mem hx r

lemma hasCoeffsIn_neg (R A : Type*) [CommRing R] [Ring A] [Algebra R A] {x : PowerSeries A}
    (hx : HasCoeffsIn R A x) : HasCoeffsIn R A (-x) :=
  (powerSeriesMapSubalgebra R A).neg_mem hx

lemma hasCoeffsIn_sub (R A : Type*) [CommRing R] [Ring A] [Algebra R A] {x y : PowerSeries A}
    (hx : HasCoeffsIn R A x) (hy : HasCoeffsIn R A y) : HasCoeffsIn R A (x - y) :=
  (powerSeriesMapSubalgebra R A).sub_mem hx hy

lemma hasCoeffsIn_C_algebraMap (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (r : R) : HasCoeffsIn R A (PowerSeries.C (algebraMap R A r)) :=
  ⟨PowerSeries.C r, by simp [PowerSeries.map_C]⟩

/-- The coefficientwise coercion `R⟦X⟧ → ℂ⟦X⟧` as a ring homomorphism. -/
abbrev coeToComplexPowerSeries.ringHom (R : Type*) [CommRing R] [Algebra R ℂ] :
    PowerSeries R →+* PowerSeries ℂ := (powerSeriesMapAlgHom R ℂ).toRingHom

/-- The subring of `ℂ⟦X⟧` of power series with coefficients in the image of `R`. -/
noncomputable abbrev RIntegralCPowerSeriesSubring (R : Type*) [CommRing R] [Algebra R ℂ] :
    Subring (PowerSeries ℂ) := (powerSeriesMapSubalgebra R ℂ).toSubring

/-- A complex power series has all its coefficients in the image of `R`. -/
abbrev IsRIntegralCPowerSeries (R : Type*) [CommRing R] [Algebra R ℂ] (x : PowerSeries ℂ) : Prop :=
  HasCoeffsIn R ℂ x

/-- A complex power series has integer coefficients. -/
abbrev IsIntegralCPowerSeries (x : PowerSeries ℂ) : Prop :=
  HasCoeffsIn ℤ ℂ x

lemma isRIntegralCPowerSeries_iff_coeff (R : Type*) [CommRing R] [Algebra R ℂ]
    (f : PowerSeries ℂ) : IsRIntegralCPowerSeries R f ↔
      ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n f = algebraMap R ℂ r := by
  simpa [IsRIntegralCPowerSeries] using hasCoeffsIn_iff_coeff R ℂ f

/-- A (noncanonical) lift to `R⟦X⟧` of a power series with coefficients in `R`. -/
noncomputable def toHasCoeffsInPowerSeries (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] {f : PowerSeries A} (hf : HasCoeffsIn R A f) : PowerSeries R :=
  Classical.choose hf

lemma map_toHasCoeffsInPowerSeries (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    {f : PowerSeries A} (hf : HasCoeffsIn R A f) :
    (powerSeriesMapAlgHom R A) (toHasCoeffsInPowerSeries R A hf) = f :=
  Classical.choose_spec hf

/-- The lift to `R⟦X⟧` of an `R`-integral complex power series. -/
noncomputable def toRIntegralCPowerSeries (R : Type*) [CommRing R] [Algebra R ℂ]
    {f : PowerSeries ℂ} (hf : IsRIntegralCPowerSeries R f) : PowerSeries R :=
  toHasCoeffsInPowerSeries R ℂ hf

lemma coeToComplexPowerSeries_of_toRIntegralCPowerSeries (R : Type*) [CommRing R] [Algebra R ℂ]
    {f : PowerSeries ℂ} (hf : IsRIntegralCPowerSeries R f) :
    (coeToComplexPowerSeries.ringHom R) (toRIntegralCPowerSeries R hf) = f :=
  map_toHasCoeffsInPowerSeries R ℂ hf

namespace IntegralPowerSeries

/-- The subring of complex power series with integer coefficients. -/
noncomputable abbrev IntegralPowerSeriesSubring : Subring (PowerSeries ℂ) :=
  RIntegralCPowerSeriesSubring ℤ

/-- A complex power series has integer coefficients. -/
abbrev IsIntegralPowerSeries (x : PowerSeries ℂ) : Prop :=
  IsIntegralCPowerSeries x

/-- A complex power series is integral iff every coefficient is the coercion of an integer. -/
lemma int_iff (f : PowerSeries ℂ) : IsIntegralPowerSeries f ↔
    ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = z := by
  simpa [IsIntegralPowerSeries] using isRIntegralCPowerSeries_iff_coeff ℤ f

/-- The integer-coefficient lift of an integral complex power series. -/
noncomputable abbrev toIntegralPowerSeries {f : PowerSeries ℂ}
    (hf : IsIntegralPowerSeries f) : PowerSeries ℤ :=
  toRIntegralCPowerSeries ℤ hf

lemma coeTo_of_toIntegralPowerSeries {f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) :
    (coeToComplexPowerSeries.ringHom ℤ) (toIntegralPowerSeries hf) = f := by
  simpa [toIntegralPowerSeries] using coeToComplexPowerSeries_of_toRIntegralCPowerSeries ℤ hf

/-- Divisibility descent: if all integer coefficients of an integral power series are divisible
by `c ≠ 0`, then `(1 / c) • f` is again an integral power series. -/
lemma IsIntegralPowerSeriesmod {c : ℤ} (hc : c ≠ 0) {f : PowerSeries ℂ}
    (hf : IsIntegralPowerSeries f) (hmod : ∀ n : ℕ, Int.ModEq c
    ((toIntegralPowerSeries hf).coeff n) 0) : IsIntegralPowerSeries ((1 / c : ℂ) • f) := by
  rw [int_iff]
  intro n
  let g : PowerSeries ℤ := toIntegralPowerSeries hf
  have hg : (coeToComplexPowerSeries.ringHom ℤ) g = f := by
    simpa [g] using coeTo_of_toIntegralPowerSeries hf
  have hdiv : c ∣ g.coeff n := by
    have hneg : c ∣ -g.coeff n := by
      simpa [Int.sub_eq_add_neg] using Int.modEq_iff_dvd.mp (hmod n)
    exact Int.dvd_neg.mp hneg
  rcases hdiv with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have hgn : (g.coeff n : ℂ) = f.coeff n := congrArg (PowerSeries.coeff n) hg
  calc
  _ = (1 / c : ℂ) * f.coeff n := by simp
  _ = (1 / c : ℂ) * (g.coeff n : ℂ) := by simp [hgn]
  _ = (1 / c : ℂ) * ((c * t : ℤ) : ℂ) := by simp [ht]
  _ = (1 / c : ℂ) * ((c : ℂ) * (t : ℂ)) := by norm_cast
  _ = _ := by simp [hc]

section ModularForms

open UpperHalfPlane ModularFormClass

/-- The `R`-module structure on modular forms obtained by restricting the `ℂ`-action along a
scalar tower `R → ℂ`.  Scoped: at `R = ℕ, ℤ, ℝ, ℂ` it would form non-defeq diamonds with the
module instances provided by mathlib. -/
noncomputable scoped instance modularFormModuleofIsScalarTower (R : Type*) [Semiring R]
    [Module R ℂ] [IsScalarTower R ℂ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [Γ.HasDetOne] :
    Module R (ModularForm Γ k) :=
  Function.Injective.module R ModularForm.coeHom DFunLike.coe_injective fun _ _ => rfl

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
