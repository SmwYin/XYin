import Mathlib.NumberTheory.ModularForms.QExpansion

set_option linter.style.header false

def powerSeriesMapAlgHom (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    PowerSeries R →ₐ[R] PowerSeries A :=
  { toRingHom := PowerSeries.map (algebraMap R A)
    commutes' := by
      intro r
      ext n
      simp [PowerSeries.algebraMap_apply] }

noncomputable def powerSeriesMapSubalgebra (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Subalgebra R (PowerSeries A) := (powerSeriesMapAlgHom R A).range

noncomputable def powerSeriesMapSubmodule (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Submodule R (PowerSeries A) := (powerSeriesMapSubalgebra R A).toSubmodule

def HasCoeffsIn (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (x : PowerSeries A) : Prop := x ∈ powerSeriesMapSubalgebra R A

lemma hasCoeffsIn_iff_coeff (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (f : PowerSeries A) : HasCoeffsIn R A f ↔
      ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n f = algebraMap R A r := by
  constructor
  · intro h n
    obtain ⟨g, rfl⟩ := h
    refine ⟨PowerSeries.coeff n g, ?_⟩
    change PowerSeries.coeff n (PowerSeries.map (algebraMap R A) g) =
      algebraMap R A (PowerSeries.coeff n g)
    exact PowerSeries.coeff_map (algebraMap R A) n g
  · intro h
    choose r hr using h
    refine ⟨PowerSeries.mk r, ?_⟩
    ext n
    calc
    _ = algebraMap R A (PowerSeries.coeff n (PowerSeries.mk r)) :=
      PowerSeries.coeff_map (algebraMap R A) n (PowerSeries.mk r)
    _ = algebraMap R A (r n) := by simp
    _ = _ := (hr n).symm

lemma mem_powerSeriesMapSubmodule_iff (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] (x : PowerSeries A) :
    x ∈ powerSeriesMapSubmodule R A ↔ HasCoeffsIn R A x := by
  simp [HasCoeffsIn, powerSeriesMapSubmodule]

lemma mem_powerSeriesMapSubmodule_iff_coeff (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] (x : PowerSeries A) : x ∈ powerSeriesMapSubmodule R A ↔
      ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n x = algebraMap R A r := by
  simpa [mem_powerSeriesMapSubmodule_iff] using hasCoeffsIn_iff_coeff R A x

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
    (r : R) : HasCoeffsIn R A (PowerSeries.C (algebraMap R A r)) := by
  refine ⟨PowerSeries.C r, ?_⟩
  change PowerSeries.map (algebraMap R A) (PowerSeries.C r) = PowerSeries.C (algebraMap R A r)
  exact PowerSeries.map_C (algebraMap R A) r

lemma powerSeriesMapAlgHom_injective (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    [FaithfulSMul R A] : Function.Injective (powerSeriesMapAlgHom R A) := by
  intro f g hfg
  change PowerSeries.map (algebraMap R A) f = PowerSeries.map (algebraMap R A) g at hfg
  exact (PowerSeries.map_injective (algebraMap R A) (FaithfulSMul.algebraMap_injective R A)) hfg

abbrev coeToComplexPowerSeries.ringHom (R : Type*) [CommRing R] [Algebra R ℂ] :
    PowerSeries R →+* PowerSeries ℂ := (powerSeriesMapAlgHom R ℂ).toRingHom

noncomputable abbrev RIntegralCPowerSeriesSubring (R : Type*) [CommRing R] [Algebra R ℂ] :
    Subring (PowerSeries ℂ) := (powerSeriesMapSubalgebra R ℂ).toSubring

abbrev IsRIntegralCPowerSeries (R : Type*) [CommRing R] [Algebra R ℂ] (x : PowerSeries ℂ) : Prop :=
  HasCoeffsIn R ℂ x

abbrev IsIntegralCPowerSeries (x : PowerSeries ℂ) : Prop :=
  HasCoeffsIn ℤ ℂ x

lemma isRIntegralCPowerSeries_iff_coeff (R : Type*) [CommRing R] [Algebra R ℂ]
    (f : PowerSeries ℂ) : IsRIntegralCPowerSeries R f ↔
      ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n f = algebraMap R ℂ r := by
  simpa [IsRIntegralCPowerSeries] using hasCoeffsIn_iff_coeff R ℂ f

noncomputable def toHasCoeffsInPowerSeries (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] {f : PowerSeries A} (hf : HasCoeffsIn R A f) : PowerSeries R :=
  Classical.choose hf

lemma map_toHasCoeffsInPowerSeries (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    {f : PowerSeries A} (hf : HasCoeffsIn R A f) :
    (powerSeriesMapAlgHom R A) (toHasCoeffsInPowerSeries R A hf) = f :=
  Classical.choose_spec hf

noncomputable def toRIntegralCPowerSeries (R : Type*) [CommRing R] [Algebra R ℂ]
    {f : PowerSeries ℂ} (hf : IsRIntegralCPowerSeries R f) : PowerSeries R :=
  toHasCoeffsInPowerSeries R ℂ hf

lemma coeToComplexPowerSeries_of_toRIntegralCPowerSeries (R : Type*) [CommRing R] [Algebra R ℂ]
    {f : PowerSeries ℂ} (hf : IsRIntegralCPowerSeries R f) :
    (coeToComplexPowerSeries.ringHom R) (toRIntegralCPowerSeries R hf) = f :=
  map_toHasCoeffsInPowerSeries R ℂ hf

namespace IntegralPowerSeries

noncomputable abbrev IntegralPowerSeriesSubring : Subring (PowerSeries ℂ) :=
  RIntegralCPowerSeriesSubring ℤ

abbrev IsIntegralPowerSeries (x : PowerSeries ℂ) : Prop :=
  IsIntegralCPowerSeries x

lemma int_iff (f : PowerSeries ℂ) : IsIntegralPowerSeries f ↔
    ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = z := by
  simpa [IsIntegralPowerSeries] using isRIntegralCPowerSeries_iff_coeff ℤ f

noncomputable abbrev toIntegralPowerSeries {f : PowerSeries ℂ}
    (hf : IsIntegralPowerSeries f) : PowerSeries ℤ :=
  toRIntegralCPowerSeries ℤ hf

lemma coeTo_of_toIntegralPowerSeries {f : PowerSeries ℂ} (hf : IsIntegralPowerSeries f) :
    (coeToComplexPowerSeries.ringHom ℤ) (toIntegralPowerSeries hf) = f := by
  simpa [toIntegralPowerSeries] using coeToComplexPowerSeries_of_toRIntegralCPowerSeries ℤ hf

lemma IsIntegralPowerSeriesmod {c : ℤ} (hc : c ≠ 0) {f : PowerSeries ℂ}
    (hf : IsIntegralPowerSeries f) (hmod : ∀ n : ℕ, Int.ModEq c
    ((toIntegralPowerSeries hf).coeff n) 0) : IsIntegralPowerSeries ((1 / c : ℂ) • f) := by
  rw [int_iff]
  intro n
  let g : PowerSeries ℤ := toIntegralPowerSeries hf
  have hg : (coeToComplexPowerSeries.ringHom ℤ) g = f := by
    simpa [g] using coeTo_of_toIntegralPowerSeries hf
  have h0 : Int.ModEq c (g.coeff n) 0 := by simpa [g] using hmod n
  have hdiv : c ∣ g.coeff n := by
    have hneg : c ∣ -g.coeff n := by
      simpa [Int.sub_eq_add_neg] using (Int.modEq_iff_dvd.mp h0)
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

end IntegralPowerSeries

section ModularForms

open UpperHalfPlane ModularFormClass

noncomputable instance modularFormModuleofIsScalarTower (R : Type*) [Semiring R] [Module R ℂ]
    [IsScalarTower R ℂ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [Γ.HasDetOne] :
    Module R (ModularForm Γ k) :=
  Function.Injective.module R ModularForm.coeHom DFunLike.coe_injective fun _ _ => rfl

lemma qExpansion_smul_algebra (R : Type*) [CommSemiring R] [Algebra R ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [Γ.HasDetOne] {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (r : R) (f : ModularForm Γ k) :
    qExpansion h (r • f) = (algebraMap R ℂ r) • qExpansion h f := by
  simpa using ModularForm.qExpansion_smul (F := ModularForm Γ k) hh hΓ (algebraMap R ℂ r) f

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
    simpa [Algebra.smul_def, PowerSeries.algebraMap_apply] using (hasCoeffsIn_smul R ℂ r hf)

lemma mem_modularFormQExpansionSubmodule_iff_coeff (R : Type*) [CommRing R] [Algebra R ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] (k : ℤ) (h : ℝ) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (f : ModularForm Γ k) :
    f ∈ modularFormQExpansionSubmodule R k h hh hΓ ↔
      ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n (qExpansion h f) = algebraMap R ℂ r := by
  simpa [modularFormQExpansionSubmodule] using (hasCoeffsIn_iff_coeff R ℂ (qExpansion h f))

noncomputable def modularFormQExpansionLinearMap (R : Type*) [CommRing R] [Algebra R ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] (k : ℤ) (h : ℝ) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) :
    modularFormQExpansionSubmodule R k h hh hΓ →ₗ[R] powerSeriesMapSubmodule R ℂ where
  toFun f := ⟨qExpansion h ((f : ModularForm Γ k)),
      (mem_powerSeriesMapSubmodule_iff R ℂ (qExpansion h f)).2 f.property⟩
  map_add' f g := by
    apply Subtype.ext
    change qExpansion h (f + g) = qExpansion h f + qExpansion h g
    simpa [ModularForm.coe_add] using
      (ModularForm.qExpansion_add hh hΓ (f : ModularForm Γ k) (g : ModularForm Γ k))
  map_smul' r f := by
    apply Subtype.ext
    change qExpansion h (r • f) = r • qExpansion h f
    have hs : qExpansion h (r • f) = (algebraMap R ℂ r) • qExpansion h f := by
      simpa using qExpansion_smul_algebra R hh hΓ r (f : ModularForm Γ k)
    simpa [Algebra.smul_def, PowerSeries.algebraMap_apply] using hs

end ModularForms

#min_imports
