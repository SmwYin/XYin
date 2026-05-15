import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Basic

def powerSeriesMapAlgHom (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    PowerSeries R →ₐ[R] PowerSeries A :=
  { toRingHom := PowerSeries.map (algebraMap R A)
    commutes' := by
      intro r
      ext n
      simp [PowerSeries.algebraMap_apply] }

noncomputable def powerSeriesMapSubalgebra (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Subalgebra R (PowerSeries A) := (powerSeriesMapAlgHom R A).range

noncomputable abbrev powerSeriesMapSubmodule (R A : Type*) [CommSemiring R] [Semiring A]
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

noncomputable abbrev RIntegralPowerSeriesSubring (R : Type*) [CommRing R] [Algebra R ℂ] :
    Subring (PowerSeries ℂ) := (powerSeriesMapSubalgebra R ℂ).toSubring

abbrev IsRIntegralPowerSeries (R : Type*) [CommRing R] [Algebra R ℂ] (x : PowerSeries ℂ) : Prop :=
  HasCoeffsIn R ℂ x

lemma isRIntegralPowerSeries_iff_coeff (R : Type*) [CommRing R] [Algebra R ℂ]
    (f : PowerSeries ℂ) : IsRIntegralPowerSeries R f ↔
      ∀ n : ℕ, ∃ r : R, PowerSeries.coeff n f = algebraMap R ℂ r := by
  simpa [IsRIntegralPowerSeries] using hasCoeffsIn_iff_coeff R ℂ f

noncomputable def toHasCoeffsInPowerSeries (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] {f : PowerSeries A} (hf : HasCoeffsIn R A f) : PowerSeries R :=
  Classical.choose hf

lemma map_toHasCoeffsInPowerSeries (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    {f : PowerSeries A} (hf : HasCoeffsIn R A f) :
    (powerSeriesMapAlgHom R A) (toHasCoeffsInPowerSeries R A hf) = f :=
  Classical.choose_spec hf

noncomputable def toRIntegralPowerSeries (R : Type*) [CommRing R] [Algebra R ℂ]
    {f : PowerSeries ℂ} (hf : IsRIntegralPowerSeries R f) : PowerSeries R :=
  toHasCoeffsInPowerSeries R ℂ hf

lemma coeToComplexPowerSeries_of_toRIntegralPowerSeries (R : Type*) [CommRing R] [Algebra R ℂ]
    {f : PowerSeries ℂ} (hf : IsRIntegralPowerSeries R f) :
    (coeToComplexPowerSeries.ringHom R) (toRIntegralPowerSeries R hf) = f :=
  map_toHasCoeffsInPowerSeries R ℂ hf

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
  simpa using ModularFormClass.qExpansion_smul (F := ModularForm Γ k) hh hΓ (algebraMap R ℂ r) f

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
    rw [ModularFormClass.qExpansion_add hh hΓ]
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
      (ModularFormClass.qExpansion_add hh hΓ (f : ModularForm Γ k) (g : ModularForm Γ k))
  map_smul' r f := by
    apply Subtype.ext
    change qExpansion h (r • f) = r • qExpansion h f
    have hs : qExpansion h (r • f) = (algebraMap R ℂ r) • qExpansion h f := by
      simpa using qExpansion_smul_algebra R hh hΓ r (f : ModularForm Γ k)
    simpa [Algebra.smul_def, PowerSeries.algebraMap_apply] using hs

end ModularForms

#min_imports
