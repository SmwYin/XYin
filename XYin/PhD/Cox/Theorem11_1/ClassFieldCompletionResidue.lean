/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldApproximation

/-! # Completed residue rings and normalized uniformizers

The completion and valuation steps used in Janusz V.3.1–3.4 and V.9. They are placed below
class-field arithmetic for reuse in completion degree comparisons.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors WithZero
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- A completed principal ideal is detected by its valuation bound. -/
theorem completed_mem_span_iff (v : HeightOneSpectrum (𝓞 K))
    (a b : v.adicCompletionIntegers K) :
    a ∈ Ideal.span {b} ↔
      Valued.v (a : v.adicCompletion K) ≤ Valued.v (b : v.adicCompletion K) := by
  rw [Ideal.mem_span_singleton,
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers K v).dvd_iff_le]
  rfl

/-- A global uniformizer remains a uniformizer in the completion. -/
theorem exists_completed_uniformizer (v : HeightOneSpectrum (𝓞 K)) :
    ∃ π : v.adicCompletionIntegers K,
      Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer' K
  refine ⟨algebraMap (𝓞 K) (v.adicCompletionIntegers K) π, ?_⟩
  change Valued.v (((π : K)) : v.adicCompletion K) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hπ

/-- The chosen normalized uniformizer generates the completed maximal ideal. -/
theorem completed_maximalIdeal_eq_span (v : HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletionIntegers K)
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π} := by
  ext a
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    completed_mem_span_iff K v a π, hπ]
  have ha : Valued.v (a : v.adicCompletion K) ≤ 1 := a.2
  constructor
  · intro h
    have hlt : Valued.v (a : v.adicCompletion K) < 1 := lt_of_le_of_ne ha h
    rcases eq_or_ne (Valued.v (a : v.adicCompletion K)) 0 with h0 | h0
    · rw [h0]
      exact zero_le'
    · rw [← WithZero.exp_log h0] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      exact WithZero.exp_le_exp.mpr (by omega)
  · intro h heq
    change Valued.v (a : v.adicCompletion K) = 1 at heq
    rw [heq] at h
    exact absurd h (not_le.mpr (by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by norm_num)))

/-- Powers of the completed maximal ideal match the normalized valuation filtration. -/
theorem completed_mem_maximalIdeal_pow_iff (v : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletionIntegers K) (t : ℕ) :
    a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t ↔
      Valued.v (a : v.adicCompletion K) ≤ WithZero.exp (-(t : ℤ)) := by
  obtain ⟨π, hπ⟩ := exists_completed_uniformizer K v
  rw [completed_maximalIdeal_eq_span K v π hπ, Ideal.span_singleton_pow,
    completed_mem_span_iff K v a (π ^ t)]
  have h : Valued.v ((π ^ t : v.adicCompletionIntegers K) : v.adicCompletion K) =
      WithZero.exp (-(t : ℤ)) := by
    rw [SubmonoidClass.coe_pow, map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  rw [h]

/-- The canonical map from global integers to a completed primary quotient. -/
def completedPrimaryResidueMap (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    𝓞 K →+* ((v.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t) :=
  (Ideal.Quotient.mk _).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))

/-- Reduction of a global integer agrees with its image in the completed quotient. -/
theorem completedPrimaryResidueMap_apply (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) (a : 𝓞 K) :
    completedPrimaryResidueMap K v t a = Ideal.Quotient.mk _
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) := by
  rfl

/-- Integer approximation proves surjectivity of the primary residue map. -/
theorem completedPrimaryResidueMap_surjective (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    Function.Surjective (completedPrimaryResidueMap K v t) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := exists_integer_completion_approx K v a t
  refine ⟨x, ?_⟩
  rw [completedPrimaryResidueMap_apply, Ideal.Quotient.eq, completed_mem_maximalIdeal_pow_iff]
  push_cast
  exact hx.le

/-- The primary residue kernel is the same prime power in the global integer ring. -/
theorem completedPrimaryResidueMap_ker (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    RingHom.ker (completedPrimaryResidueMap K v t) = v.asIdeal ^ t := by
  ext x
  rw [RingHom.mem_ker, completedPrimaryResidueMap_apply, Ideal.Quotient.eq_zero_iff_mem,
    completed_mem_maximalIdeal_pow_iff, ← v.intValuation_le_pow_iff_mem]
  have h : Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) x :
      v.adicCompletion K)) = v.intValuation x := by
    rw [← v.valuation_of_algebraMap (K := K)]
    change Valued.v (((x : K)) : v.adicCompletion K) = _
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : K)
  rw [h]

/-- Completion preserves each finite primary quotient. -/
theorem completed_primary_quotient_equiv (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    Nonempty (((𝓞 K) ⧸ v.asIdeal ^ t) ≃+*
      ((v.adicCompletionIntegers K) ⧸
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t)) := by
  exact ⟨(Ideal.quotEquivOfEq (completedPrimaryResidueMap_ker K v t)).symm.trans
    (RingHom.quotientKerEquivOfSurjective (completedPrimaryResidueMap_surjective K v t))⟩

/-- The completed primary quotient is finite, including the zero-depth zero ring. -/
theorem finite_completed_primary_quotient (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    Finite ((v.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t) := by
  obtain ⟨e⟩ := completed_primary_quotient_equiv K v t
  haveI : Finite (𝓞 K ⧸ v.asIdeal ^ t) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero t v.ne_bot)
  exact Finite.of_equiv _ e.toEquiv

/-- The normalized completed valuation on nonzero elements, with additive integers as target. -/
def localUnitValuation (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (Valued.v (R := v.adicCompletion K)).toMonoidHom)

/-- The integer-valued normalization recovers the original multiplicative valuation. -/
theorem localUnitValuation_apply (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    WithZero.exp (Multiplicative.toAdd (localUnitValuation K v u)) =
      Valued.v (u : v.adicCompletion K) := by
  simp [localUnitValuation, WithZero.exp]

/-- The valuation kernel is precisely the embedded local integer units. -/
theorem localUnitValuation_ker (v : HeightOneSpectrum (𝓞 K)) :
    (localUnitValuation K v).ker =
      (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom).range := by
  ext u
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  have hval : localUnitValuation K v u = 1 ↔ Valued.v (u : v.adicCompletion K) = 1 := by
    rw [← localUnitValuation_apply]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      have h1 : WithZero.exp (Multiplicative.toAdd (localUnitValuation K v u)) =
          WithZero.exp 0 := by rw [h, WithZero.exp_zero]
      exact WithZero.exp_injective h1
  rw [hval]
  constructor
  · intro h
    have hmem : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K := h.le
    have hunit : IsUnit (⟨u, hmem⟩ : v.adicCompletionIntegers K) :=
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr h
    exact ⟨hunit.unit, Units.ext rfl⟩
  · rintro ⟨w, rfl⟩
    exact IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp
      w.isUnit

/-- Powers of an inverse uniformizer give a homomorphic section of normalized valuation. -/
theorem exists_localUnitValuation_section (v : HeightOneSpectrum (𝓞 K)) :
    ∃ s : Multiplicative ℤ →* (v.adicCompletion K)ˣ,
      (localUnitValuation K v).comp s = MonoidHom.id _ := by
  obtain ⟨π, hπ⟩ := exists_completed_uniformizer K v
  have hπ0 : (π : v.adicCompletion K) ≠ 0 := fun h => by
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨zpowersHom _ (Units.mk0 _ hπ0)⁻¹, ?_⟩
  have h1 : localUnitValuation K v (Units.mk0 _ hπ0)⁻¹ = Multiplicative.ofAdd 1 := by
    have h2 : WithZero.exp (Multiplicative.toAdd (localUnitValuation K v (Units.mk0 _ hπ0)⁻¹)) =
        WithZero.exp (1 : ℤ) := by
      rw [localUnitValuation_apply, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hπ,
        ← WithZero.exp_neg, neg_neg]
    exact WithZero.exp_injective h2
  apply MonoidHom.ext_mint
  rw [MonoidHom.comp_apply, zpowersHom_apply, MonoidHom.id_apply, toAdd_ofAdd, zpow_one, h1]

/-- A split homomorphism of abelian groups gives the product with its kernel. -/
theorem split_hom_ker_equiv (G H : Type*) [CommGroup G] [CommGroup H]
    (f : G →* H) (s : H →* G) (hs : f.comp s = MonoidHom.id H) :
    ∃ e : G ≃* H × f.ker, ∀ g : f.ker, e g = (1, g) := by
  have hsf : ∀ h, f (s h) = h := fun h => DFunLike.congr_fun hs h
  let p : G →* f.ker :=
    { toFun := fun g => ⟨g * (s (f g))⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hsf, mul_inv_cancel]⟩
      map_one' := by
        ext
        simp
      map_mul' := fun a b => by
        ext
        simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
        ac_rfl }
  let e : G ≃* H × f.ker :=
    { toFun := fun g => (f g, p g)
      invFun := fun x => s x.1 * x.2
      left_inv := fun g => by
        change s (f g) * (g * (s (f g))⁻¹) = g
        rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]
      right_inv := fun x => by
        have hx2 : f (x.2 : G) = 1 := x.2.2
        refine Prod.ext ?_ (Subtype.ext ?_)
        · change f (s x.1 * x.2) = x.1
          rw [map_mul, hsf, hx2, mul_one]
        · change s x.1 * x.2 * (s (f (s x.1 * x.2)))⁻¹ = x.2
          rw [map_mul, hsf, hx2, mul_one, mul_comm, inv_mul_cancel_left]
      map_mul' := fun a b => by
        change (f (a * b), p (a * b)) = (f a, p a) * (f b, p b)
        rw [map_mul, map_mul]
        rfl }
  refine ⟨e, fun g => ?_⟩
  have hg : f (g : G) = 1 := g.2
  refine Prod.ext hg (Subtype.ext ?_)
  change (g : G) * (s (f g))⁻¹ = g
  rw [hg, map_one, inv_one, mul_one]

/-- Normalized valuation splits off a uniformizer power from a local field unit. -/
theorem exists_localFieldUnits_equiv (v : HeightOneSpectrum (𝓞 K)) :
    ∃ e : (v.adicCompletion K)ˣ ≃*
      Multiplicative ℤ × (v.adicCompletionIntegers K)ˣ,
      ∀ u : (v.adicCompletionIntegers K)ˣ,
        e (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u) = (1, u) := by
  obtain ⟨s, hs⟩ := exists_localUnitValuation_section K v
  obtain ⟨e₁, he₁⟩ := split_hom_ker_equiv _ _ (localUnitValuation K v) s hs
  have hinj : Function.Injective
      (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom) :=
    Units.map_injective Subtype.val_injective
  let e₂ : (localUnitValuation K v).ker ≃* (v.adicCompletionIntegers K)ˣ :=
    (MulEquiv.subgroupCongr (localUnitValuation_ker K v)).trans
      (MonoidHom.ofInjective hinj).symm
  refine ⟨e₁.trans (MulEquiv.prodCongr (MulEquiv.refl _) e₂), fun u => ?_⟩
  have hmem : Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u ∈
      (localUnitValuation K v).ker := by
    rw [localUnitValuation_ker]
    exact ⟨u, rfl⟩
  have h1 := he₁ ⟨_, hmem⟩
  rw [MulEquiv.trans_apply]
  change (MulEquiv.prodCongr (MulEquiv.refl _) e₂) (e₁ (⟨_, hmem⟩ :
    (localUnitValuation K v).ker)) = _
  rw [h1]
  refine Prod.ext rfl ?_
  change (MonoidHom.ofInjective hinj).symm _ = u
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext rfl

end Cox.ClassFieldTheory
