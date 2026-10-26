/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArithmetic
import XYin.PhD.Cox.Theorem11_1.ClassFieldCompletionResidue

/-! # Approximation in local ray quotients

Janusz V.3.1–3.4 and V.(9.12)–(9.13), with the depth-zero convention required by V.12.1.
The field-unit quotient is distinct from the integer-unit quotient.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors WithZero
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The global embedding on nonzero elements. -/
def completionUnitMap (v : HeightOneSpectrum (𝓞 K)) : Kˣ →* (v.adicCompletion K)ˣ :=
  Units.map (FinitePlace.embedding v).toMonoidHom

/-- The unit embedding has the specified underlying field embedding. -/
theorem completionUnitMap_apply (v : HeightOneSpectrum (𝓞 K)) (u : Kˣ) :
    (completionUnitMap K v u : v.adicCompletion K) = FinitePlace.embedding v (u : K) := by
  rfl

/-- The actual homomorphism into a completed ray quotient. -/
def localRayMap (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    Kˣ →* ((v.adicCompletion K)ˣ ⧸ localFieldUnitFiltration K v t) :=
  (QuotientGroup.mk' _).comp (completionUnitMap K v)





/-- Positive principal-unit depth is exactly the one-congruence valuation inequality. -/
theorem mem_localFieldUnitFiltration_iff (v : HeightOneSpectrum (𝓞 K))
    (t : ℕ) (ht : 0 < t) (u : (v.adicCompletion K)ˣ) :
    u ∈ localFieldUnitFiltration K v t ↔
      Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(t : ℤ)) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [localUnitFiltration, SetLike.mem_coe, MonoidHom.mem_ker] at hw
    have h1 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t)
        (w : v.adicCompletionIntegers K) = 1 := congrArg Units.val hw
    have h2 : (w : v.adicCompletionIntegers K) - 1 ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t :=
      Ideal.Quotient.eq.mp (h1.trans (map_one _).symm)
    have h3 := (completed_mem_maximalIdeal_pow_iff K v _ t).mp h2
    simpa using h3
  · intro h
    have hv1 : Valued.v (u : v.adicCompletion K) = 1 := by
      have hlt : Valued.v ((u : v.adicCompletion K) - 1) < Valued.v (1 : v.adicCompletion K) := by
        rw [map_one]
        exact lt_of_le_of_lt h (by
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
          omega)
      rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
    have hmem : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hv1.le
    have hunit : IsUnit (⟨u, hmem⟩ : v.adicCompletionIntegers K) :=
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hv1
    refine ⟨hunit.unit, ?_, Units.ext rfl⟩
    rw [localUnitFiltration, SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    change Ideal.Quotient.mk _ (⟨u, hmem⟩ : v.adicCompletionIntegers K) = 1
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    apply (completed_mem_maximalIdeal_pow_iff K v _ t).mpr
    simpa using h

/-- Depth zero is the full integer-unit group, hence valuation exactly one. -/
theorem mem_localFieldUnitFiltration_zero_iff (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    u ∈ localFieldUnitFiltration K v 0 ↔ Valued.v (u : v.adicCompletion K) = 1 := by
  rw [localFieldUnitFiltration_zero_eq_ker, MonoidHom.mem_ker, ← localUnitValuation_apply]
  constructor
  · intro h
    rw [h, toAdd_one, WithZero.exp_zero]
  · intro h
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact WithZero.exp_injective (h.trans WithZero.exp_zero.symm)

/-- The quotient map applied to a global unit is the class of its fixed embedding. -/
theorem localRayMap_apply (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) (u : Kˣ) :
    localRayMap K v t u = QuotientGroup.mk (completionUnitMap K v u) := by
  rfl

/-- A sufficiently small additive error gives the requested multiplicative ray error. -/
theorem exists_precision_for_localRay (v : HeightOneSpectrum (𝓞 K))
    (t : ℕ) (u : (v.adicCompletion K)ˣ) :
    ∃ N : ℤ, ∀ x : (v.adicCompletion K)ˣ,
      Valued.v ((x : v.adicCompletion K) - u) < WithZero.exp (-N) →
        x * u⁻¹ ∈ localFieldUnitFiltration K v t := by
  set k := Multiplicative.toAdd (localUnitValuation K v u) with hk
  have hu : Valued.v (u : v.adicCompletion K) = WithZero.exp k :=
    (localUnitValuation_apply K v u).symm
  have hu0 : (u : v.adicCompletion K) ≠ 0 := u.ne_zero
  refine ⟨t - k, fun x hx => ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [mem_localFieldUnitFiltration_zero_iff]
    have hlt : Valued.v ((x : v.adicCompletion K) - u) < Valued.v (u : v.adicCompletion K) := by
      rw [hu]
      simpa using hx
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
      Valuation.map_eq_of_sub_lt _ hlt, mul_inv_cancel₀ (by rw [hu]; exact WithZero.exp_ne_zero)]
  · rw [mem_localFieldUnitFiltration_iff K v t ht]
    have hdiv : ((x * u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
        ((x : v.adicCompletion K) - u) * (u : v.adicCompletion K)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    rw [hdiv, map_mul, map_inv₀, hu, ← WithZero.exp_neg]
    calc Valued.v ((x : v.adicCompletion K) - u) * WithZero.exp (-k) ≤
          WithZero.exp (-((t : ℤ) - k)) * WithZero.exp (-k) := mul_le_mul' hx.le le_rfl
      _ = WithZero.exp (-(t : ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          ring

/-- Approximation gives every class in the completed field-unit ray quotient. -/
theorem localRayMap_surjective (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    Function.Surjective (localRayMap K v t) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (localFieldUnitFiltration K v t) q
  obtain ⟨N, hN⟩ := exists_precision_for_localRay K v t y
  have hy : Valued.v (y : v.adicCompletion K) =
      WithZero.exp (Multiplicative.toAdd (localUnitValuation K v y)) :=
    (localUnitValuation_apply K v y).symm
  obtain ⟨x, hx⟩ := exists_field_completion_approx K v (y : v.adicCompletion K)
    (max N (-Multiplicative.toAdd (localUnitValuation K v y)))
  have hx1 : Valued.v (algebraMap K (v.adicCompletion K) x - y) < WithZero.exp (-N) :=
    lt_of_lt_of_le hx (WithZero.exp_le_exp.mpr (by omega))
  have hx2 : Valued.v (algebraMap K (v.adicCompletion K) x - y) <
      Valued.v (y : v.adicCompletion K) :=
    lt_of_lt_of_le hx (by
      rw [hy]
      exact WithZero.exp_le_exp.mpr (by omega))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_sub, Valuation.map_neg] at hx2
    exact lt_irrefl _ hx2
  have h := hN (completionUnitMap K v (Units.mk0 x hx0)) hx1
  refine ⟨Units.mk0 x hx0, ?_⟩
  rw [localRayMap_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have h' := (localFieldUnitFiltration K v t).inv_mem h
  rwa [mul_inv_rev, inv_inv, mul_comm] at h'

/-- For positive depth the global ray subgroup is exactly the completed quotient kernel. -/
theorem localRayMap_ker (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) (ht : 0 < t) :
    (localRayMap K v t).ker = rayElements K (v.asIdeal ^ t) := by
  ext u
  rw [MonoidHom.mem_ker, localRayMap_apply, QuotientGroup.eq_one_iff,
    mem_localFieldUnitFiltration_iff K v t ht, mem_rayElements_primePower_iff K v t ht u,
    completionUnitMap_apply, ← map_one (FinitePlace.embedding v), ← map_sub,
    FinitePlace.embedding_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- The prime-power global ray quotient is its completed field-unit quotient. -/
theorem primePower_ray_quotient_equiv (v : HeightOneSpectrum (𝓞 K))
    (t : ℕ) (ht : 0 < t) :
    Nonempty ((Kˣ ⧸ rayElements K (v.asIdeal ^ t)) ≃*
      ((v.adicCompletion K)ˣ ⧸ localFieldUnitFiltration K v t)) := by
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (localRayMap_ker K v t ht).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (localRayMap_surjective K v t))⟩

/-- Elements of one deeper prime-power ray group lie in the local ray kernel at every depth. -/
theorem rayElements_le_ker_localRayMap (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    rayElements K (v.asIdeal ^ (t + 1)) ≤ (localRayMap K v t).ker := by
  intro u hu
  have h := (mem_rayElements_primePower_iff K v (t + 1) t.succ_pos u).mp hu
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [MonoidHom.mem_ker, localRayMap_apply, QuotientGroup.eq_one_iff,
      mem_localFieldUnitFiltration_zero_iff, completionUnitMap_apply,
      FinitePlace.embedding_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hlt : v.valuation K ((u : K) - 1) < v.valuation K 1 := by
      rw [map_one]
      exact lt_of_le_of_lt h (by
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        omega)
    rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
  · rw [localRayMap_ker K v t ht, mem_rayElements_primePower_iff K v t ht u]
    exact h.trans (WithZero.exp_le_exp.mpr (by omega))

/-- Approximation can preserve a ray condition at a coprime modulus. -/
theorem localRayMap_ray_restriction_surjective (v : HeightOneSpectrum (𝓞 K))
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤) (t : ℕ) :
    Function.Surjective ((localRayMap K v t).comp (rayElements K m).subtype) := by
  intro q
  obtain ⟨u, hu⟩ := localRayMap_surjective K v t q
  have hcop' : v.asIdeal ^ (t + 1) ⊔ m = ⊤ := Ideal.pow_sup_eq_top hcop
  have hsup := rayElements_sup_of_coprime K (v.asIdeal ^ (t + 1)) m
    (pow_ne_zero _ v.ne_bot) hm hcop'
  have hmem : u⁻¹ ∈ rayElements K (v.asIdeal ^ (t + 1)) ⊔ rayElements K m := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hmem
  refine ⟨⟨b⁻¹, (rayElements K m).inv_mem hb⟩, ?_⟩
  change localRayMap K v t b⁻¹ = q
  have hbu : b⁻¹ = u * a := by
    rw [← inv_inv u, ← hab, mul_inv_rev, inv_mul_cancel_right]
  rw [hbu, map_mul, hu, MonoidHom.mem_ker.mp (rayElements_le_ker_localRayMap K v t ha), mul_one]

/-- The quotient identification used by Janusz V.12.1; depth zero is included. -/
theorem localRay_quotient_equiv_ray (v : HeightOneSpectrum (𝓞 K))
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (hcop : v.asIdeal ⊔ m = ⊤) (t : ℕ) :
    Nonempty (((v.adicCompletion K)ˣ ⧸ localFieldUnitFiltration K v t) ≃*
      (rayElements K m ⧸ (localFieldUnitFiltration K v t).comap
        ((completionUnitMap K v).comp (rayElements K m).subtype))) := by
  have hker : ((localRayMap K v t).comp (rayElements K m).subtype).ker =
      (localFieldUnitFiltration K v t).comap
        ((completionUnitMap K v).comp (rayElements K m).subtype) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.comp_apply, localRayMap_apply,
      QuotientGroup.eq_one_iff]
    rfl
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (localRayMap_ray_restriction_surjective K v m hm hcop t))).symm⟩







/-- Principal-unit filtrations have finite index in the full completed unit group. -/
theorem localUnitFiltration_finiteIndex (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    (localUnitFiltration K v t).FiniteIndex := by
  haveI := finite_completed_primary_quotient K v t
  exact Subgroup.finiteIndex_ker _







end Cox.ClassFieldTheory
