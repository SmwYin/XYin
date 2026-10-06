/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclic
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocalApproximation
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Local power indices in Janusz V.(9.12)–(9.15)

The cyclic group acts trivially in this source computation. These contracts do not
substitute the Galois action used for the local norm index.
-/
open NumberField IsDedekindDomain
open NumberField.InfinitePlace
open Cox.CyclicCohomology
open scoped nonZeroDivisors WithZero
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Janusz V.(9.14): the actual H¹/H⁰ ratio for the trivial power action. -/
def powerHerbrand (G : Type*) [CommGroup G] (n : ℕ) : ℚ :=
  (Nat.card (powMonoidHom n : G →* G).ker : ℚ) /
    (powMonoidHom n : G →* G).range.index

/-- The cyclic generator used for the source's trivial action. -/
def powerCycleGenerator (n : ℕ) : Multiplicative (ZMod n) :=
  Multiplicative.ofAdd 1

/-- The element one additively generates Z/nZ, including n=1. -/
theorem powerCycleGenerator_generates (n : ℕ) :
    ∀ γ : Multiplicative (ZMod n), γ ∈ Subgroup.zpowers (powerCycleGenerator n) := by
  intro γ
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd γ)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_zpow, powerCycleGenerator, toAdd_ofAdd, zsmul_one, hk]

/-- On a trivial action the cyclic norm is multiplication by the group order. -/
theorem trivial_power_norm (A : Type*) [AddCommGroup A] (n : ℕ) [NeZero n] :
    (Representation.trivial ℤ (Multiplicative (ZMod n)) A).norm =
      n • (LinearMap.id : A →ₗ[ℤ] A) := by
  ext x
  simp [Representation.norm, Finset.sum_const, Finset.card_univ, ZMod.card]

/-- Trivial-action Tate H⁰ is the actual quotient by nth powers. -/
theorem trivial_power_tateZero_equiv (G : Type*) [CommGroup G] (n : ℕ) [NeZero n] :
    Nonempty (tateZero (Representation.trivial ℤ (Multiplicative (ZMod n)) (Additive G))
      (powerCycleGenerator n) ≃+
        Additive (G ⧸ (powMonoidHom n : G →* G).range)) := by
  set ρ := Representation.trivial ℤ (Multiplicative (ZMod n)) (Additive G)
  have hD : ρ (powerCycleGenerator n) - LinearMap.id = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply, sub_eq_zero]
    rfl
  have hP : LinearMap.ker (ρ (powerCycleGenerator n) - LinearMap.id) = ⊤ := by
    rw [hD, LinearMap.ker_zero]
  have hR : LinearMap.range ρ.norm =
      (powMonoidHom n : G →* G).range.toAddSubgroup.toIntSubmodule := by
    rw [trivial_power_norm (Additive G) n]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Additive.toMul y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩
  let e1 := LinearEquiv.ofTop _ hP
  have hmap : ((LinearMap.range ρ.norm).comap
      (LinearMap.ker (ρ (powerCycleGenerator n) - LinearMap.id)).subtype).map
        e1.toLinearMap = (powMonoidHom n : G →* G).range.toAddSubgroup.toIntSubmodule := by
    rw [← hR]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hP ▸ Submodule.mem_top⟩, hx, rfl⟩
  exact ⟨(Submodule.Quotient.equiv _ _ e1 hmap).toAddEquiv.trans (additiveIntQuotientEquiv _)⟩

/-- Trivial-action Tate H¹ is the actual nth-power kernel. -/
theorem trivial_power_tateOne_equiv (G : Type*) [CommGroup G] (n : ℕ) [NeZero n] :
    Nonempty (tateOne (Representation.trivial ℤ (Multiplicative (ZMod n)) (Additive G))
      (powerCycleGenerator n) ≃+ Additive (powMonoidHom n : G →* G).ker) := by
  set ρ := Representation.trivial ℤ (Multiplicative (ZMod n)) (Additive G)
  have hD : ρ (powerCycleGenerator n) - LinearMap.id = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply, sub_eq_zero]
    rfl
  have hbot : (LinearMap.range (ρ (powerCycleGenerator n) - LinearMap.id)).comap
      (LinearMap.ker ρ.norm).subtype = ⊥ := by
    rw [hD, LinearMap.range_zero, Submodule.comap_bot, Submodule.ker_subtype]
  have hnorm := trivial_power_norm (Additive G) n
  have hmem : ∀ x : Additive G, x ∈ LinearMap.ker ρ.norm ↔
      Additive.toMul x ∈ (powMonoidHom n : G →* G).ker := by
    intro x
    rw [LinearMap.mem_ker, hnorm]
    rfl
  let e2 : LinearMap.ker ρ.norm ≃+ Additive (powMonoidHom n : G →* G).ker :=
    { toFun := fun x => Additive.ofMul ⟨Additive.toMul (x : Additive G), (hmem x).mp x.2⟩
      invFun := fun y => ⟨Additive.ofMul ((Additive.toMul y : (powMonoidHom n : G →* G).ker) : G),
        (hmem _).mpr (Additive.toMul y).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact ⟨(Submodule.quotEquivOfEqBot _ hbot).toAddEquiv.trans e2⟩

/-- The elementary power ratio equals the source's genuine Tate ratio. -/
theorem powerHerbrand_eq_tate (G : Type*) [CommGroup G] (n : ℕ) [NeZero n] :
    powerHerbrand G n =
      herbrandQuotient (Representation.trivial ℤ (Multiplicative (ZMod n)) (Additive G))
        (powerCycleGenerator n) := by
  obtain ⟨e0⟩ := trivial_power_tateZero_equiv G n
  obtain ⟨e1⟩ := trivial_power_tateOne_equiv G n
  rw [powerHerbrand, herbrandQuotient, Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv,
    Subgroup.index]
  rfl

/-- The two explicit finite power groups give finite Tate groups. -/
theorem finiteHerbrand_trivial_power (G : Type*) [CommGroup G] (n : ℕ) [NeZero n]
    [Finite (powMonoidHom n : G →* G).ker]
    [(powMonoidHom n : G →* G).range.FiniteIndex] :
    FiniteHerbrand (Representation.trivial ℤ (Multiplicative (ZMod n)) (Additive G))
      (powerCycleGenerator n) := by
  obtain ⟨e0⟩ := trivial_power_tateZero_equiv G n
  obtain ⟨e1⟩ := trivial_power_tateOne_equiv G n
  haveI : Finite (G ⧸ (powMonoidHom n : G →* G).range) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Finite (Additive (G ⧸ (powMonoidHom n : G →* G).range)) :=
    Finite.of_equiv _ Additive.ofMul
  haveI : Finite (Additive (powMonoidHom n : G →* G).ker) := Finite.of_equiv _ Additive.ofMul
  exact ⟨Finite.of_equiv _ e0.symm.toEquiv, Finite.of_equiv _ e1.symm.toEquiv⟩

/-- Janusz V.1.4 specialized to the trivial action: finite-index comparison. -/
theorem powerHerbrand_subgroup (G : Type*) [CommGroup G] (H : Subgroup G)
    [H.FiniteIndex] (n : ℕ) [NeZero n]
    [Finite (powMonoidHom n : G →* G).ker]
    [(powMonoidHom n : G →* G).range.FiniteIndex] :
    powerHerbrand H n = powerHerbrand G n := by
  let ρ := Representation.trivial ℤ (Multiplicative (ZMod n)) (Additive G)
  let W : Submodule ℤ (Additive G) := H.toAddSubgroup.toIntSubmodule
  have hW : ∀ γ, W ≤ W.comap (ρ γ) := fun _ _ hx => hx
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Finite (Additive (G ⧸ H)) := Finite.of_equiv _ Additive.ofMul
  haveI : Finite (Additive G ⧸ W) := Finite.of_equiv _ (additiveIntQuotientEquiv H).symm.toEquiv
  have hA := finiteHerbrand_trivial_power G n
  have hS := (finiteHerbrand_iff_subrepresentation ρ (powerCycleGenerator n) W hW
    (powerCycleGenerator_generates n)).mp hA
  have h1 := herbrandQuotient_subrepresentation ρ (powerCycleGenerator n) W hW
    (powerCycleGenerator_generates n) hA hS
  let e : W ≃+ Additive H :=
    { toFun := fun x => Additive.ofMul ⟨Additive.toMul (x : Additive G), x.2⟩
      invFun := fun y => ⟨Additive.ofMul ((Additive.toMul y : H) : G), (Additive.toMul y).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have h2 := herbrandQuotient_congr (powerCycleGenerator n) (ρ.subrepresentation W hW)
    (Representation.trivial ℤ (Multiplicative (ZMod n)) (Additive H)) e (fun _ _ => rfl)
  rw [powerHerbrand_eq_tate H n, powerHerbrand_eq_tate G n]
  exact h2.symm.trans h1

/-- A multiplicative equivalence preserves both groups in the power ratio. -/
theorem powerHerbrand_congr {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) : powerHerbrand G n = powerHerbrand H n := by
  have hker : (powMonoidHom n : H →* H).ker =
      (powMonoidHom n : G →* G).ker.map (e : G →* H) := by
    ext y
    simp only [MonoidHom.mem_ker, powMonoidHom_apply, Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [← map_pow, hy, map_one]
    · rintro ⟨x, hx, rfl⟩
      rw [MonoidHom.coe_coe, ← map_pow, hx, map_one]
  have hrange : (powMonoidHom n : H →* H).range =
      (powMonoidHom n : G →* G).range.map (e : G →* H) := by
    ext y
    simp only [MonoidHom.mem_range, powMonoidHom_apply, Subgroup.mem_map]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨(e.symm z) ^ n, ⟨e.symm z, rfl⟩, ?_⟩
      rw [MonoidHom.coe_coe, map_pow, e.apply_symm_apply]
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨e z, by rw [MonoidHom.coe_coe, map_pow]⟩
  rw [powerHerbrand, powerHerbrand, hker, hrange, Subgroup.card_map_of_injective e.injective,
    Subgroup.index_map_equiv]

/-- For a characteristic-zero additive ring, the power kernel is trivial and
its power cokernel is R/nR. -/
theorem additive_powerHerbrand (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (n : ℕ) (hn : 0 < n) :
    powerHerbrand (Multiplicative R) n =
      (Nat.card (R ⧸ Ideal.span {(n : R)}) : ℚ)⁻¹ := by
  have hn0 : (n : R) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hker : (powMonoidHom n : Multiplicative R →* Multiplicative R).ker = ⊥ := by
    ext x
    rw [MonoidHom.mem_ker, powMonoidHom_apply, Subgroup.mem_bot]
    constructor
    · intro hx
      have h : (n : R) * Multiplicative.toAdd x = 0 := by
        have h' := congrArg Multiplicative.toAdd hx
        rwa [toAdd_pow, toAdd_one, nsmul_eq_mul] at h'
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      exact (mul_eq_zero.mp h).resolve_left hn0
    · rintro rfl
      exact one_pow n
  have hr : (powMonoidHom n : Multiplicative R →* Multiplicative R).range =
      AddSubgroup.toSubgroup (Ideal.span {(n : R)}).toAddSubgroup := by
    ext x
    rw [MonoidHom.mem_range]
    change _ ↔ Multiplicative.toAdd x ∈ Ideal.span {(n : R)}
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Multiplicative.toAdd y, by rw [powMonoidHom_apply, toAdd_pow, nsmul_eq_mul, mul_comm]⟩
    · rintro ⟨a, ha⟩
      refine ⟨Multiplicative.ofAdd a, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [powMonoidHom_apply, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_comm, ha]
  rw [powerHerbrand, hker, hr, AddSubgroup.index_toSubgroup, Subgroup.card_bot, Nat.cast_one,
    one_div]
  rfl

/-- Multiplication by a nonzero principal generator identifies its ideal with the ring. -/
theorem nonzero_principal_ideal_addEquiv (R : Type*) [CommRing R] [IsDomain R]
    (I : Ideal R) [I.IsPrincipal] (hI : I ≠ ⊥) : Nonempty (I ≃+ R) := by
  set a := Submodule.IsPrincipal.generator I
  have ha : a ≠ 0 := fun h => hI ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr h)
  have hspan : Ideal.span {a} = I := Ideal.span_singleton_generator I
  have hmem : ∀ r : R, r * a ∈ I := fun r => by
    rw [← hspan]
    exact Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩
  let f : R →+ I :=
    { toFun := fun r => ⟨r * a, hmem r⟩
      map_zero' := Subtype.ext (zero_mul a)
      map_add' := fun r s => Subtype.ext (add_mul r s a) }
  have hf : Function.Bijective f := by
    refine ⟨fun r s h => mul_right_cancel₀ ha (congrArg Subtype.val h), fun x => ?_⟩
    have hx : (x : R) ∈ Ideal.span {a} := by
      rw [hspan]
      exact x.2
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hx
    exact ⟨r, Subtype.ext hr⟩
  exact ⟨(AddEquiv.ofBijective f hf).symm⟩

/-- The completed integer-ring residue map used in the local-to-global comparison. -/
def completionResidueMap (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    𝓞 K →+* ((v.adicCompletionIntegers K) ⧸
      Ideal.span {(n : v.adicCompletionIntegers K)}) :=
  (Ideal.Quotient.mk _).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))

/-- The completion residue homomorphism is the expected quotient reduction. -/
theorem completionResidueMap_apply (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (a : 𝓞 K) :
    completionResidueMap K v n a = Ideal.Quotient.mk _
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) := by
  rfl

/-- The exponent of a finite prime in the integer ideal (n). -/
def nthPrimeExponent (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(n : 𝓞 K)})).factors

/-- The valuation of n records exactly its primary ideal exponent. -/
theorem completion_valuation_natCast (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) :
    Valued.v (n : v.adicCompletion K) =
      WithZero.exp (-(nthPrimeExponent K v n : ℤ)) := by
  have hn0 : (n : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h : Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) (n : 𝓞 K) :
      v.adicCompletion K)) = v.intValuation (n : 𝓞 K) := by
    rw [← v.valuation_of_algebraMap (K := K)]
    change Valued.v ((((n : 𝓞 K) : K)) : v.adicCompletion K) = _
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((n : 𝓞 K) : K)
  rw [map_natCast] at h
  push_cast at h
  rw [h, v.intValuation_if_neg hn0]
  rfl

/-- Integral approximation inside the completion gives every residue class. -/
theorem completionResidueMap_surjective (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) : Function.Surjective (completionResidueMap K v n) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := exists_integer_completion_approx K v a (nthPrimeExponent K v n)
  refine ⟨x, ?_⟩
  rw [completionResidueMap_apply, Ideal.Quotient.eq, completed_mem_span_iff]
  push_cast
  rw [completion_valuation_natCast K v n hn]
  exact hx.le

/-- The kernel is exactly the v-primary factor of the ideal (n). -/
theorem completionResidueMap_ker (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) :
    RingHom.ker (completionResidueMap K v n) = v.asIdeal ^ nthPrimeExponent K v n := by
  ext a
  rw [RingHom.mem_ker, completionResidueMap_apply, Ideal.Quotient.eq_zero_iff_mem,
    completed_mem_span_iff, ← v.intValuation_le_pow_iff_mem]
  have h : Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) a :
      v.adicCompletion K)) = v.intValuation a := by
    rw [← v.valuation_of_algebraMap (K := K)]
    change Valued.v (((a : K)) : v.adicCompletion K) = _
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a : K)
  have hn' : Valued.v ((n : v.adicCompletionIntegers K) : v.adicCompletion K) =
      WithZero.exp (-(nthPrimeExponent K v n : ℤ)) := by
    push_cast
    exact completion_valuation_natCast K v n hn
  rw [h, hn']

/-- Completing at v does not change the relevant primary quotient. -/
theorem completion_integer_quotient_equiv (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) :
    Nonempty (((𝓞 K) ⧸ v.asIdeal ^ nthPrimeExponent K v n) ≃+*
      ((v.adicCompletionIntegers K) ⧸ Ideal.span {(n : v.adicCompletionIntegers K)})) := by
  exact ⟨(Ideal.quotEquivOfEq (completionResidueMap_ker K v n hn)).symm.trans
    (RingHom.quotientKerEquivOfSurjective (completionResidueMap_surjective K v n hn))⟩

/-- The local additive n-quotient is finite, even if n is a local unit. -/
theorem finite_completion_integer_quotient (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) :
    Finite ((v.adicCompletionIntegers K) ⧸ Ideal.span {(n : v.adicCompletionIntegers K)}) := by
  obtain ⟨e⟩ := completion_integer_quotient_equiv K v n hn
  haveI : Finite (𝓞 K ⧸ v.asIdeal ^ nthPrimeExponent K v n) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ v.ne_bot)
  exact Finite.of_equiv _ e.toEquiv

/-- The given primitive root embeds as a primitive root in the local integer units. -/
theorem exists_local_primitive_root (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    ∃ z : v.adicCompletionIntegers K, IsPrimitiveRoot z n := by
  have hinj : Function.Injective (FinitePlace.embedding (K := K) v) :=
    (FinitePlace.embedding (K := K) v).injective
  have hζv := hζ.map_of_injective hinj
  have hval : Valued.v (FinitePlace.embedding v ζ) = 1 := by
    have h1 : Valued.v (FinitePlace.embedding v ζ) ^ n = 1 := by
      rw [← map_pow, hζv.pow_eq_one, map_one]
    exact (pow_eq_one_iff.mp h1).resolve_right hn.ne'
  have hmem : FinitePlace.embedding v ζ ∈ v.adicCompletionIntegers K :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hval.le
  exact ⟨⟨_, hmem⟩, IsPrimitiveRoot.of_map_of_injective
    (f := (v.adicCompletionIntegers K).subtype) hζv Subtype.val_injective⟩

/-- Janusz V.(9.14): H¹ of the trivial action has cardinal n. -/
theorem card_local_power_kernel (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →*
      (v.adicCompletionIntegers K)ˣ).ker = n := by
  obtain ⟨z, hz⟩ := exists_local_primitive_root K v n hn ζ hζ
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [← rootsOfUnity_eq_ker, Nat.card_eq_fintype_card, hz.card_rootsOfUnity]

/-- Finiteness of the kernel follows from its positive cardinal. -/
theorem finite_local_power_kernel (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Finite (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →*
      (v.adicCompletionIntegers K)ˣ).ker := by
  exact Nat.finite_of_card_ne_zero (by rw [card_local_power_kernel K v n hn ζ hζ]; exact hn.ne')

/-- Janusz V.3.6: sufficiently deep local principal units are nth powers. -/
theorem localUnitFiltration_le_nthPowers (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, localUnitFiltration K v t ≤
      (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →*
        (v.adicCompletionIntegers K)ˣ).range := by
  exact LocalCyclic.deep_units_are_powers K v n hn

/-- Deep nth powers and finite filtration index make the full power quotient finite. -/
theorem local_power_finiteIndex (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) :
    (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →*
      (v.adicCompletionIntegers K)ˣ).range.FiniteIndex := by
  obtain ⟨t₀, ht₀⟩ := localUnitFiltration_le_nthPowers K v n hn
  haveI := finite_completed_primary_quotient K v t₀
  haveI : Finite ((v.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t₀)ˣ :=
    Finite.of_injective _ Units.val_injective
  haveI : (localUnitFiltration K v t₀).FiniteIndex := by
    rw [localUnitFiltration]
    exact Subgroup.finiteIndex_ker _
  exact Subgroup.finiteIndex_of_le (ht₀ t₀ le_rfl)

/-- The source compares full units with a sufficiently deep logarithmic ideal. -/
theorem local_powerHerbrand (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    powerHerbrand (v.adicCompletionIntegers K)ˣ n =
      (Nat.card ((v.adicCompletionIntegers K) ⧸
        Ideal.span {(n : v.adicCompletionIntegers K)}) : ℚ)⁻¹ := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨t₀, ht₀⟩ := LocalCyclic.exists_logIso K v
  obtain ⟨E, -, -⟩ := ht₀ t₀ le_rfl
  haveI := finite_local_power_kernel K v n hn ζ hζ
  haveI := local_power_finiteIndex K v n hn
  haveI := finite_completed_primary_quotient K v t₀
  haveI : Finite ((v.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t₀)ˣ :=
    Finite.of_injective _ Units.val_injective
  haveI : (localUnitFiltration K v t₀).FiniteIndex := by
    rw [localUnitFiltration]
    exact Subgroup.finiteIndex_ker _
  have hI : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ t₀ ≠ ⊥ :=
    pow_ne_zero _ (IsDiscreteValuationRing.not_a_field _)
  obtain ⟨f⟩ := nonzero_principal_ideal_addEquiv (v.adicCompletionIntegers K) _ hI
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  haveI : CharZero (v.adicCompletionIntegers K) := ⟨fun a b h => by
    have h' := congrArg (fun x : v.adicCompletionIntegers K => (x : v.adicCompletion K)) h
    simp only [SubringClass.coe_natCast] at h'
    exact_mod_cast h'⟩
  rw [← powerHerbrand_subgroup _ (localUnitFiltration K v t₀) n, powerHerbrand_congr E n,
    powerHerbrand_congr (AddEquiv.toMultiplicative f) n,
    additive_powerHerbrand (v.adicCompletionIntegers K) n hn]

/-- Janusz V.(9.14)–(9.15): local logarithms and the Herbrand quotient determine
the local unit power index. -/
theorem local_unit_power_index (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →*
      (v.adicCompletionIntegers K)ˣ).range.index =
      n * Nat.card ((v.adicCompletionIntegers K) ⧸
        Ideal.span {(n : v.adicCompletionIntegers K)}) := by
  have h := local_powerHerbrand K v n hn ζ hζ
  rw [powerHerbrand, card_local_power_kernel K v n hn ζ hζ] at h
  haveI := local_power_finiteIndex K v n hn
  haveI := finite_completion_integer_quotient K v n hn
  have hI : ((powMonoidHom n : (v.adicCompletionIntegers K)ˣ →*
      (v.adicCompletionIntegers K)ˣ).range.index : ℚ) ≠ 0 := by
    exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  have hc : (Nat.card ((v.adicCompletionIntegers K) ⧸
      Ideal.span {(n : v.adicCompletionIntegers K)}) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [div_eq_iff hI, inv_mul_eq_div, eq_div_iff hc] at h
  exact_mod_cast h.symm

/-- Quotienting by powers and a subgroup is the power quotient of the subgroup quotient. -/
theorem quotient_sup_powers_equiv (G : Type*) [CommGroup G] (H : Subgroup G) (n : ℕ) :
    Nonempty ((G ⧸ ((powMonoidHom n : G →* G).range ⊔ H)) ≃*
      ((G ⧸ H) ⧸ (powMonoidHom n : (G ⧸ H) →* (G ⧸ H)).range)) := by
  have hmap : ((powMonoidHom n : G →* G).range ⊔ H).map (QuotientGroup.mk' H) =
      (powMonoidHom n : (G ⧸ H) →* (G ⧸ H)).range := by
    ext q
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨a, ⟨c, rfl⟩, b, hb, rfl⟩ := Subgroup.mem_sup.mp hg
      refine ⟨QuotientGroup.mk c, ?_⟩
      rw [powMonoidHom_apply, map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff b).mpr hb, mul_one, powMonoidHom_apply, QuotientGroup.mk_pow]
    · rintro ⟨q', rfl⟩
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q'
      exact ⟨c ^ n, Subgroup.mem_sup_left ⟨c, rfl⟩, rfl⟩
  exact ⟨(QuotientGroup.quotientQuotientEquivQuotient H _ le_sup_right).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hmap)⟩

/-- A group equivalence transports its quotient by nth powers. -/
theorem quotient_powers_congr {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    Nonempty ((G ⧸ (powMonoidHom n : G →* G).range) ≃*
      (H ⧸ (powMonoidHom n : H →* H).range)) := by
  have hmap : (powMonoidHom n : G →* G).range.map (e : G →* H) =
      (powMonoidHom n : H →* H).range := by
    ext y
    simp only [MonoidHom.mem_range, powMonoidHom_apply, Subgroup.mem_map]
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨e z, by rw [MonoidHom.coe_coe, map_pow]⟩
    · rintro ⟨z, rfl⟩
      refine ⟨(e.symm z) ^ n, ⟨e.symm z, rfl⟩, ?_⟩
      rw [MonoidHom.coe_coe, map_pow, e.apply_symm_apply]
  exact ⟨QuotientGroup.congr _ _ e hmap⟩

/-- The free valuation factor modulo nth powers has n elements. -/
theorem quotient_int_powers_equiv (n : ℕ) :
    Nonempty ((Multiplicative ℤ ⧸
      (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range) ≃*
        Multiplicative (ZMod n)) := by
  let φ : Multiplicative ℤ →* Multiplicative (ZMod n) := (Int.castAddHom (ZMod n)).toMultiplicative
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
    exact ⟨Multiplicative.ofAdd k, congrArg Multiplicative.ofAdd hk⟩
  have hker : (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range = φ.ker := by
    ext x
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    change _ ↔ Multiplicative.ofAdd (((Multiplicative.toAdd x : ℤ) : ZMod n)) = 1
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Multiplicative.toAdd y, by rw [powMonoidHom_apply, toAdd_pow, nsmul_eq_mul]⟩
    · rintro ⟨k, hk⟩
      refine ⟨Multiplicative.ofAdd k, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [powMonoidHom_apply, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, hk]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

/-- The quotient of a product by nth powers is the product of the power quotients. -/
theorem quotient_prod_powers_equiv (G H : Type*) [CommGroup G] [CommGroup H] (n : ℕ) :
    Nonempty (((G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range) ≃*
      (G ⧸ (powMonoidHom n : G →* G).range) ×
        (H ⧸ (powMonoidHom n : H →* H).range)) := by
  let φ := (QuotientGroup.mk' (powMonoidHom n : G →* G).range).prodMap
    (QuotientGroup.mk' (powMonoidHom n : H →* H).range)
  have hφ : Function.Surjective φ := by
    rintro ⟨a, b⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ b
    exact ⟨(x, y), rfl⟩
  have hker : (powMonoidHom n : (G × H) →* (G × H)).range = φ.ker := by
    ext ⟨g, h⟩
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    change _ ↔ ((QuotientGroup.mk g : G ⧸ (powMonoidHom n : G →* G).range),
      (QuotientGroup.mk h : H ⧸ (powMonoidHom n : H →* H).range)) = 1
    rw [Prod.mk_eq_one, QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩
      rw [powMonoidHom_apply, Prod.pow_mk, Prod.mk.injEq] at hab
      exact ⟨⟨a, hab.1⟩, ⟨b, hab.2⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨(a, b), ?_⟩
      rw [powMonoidHom_apply, Prod.pow_mk]
      exact Prod.ext ha hb
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

/-- The uniformizer splitting preserves the prescribed principal-unit subgroup. -/
theorem local_ray_split_equiv (v : HeightOneSpectrum (𝓞 K)) (t : ℕ) :
    Nonempty (((v.adicCompletion K)ˣ ⧸ localFieldUnitFiltration K v t) ≃*
      Multiplicative ℤ × ((v.adicCompletionIntegers K)ˣ ⧸ localUnitFiltration K v t)) := by
  obtain ⟨e, he⟩ := exists_localFieldUnits_equiv K v
  let Φ : (v.adicCompletion K)ˣ →* Multiplicative ℤ ×
      ((v.adicCompletionIntegers K)ˣ ⧸ localUnitFiltration K v t) :=
    ((MonoidHom.id _).prodMap (QuotientGroup.mk' (localUnitFiltration K v t))).comp e.toMonoidHom
  have hΦ : Function.Surjective Φ := by
    rintro ⟨a, b⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ b
    refine ⟨e.symm (a, c), ?_⟩
    change ((MonoidHom.id _).prodMap (QuotientGroup.mk' (localUnitFiltration K v t)))
      (e (e.symm (a, c))) = _
    rw [e.apply_symm_apply]
    rfl
  have hker : Φ.ker = localFieldUnitFiltration K v t := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (e x).1 = 1 := congrArg Prod.fst hx
      have h2 : (e x).2 ∈ localUnitFiltration K v t :=
        (QuotientGroup.eq_one_iff _).mp (congrArg Prod.snd hx)
      refine ⟨(e x).2, h2, ?_⟩
      apply e.injective
      rw [he]
      exact Prod.ext h1.symm rfl
    · rintro ⟨u, hu, rfl⟩
      change ((MonoidHom.id _).prodMap (QuotientGroup.mk' (localUnitFiltration K v t)))
        (e (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u)) = 1
      rw [he]
      exact Prod.ext rfl ((QuotientGroup.eq_one_iff u).mpr hu)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Φ hΦ)⟩

/-- Janusz V.(9.12)–(9.13): valuation and unit factors in the prime-power quotient. -/
theorem primePower_power_quotient_equiv (v : HeightOneSpectrum (𝓞 K))
    (n t : ℕ) (ht : 0 < t) :
    Nonempty ((Kˣ ⧸ (nthPowers K n ⊔ rayElements K (v.asIdeal ^ t))) ≃*
      Multiplicative (ZMod n) × ((v.adicCompletionIntegers K)ˣ ⧸
        ((powMonoidHom n : (v.adicCompletionIntegers K)ˣ →*
          (v.adicCompletionIntegers K)ˣ).range ⊔ localUnitFiltration K v t))) := by
  obtain ⟨e1⟩ := quotient_sup_powers_equiv Kˣ (rayElements K (v.asIdeal ^ t)) n
  obtain ⟨e2⟩ := primePower_ray_quotient_equiv K v t ht
  obtain ⟨e3⟩ := quotient_powers_congr e2 n
  obtain ⟨e4⟩ := local_ray_split_equiv K v t
  obtain ⟨e5⟩ := quotient_powers_congr e4 n
  obtain ⟨e6⟩ := quotient_prod_powers_equiv (Multiplicative ℤ)
    ((v.adicCompletionIntegers K)ˣ ⧸ localUnitFiltration K v t) n
  obtain ⟨e7⟩ := quotient_int_powers_equiv n
  obtain ⟨e8⟩ := quotient_sup_powers_equiv (v.adicCompletionIntegers K)ˣ
    (localUnitFiltration K v t) n
  exact ⟨e1.trans (e3.trans (e5.trans (e6.trans (MulEquiv.prodCongr e7 e8.symm))))⟩

-- `hn` is kept: the planned signature includes it.
set_option linter.unusedVariables false in
/-- The source's index product follows by counting the actual quotient equivalence. -/
theorem powerCongruenceIndex_primePower_eq (v : HeightOneSpectrum (𝓞 K))
    (n t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    powerCongruenceIndex K n (v.asIdeal ^ t) = n *
      ((powMonoidHom n : (v.adicCompletionIntegers K)ˣ →*
        (v.adicCompletionIntegers K)ˣ).range ⊔ localUnitFiltration K v t).index := by
  obtain ⟨e⟩ := primePower_power_quotient_equiv K v n t ht
  rw [powerCongruenceIndex, Subgroup.index, Nat.card_congr e.toEquiv, Nat.card_prod,
    Subgroup.index]
  congr 1
  exact Nat.card_zmod n

/-- Janusz V.(9.12)–(9.15): sufficiently deep prime-power moduli have the local index. -/
theorem powerCongruenceIndex_primePower (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀,
      powerCongruenceIndex K n (v.asIdeal ^ t) =
        n ^ 2 * Nat.card ((v.adicCompletionIntegers K) ⧸
          Ideal.span {(n : v.adicCompletionIntegers K)}) := by
  obtain ⟨c, hc⟩ := localUnitFiltration_le_nthPowers K v n hn
  refine ⟨max 1 c, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) ht)
  have hct : c ≤ t := le_trans (le_max_right _ _) ht
  rw [powerCongruenceIndex_primePower_eq K v n t hn ht0, sup_eq_left.mpr (hc t hct),
    local_unit_power_index K v n hn ζ hζ]
  ring

/-- Coprime ray conditions give the source's actual product of ray quotients. -/
theorem ray_quotient_CRT (m₁ m₂ : Ideal (𝓞 K)) (hm₁ : m₁ ≠ ⊥) (hm₂ : m₂ ≠ ⊥)
    (hcop : m₁ ⊔ m₂ = ⊤) :
    Nonempty ((Kˣ ⧸ rayElements K (m₁ * m₂)) ≃*
      (Kˣ ⧸ rayElements K m₁) × (Kˣ ⧸ rayElements K m₂)) := by
  have hmn : m₁ * m₂ = m₁ ⊓ m₂ :=
    Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr hcop)
  obtain ⟨e⟩ := quotient_inf_equiv_prod Kˣ _ _ (rayElements_sup_of_coprime K m₁ m₂ hm₁ hm₂ hcop)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (by rw [hmn, rayElements_inf K m₁ m₂ hm₁ hm₂])).trans
    e⟩

/-- CRT commutes with the power quotient, by surjectivity of the underlying ray map. -/
theorem power_ray_quotient_CRT (n : ℕ) (m₁ m₂ : Ideal (𝓞 K))
    (hm₁ : m₁ ≠ ⊥) (hm₂ : m₂ ≠ ⊥) (hcop : m₁ ⊔ m₂ = ⊤) :
    Nonempty ((Kˣ ⧸ (nthPowers K n ⊔ rayElements K (m₁ * m₂))) ≃*
      (Kˣ ⧸ (nthPowers K n ⊔ rayElements K m₁)) ×
        (Kˣ ⧸ (nthPowers K n ⊔ rayElements K m₂))) := by
  obtain ⟨e1⟩ := quotient_sup_powers_equiv Kˣ (rayElements K (m₁ * m₂)) n
  obtain ⟨e2⟩ := ray_quotient_CRT K m₁ m₂ hm₁ hm₂ hcop
  obtain ⟨e3⟩ := quotient_powers_congr e2 n
  obtain ⟨e4⟩ := quotient_prod_powers_equiv (Kˣ ⧸ rayElements K m₁) (Kˣ ⧸ rayElements K m₂) n
  obtain ⟨f1⟩ := quotient_sup_powers_equiv Kˣ (rayElements K m₁) n
  obtain ⟨f2⟩ := quotient_sup_powers_equiv Kˣ (rayElements K m₂) n
  exact ⟨e1.trans (e3.trans (e4.trans (MulEquiv.prodCongr f1.symm f2.symm)))⟩

-- `hn` is kept: the planned signature includes it.
set_option linter.unusedVariables false in
/-- The CRT separates relatively prime modulus contributions to the global power index. -/
theorem powerCongruenceIndex_mul (n : ℕ) (hn : 0 < n)
    (m₁ m₂ : Ideal (𝓞 K)) (hm₁ : m₁ ≠ ⊥) (hm₂ : m₂ ≠ ⊥)
    (hcoprime : m₁ ⊔ m₂ = ⊤) :
    powerCongruenceIndex K n (m₁ * m₂) =
      powerCongruenceIndex K n m₁ * powerCongruenceIndex K n m₂ := by
  obtain ⟨e⟩ := power_ray_quotient_CRT K n m₁ m₂ hm₁ hm₂ hcoprime
  rw [powerCongruenceIndex, powerCongruenceIndex, powerCongruenceIndex, Subgroup.index,
    Subgroup.index, Subgroup.index, Nat.card_congr e.toEquiv, Nat.card_prod]

-- `hn` is kept: the planned signature includes it.
set_option linter.unusedVariables false in
/-- Janusz I.8.6, used in V.9: reduction of an integral basis modulo n. -/
theorem card_integer_quotient (n : ℕ) (hn : 0 < n) :
    Nat.card ((𝓞 K) ⧸ Ideal.span {(n : 𝓞 K)}) = n ^ Module.finrank ℚ K := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
    show ((n : 𝓞 K)) = algebraMap ℤ (𝓞 K) (n : ℤ) by simp, Algebra.norm_algebraMap,
    RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]

/-- The exponent is zero at a prime outside the chosen support of n. -/
theorem nthPrimeExponent_eq_zero (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (hS : CoversNthPrimes K n S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) : nthPrimeExponent K v n = 0 := by
  classical
  by_contra h
  have hn0 : Ideal.span {(n : 𝓞 K)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  have hdvd := (Associates.count_ne_zero_iff_dvd hn0 v.irreducible).mp h
  have hle : Ideal.span {(n : 𝓞 K)} ≤ v.asIdeal := Ideal.le_of_dvd hdvd
  exact hv (hS v (hle (Ideal.mem_span_singleton_self _)))

/-- Unique factorization reconstructs the ideal (n) from its chosen finite prime support. -/
theorem prod_nthPrimeExponent (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (hS : CoversNthPrimes K n S) :
    (∏ v ∈ S, v.asIdeal ^ nthPrimeExponent K v n) = Ideal.span {(n : 𝓞 K)} := by
  classical
  have hn0 : Ideal.span {(n : 𝓞 K)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hn0]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  · rfl
  · intro v hv
    by_contra hvS
    apply hv
    change v.asIdeal ^ nthPrimeExponent K v n = 1
    rw [nthPrimeExponent_eq_zero K S n hn hS v hvS, pow_zero]

/-- The global n-quotient is the product of the local completed n-quotients. -/
theorem integer_quotient_equiv_local_product (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (hS : CoversNthPrimes K n S) :
    Nonempty (((𝓞 K) ⧸ Ideal.span {(n : 𝓞 K)}) ≃+*
      ((v : S) → (v.1.adicCompletionIntegers K) ⧸
        Ideal.span {(n : v.1.adicCompletionIntegers K)})) := by
  classical
  have hcop : Pairwise (Function.onFun IsCoprime fun v : S =>
      (v : HeightOneSpectrum (𝓞 K)).asIdeal ^ nthPrimeExponent K v n) := by
    intro a b hab
    exact HeightOneSpectrum.isCoprime_pow_of_ne (a : HeightOneSpectrum (𝓞 K)) b
      (fun h => hab (Subtype.ext h)) _ _
  have hinf : Ideal.span {(n : 𝓞 K)} =
      ⨅ v : S, (v : HeightOneSpectrum (𝓞 K)).asIdeal ^ nthPrimeExponent K v n := by
    rw [← prod_nthPrimeExponent K S n hn hS, ← Finset.prod_coe_sort S]
    have h := Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := (Finset.univ : Finset S))
      (J := fun v : S => (v : HeightOneSpectrum (𝓞 K)).asIdeal ^ nthPrimeExponent K v n)
      (fun a _ b _ hab => hcop hab)
    rw [h]
    simp only [Finset.mem_univ, iInf_true]
  exact ⟨(Ideal.quotEquivOfEq hinf).trans ((Ideal.quotientInfRingEquivPiQuotient _ hcop).trans
    (RingEquiv.piCongrRight fun v => (completion_integer_quotient_equiv K v.1 n hn).some))⟩

/-- Janusz V.9: CRT and local-to-global residue comparison multiply the local indices. -/
theorem product_local_integer_quotient (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (hS : CoversNthPrimes K n S) :
    (∏ v ∈ S, Nat.card ((v.adicCompletionIntegers K) ⧸
      Ideal.span {(n : v.adicCompletionIntegers K)})) = n ^ Module.finrank ℚ K := by
  obtain ⟨e⟩ := integer_quotient_equiv_local_product K S n hn hS
  rw [← card_integer_quotient K n hn, Nat.card_congr e.toEquiv, Nat.card_pi,
    Finset.prod_coe_sort S (fun v => Nat.card ((v.adicCompletionIntegers K) ⧸
      Ideal.span {(n : v.adicCompletionIntegers K)}))]

/-- Finite iteration of the coprime-modulus formula on a supported modulus. -/
theorem powerCongruenceIndex_supportModulus (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n t : ℕ) (hn : 0 < n) :
    powerCongruenceIndex K n (supportModulus K S t) =
      ∏ v ∈ S, powerCongruenceIndex K n (v.asIdeal ^ t) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [supportModulus, Finset.prod_empty, Ideal.one_eq_top, powerCongruenceIndex,
      rayElements_top, sup_top_eq, Subgroup.index_top]
  | insert v S hv ih =>
    rw [Finset.prod_insert hv, ← ih]
    have h1 : supportModulus K (insert v S) t = v.asIdeal ^ t * supportModulus K S t := by
      rw [supportModulus, Finset.prod_insert hv]
      rfl
    have hv0 : v.asIdeal ^ t ≠ ⊥ := by
      simpa only [Ideal.zero_eq_bot] using pow_ne_zero t
        (show v.asIdeal ≠ 0 by simpa only [Ideal.zero_eq_bot] using v.ne_bot)
    rw [h1]
    exact powerCongruenceIndex_mul K n hn _ _ hv0 (supportModulus_ne_bot K S t)
      (prime_power_coprime_supportModulus K S v hv t t)

/-- A finite maximum of local cutoffs yields the supported-modulus formula. -/
theorem powerCongruenceIndex_support_eventually (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, powerCongruenceIndex K n (supportModulus K S t) =
      n ^ (2 * S.card) * ∏ v ∈ S,
        Nat.card ((v.adicCompletionIntegers K) ⧸ Ideal.span {(n : v.adicCompletionIntegers K)}) :=
  by
    classical
    choose c hc using fun v : HeightOneSpectrum (𝓞 K) =>
      powerCongruenceIndex_primePower K v n hn ζ hζ
    refine ⟨S.sup c, fun t ht => ?_⟩
    rw [powerCongruenceIndex_supportModulus K S n t hn,
      Finset.prod_congr rfl fun v hv => hc v t (le_trans (Finset.le_sup hv) ht),
      Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul]

/-- Janusz V.9, p.179: the key product equals n to twice the total number of S-places.
The totally complex restriction accounts explicitly for the infinite-place contribution. -/
theorem powerCongruenceIndex_pair_product [IsTotallyComplex K]
    (S₁ S₂ : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S₁ S₂)
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (hS : CoversNthPrimes K n (S₁.disjUnion S₂ hdisj)) :
    ∃ t₀ : ℕ, ∀ t₁ ≥ t₀, ∀ t₂ ≥ t₀,
      powerCongruenceIndex K n (supportModulus K S₁ t₁) *
        powerCongruenceIndex K n (supportModulus K S₂ t₂) =
          n ^ (2 * ((S₁.disjUnion S₂ hdisj).card + nrComplexPlaces K)) := by
  obtain ⟨c₁, hc₁⟩ := powerCongruenceIndex_support_eventually K S₁ n hn ζ hζ
  obtain ⟨c₂, hc₂⟩ := powerCongruenceIndex_support_eventually K S₂ n hn ζ hζ
  refine ⟨max c₁ c₂, fun t₁ ht₁ t₂ ht₂ => ?_⟩
  rw [hc₁ t₁ (le_trans (le_max_left _ _) ht₁), hc₂ t₂ (le_trans (le_max_right _ _) ht₂)]
  have hprod := product_local_integer_quotient K (S₁.disjUnion S₂ hdisj) n hn hS
  rw [Finset.prod_disjUnion, IsTotallyComplex.finrank] at hprod
  rw [Finset.card_disjUnion]
  calc n ^ (2 * S₁.card) * (∏ v ∈ S₁, Nat.card ((v.adicCompletionIntegers K) ⧸
          Ideal.span {(n : v.adicCompletionIntegers K)})) *
        (n ^ (2 * S₂.card) * ∏ v ∈ S₂, Nat.card ((v.adicCompletionIntegers K) ⧸
          Ideal.span {(n : v.adicCompletionIntegers K)}))
      = n ^ (2 * S₁.card) * n ^ (2 * S₂.card) *
          ((∏ v ∈ S₁, Nat.card ((v.adicCompletionIntegers K) ⧸
            Ideal.span {(n : v.adicCompletionIntegers K)})) *
          ∏ v ∈ S₂, Nat.card ((v.adicCompletionIntegers K) ⧸
            Ideal.span {(n : v.adicCompletionIntegers K)})) := by ring
    _ = n ^ (2 * (S₁.card + S₂.card + nrComplexPlaces K)) := by
      rw [hprod, ← pow_add, ← pow_add]
      ring_nf

end Cox.ClassFieldTheory
