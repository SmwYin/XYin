/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldUnitLogIndependence
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Torsion

/-! # The orbit products in Janusz V.2.3

The product is over the actual restriction fiber of infinite places. Fixedness
allows descent to base integer units; Dirichlet dependence and torsion clearing
supply a nonzero integral relation. Nonvanishing of every coefficient, subsequent
normalization, finite index and the Herbrand calculation are separate steps.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise
noncomputable section
namespace Cox.ClassFieldTheory

/-- An integer unit whose field-unit value descends to K descends as an integer unit. -/
theorem integerUnit_descends (K L : Type*) [Field K] [Field L] [Algebra K L]
    (a : Kˣ) (u : (𝓞 L)ˣ)
    (h : Units.map (algebraMap K L).toMonoidHom a =
      Units.map (algebraMap (𝓞 L) L).toMonoidHom u) :
    ∃ b : (𝓞 K)ˣ, Units.map (algebraMap (𝓞 K) K).toMonoidHom b = a := by
  have hval : algebraMap K L (a : K) = ((u : 𝓞 L) : L) := congrArg Units.val h
  have h' : Units.map (algebraMap K L).toMonoidHom a⁻¹ =
      Units.map (algebraMap (𝓞 L) L).toMonoidHom u⁻¹ := by
    rw [map_inv, map_inv, h]
  have hvalinv : algebraMap K L ((a⁻¹ : Kˣ) : K) = (((u⁻¹ : (𝓞 L)ˣ) : 𝓞 L) : L) :=
    congrArg Units.val h'
  have hint : IsIntegral ℤ (a : K) :=
    (isIntegral_algHom_iff (algebraMap K L).toIntAlgHom (algebraMap K L).injective).mp
      (by rw [show (algebraMap K L).toIntAlgHom (a : K) = algebraMap K L a from rfl, hval]
          exact (u : 𝓞 L).2)
  have hint' : IsIntegral ℤ ((a⁻¹ : Kˣ) : K) :=
    (isIntegral_algHom_iff (algebraMap K L).toIntAlgHom (algebraMap K L).injective).mp
      (by rw [show (algebraMap K L).toIntAlgHom ((a⁻¹ : Kˣ) : K) =
            algebraMap K L ((a⁻¹ : Kˣ) : K) from rfl, hvalinv]
          exact ((u⁻¹ : (𝓞 L)ˣ) : 𝓞 L).2)
  refine ⟨⟨⟨a, hint⟩, ⟨(a⁻¹ : Kˣ), hint'⟩, ?_, ?_⟩, ?_⟩
  · exact RingOfIntegers.ext (Units.mul_inv a)
  · exact RingOfIntegers.ext (Units.inv_mul a)
  · exact Units.ext rfl

/-- A Galois-fixed principal-kernel unit has an actual base integer-unit representative. -/
theorem fixedPrincipalUnit_descends (K L : Type*) [Field K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (a : (toPrincipalIdeal (𝓞 L) L).ker)
    (ha : ∀ σ : L ≃ₐ[K] L, σ • (a : Lˣ) = (a : Lˣ)) :
    ∃ b : (𝓞 K)ˣ,
      Units.map ((algebraMap K L).comp (algebraMap (𝓞 K) K)).toMonoidHom b = (a : Lˣ) := by
  obtain ⟨e, he⟩ := (principalIdeal_eq_one_iff L _).mp (MonoidHom.mem_ker.mp a.2)
  have hfix : ∀ σ : L ≃ₐ[K] L, σ ((a : Lˣ) : L) = ((a : Lˣ) : L) := fun σ =>
    congrArg Units.val (ha σ)
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) ((a : Lˣ) : L)).mpr hfix
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (a : Lˣ).ne_zero (by rw [← hc, map_zero])
  obtain ⟨b, hb⟩ := integerUnit_descends K L (Units.mk0 c hc0) e
    (by rw [he]; exact Units.ext hc)
  refine ⟨b, Units.ext ?_⟩
  have h1 := congrArg Units.val hb
  change algebraMap (𝓞 K) K (b : 𝓞 K) = c at h1
  change algebraMap K L (algebraMap (𝓞 K) K (b : 𝓞 K)) = ((a : Lˣ) : L)
  rw [h1, hc]

open scoped Classical in
/-- Product of the actual global-unit family over the exact restriction fiber. -/
def orbitUnitProduct (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker) (v : InfinitePlace K) :
    (toPrincipalIdeal (𝓞 L) L).ker :=
  ∏ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}, u w.val

/-- Equivariance makes the exact orbit product fixed by every field automorphism. -/
theorem orbitUnitProduct_fixed (K L : Type*) [Field K] [Field L] [NumberField L]
    [Algebra K L] (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hu : ∀ (σ : L ≃ₐ[K] L) w, σ • (u w : Lˣ) = (u (σ • w) : Lˣ))
    (v : InfinitePlace K) (σ : L ≃ₐ[K] L) :
    σ • (orbitUnitProduct K L u v : Lˣ) = (orbitUnitProduct K L u v : Lˣ) := by
  classical
  have hfib : ∀ w : InfinitePlace L,
      (σ • w).comap (algebraMap K L) = w.comap (algebraMap K L) := fun w => by
    rw [InfinitePlace.comap_smul]
    congr 1
    ext x
    exact σ.symm.commutes x
  let e : {w : InfinitePlace L // w.comap (algebraMap K L) = v} ≃
      {w : InfinitePlace L // w.comap (algebraMap K L) = v} :=
    Equiv.subtypeEquiv (MulAction.toPerm σ) fun w => by
      rw [MulAction.toPerm_apply, hfib]
  have hcoe : ((orbitUnitProduct K L u v : (toPrincipalIdeal (𝓞 L) L).ker) : Lˣ) =
      ∏ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}, (u w.val : Lˣ) := by
    rw [orbitUnitProduct]
    exact map_prod (toPrincipalIdeal (𝓞 L) L).ker.subtype _ _
  rw [hcoe, Finset.smul_prod']
  simp_rw [hu]
  exact Fintype.prod_equiv e _ _ fun w => rfl

/-- Each orbit product descends with an explicit base integer-unit representative. -/
theorem orbitUnitProducts_descend (K L : Type*) [Field K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hu : ∀ (σ : L ≃ₐ[K] L) w, σ • (u w : Lˣ) = (u (σ • w) : Lˣ)) :
    ∃ b : InfinitePlace K → (𝓞 K)ˣ, ∀ v,
      Units.map ((algebraMap K L).comp (algebraMap (𝓞 K) K)).toMonoidHom (b v) =
        (orbitUnitProduct K L u v : Lˣ) := by
  choose b hb using fun v => fixedPrincipalUnit_descends K L (orbitUnitProduct K L u v)
    (fun σ => orbitUnitProduct_fixed K L u hu v σ)
  exact ⟨b, hb⟩

/-- A family indexed by all infinite places exceeds the Dirichlet unit rank modulo torsion.
The letI chooses the canonical additive-monoid projection; it is not a hypothesis. -/
theorem unitFamily_modTorsion_dependent (K : Type*) [Field K] [NumberField K]
    (u : InfinitePlace K → (𝓞 K)ˣ) :
    letI : AddCommMonoid (Additive ((𝓞 K)ˣ ⧸ Units.torsion K)) :=
      (inferInstance : AddCommGroup (Additive ((𝓞 K)ˣ ⧸ Units.torsion K))).toAddCommMonoid
    ¬ LinearIndependent ℤ (fun v : InfinitePlace K ↦
      Additive.ofMul (QuotientGroup.mk (u v) : (𝓞 K)ˣ ⧸ Units.torsion K)) := by
  intro hli
  have h1 := hli.fintype_card_le_finrank
  rw [NumberField.Units.rank_modTorsion, NumberField.Units.rank] at h1
  have h2 := Fintype.card_pos (α := InfinitePlace K)
  omega

/-- Dirichlet dependence produces an integral nonzero vector whose product is torsion. -/
theorem unitFamily_relation_mod_torsion (K : Type*) [Field K] [NumberField K]
    (u : InfinitePlace K → (𝓞 K)ˣ) :
    ∃ a : InfinitePlace K → ℤ, a ≠ 0 ∧ (∏ v, u v ^ a v) ∈ Units.torsion K := by
  have h : ¬ LinearIndependent ℤ (fun v : InfinitePlace K ↦
      Additive.ofMul (QuotientGroup.mk (u v) : (𝓞 K)ˣ ⧸ Units.torsion K)) :=
    unitFamily_modTorsion_dependent K u
  rw [Fintype.not_linearIndependent_iff] at h
  obtain ⟨g, hg, i, hi⟩ := h
  refine ⟨g, fun h0 => hi (by rw [h0]; rfl), ?_⟩
  have key : Additive.ofMul ((QuotientGroup.mk' (Units.torsion K)) (∏ v, u v ^ g v)) =
      ∑ v, g v • Additive.ofMul (QuotientGroup.mk (u v) : (𝓞 K)ˣ ⧸ Units.torsion K) := by
    rw [map_prod, ofMul_prod]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_zpow, ofMul_zpow]
    rfl
  rw [hg] at key
  have h1 : (QuotientGroup.mk' (Units.torsion K)) (∏ v, u v ^ g v) = 1 :=
    Additive.ofMul.injective (key.trans rfl)
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

/-- A positive finite order clears torsion without making the integral vector zero. -/
theorem clear_torsion_relation {ι G : Type*} [Fintype ι] [CommGroup G]
    (u : ι → G) (a : ι → ℤ) (ha : a ≠ 0)
    (ht : IsOfFinOrder (∏ i, u i ^ a i)) :
    ∃ b : ι → ℤ, b ≠ 0 ∧ (∏ i, u i ^ b i) = 1 := by
  obtain ⟨n, hn, hpow⟩ := ht.exists_pow_eq_one
  refine ⟨fun i => a i * n, ?_, ?_⟩
  · intro h0
    apply ha
    funext i
    have h1 := congrFun h0 i
    simp only [Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact h1
    · omega
  · rw [← hpow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_mul, zpow_natCast]

/-- The base unit family has an exact nonzero integral multiplicative relation. -/
theorem unitFamily_nonzero_relation (K : Type*) [Field K] [NumberField K]
    (u : InfinitePlace K → (𝓞 K)ˣ) :
    ∃ a : InfinitePlace K → ℤ, a ≠ 0 ∧ (∏ v, u v ^ a v) = 1 := by
  obtain ⟨a, ha, ht⟩ := unitFamily_relation_mod_torsion K u
  exact clear_torsion_relation u a ha ((CommGroup.mem_torsion _).mp ht)

/-- Janusz V.2.3: the actual orbit products satisfy an exact nonzero integral relation.
No assertion that every coefficient is nonzero is included at this stage. -/
theorem orbitUnitProducts_nonzero_relation (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (u : InfinitePlace L → (toPrincipalIdeal (𝓞 L) L).ker)
    (hu : ∀ (σ : L ≃ₐ[K] L) w, σ • (u w : Lˣ) = (u (σ • w) : Lˣ)) :
    ∃ a : InfinitePlace K → ℤ, a ≠ 0 ∧ (∏ v, orbitUnitProduct K L u v ^ a v) = 1 := by
  obtain ⟨b, hb⟩ := orbitUnitProducts_descend K L u hu
  obtain ⟨a, ha, hrel⟩ := unitFamily_nonzero_relation K b
  refine ⟨a, ha, ?_⟩
  have h := congrArg (Units.map ((algebraMap K L).comp (algebraMap (𝓞 K) K)).toMonoidHom) hrel
  rw [map_prod, map_one] at h
  simp only [map_zpow, hb] at h
  apply Subtype.ext
  change (toPrincipalIdeal (𝓞 L) L).ker.subtype (∏ v, orbitUnitProduct K L u v ^ a v) = 1
  rw [map_prod]
  simpa only [map_zpow] using h

end Cox.ClassFieldTheory
