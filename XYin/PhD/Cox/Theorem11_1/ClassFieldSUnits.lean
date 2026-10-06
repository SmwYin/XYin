/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldArithmetic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-! # Janusz V.8.2–8.3 on S-units

The supported ideals form a free abelian group on the primes of `S`, the principal
ones have full rank, and the S-unit exact sequence splits. Combined with Dirichlet's
unit theorem this computes the index of nth powers in the S-units.
-/

open NumberField IsDedekindDomain NumberField.InfinitePlace
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Additive prime exponents on the group of nonzero fractional ideals. -/
def idealCountHom (v : HeightOneSpectrum (𝓞 K)) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* Multiplicative ℤ :=
  MonoidHom.mk' (fun I ↦ Multiplicative.ofAdd (FractionalIdeal.count K v I))
    (fun I J ↦ FractionalIdeal.count_mul K v I.ne_zero J.ne_zero)

/-- The S-prime coordinates of a supported fractional ideal. -/
def supportedIdealExponentMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    supportedIdeals K S →* Multiplicative (S → ℤ) :=
  MonoidHom.mk' (fun I ↦ Multiplicative.ofAdd
    (fun v ↦ FractionalIdeal.count K v.val (I.val : FractionalIdeal (𝓞 K)⁰ K)))
    (fun I J ↦ congrArg Multiplicative.ofAdd
      (funext fun v ↦ FractionalIdeal.count_mul K v.val I.val.ne_zero J.val.ne_zero))

/-- The principal-ideal arrow i in Janusz V.8.2, p.173. -/
def sUnitIdealMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnits K S →* supportedIdeals K S :=
  ((toPrincipalIdeal (𝓞 K) K).comp (sUnits K S).subtype).codRestrict
    (supportedIdeals K S) (fun x ↦ x.property)

/-- The prime-exponent homomorphism has the advertised value. -/
theorem idealCountHom_apply (v : HeightOneSpectrum (𝓞 K))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (idealCountHom K v I).toAdd = FractionalIdeal.count K v I := by
  rfl

/-- Supported exponent coordinates are the corresponding prime counts. -/
theorem supportedIdealExponentMap_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : supportedIdeals K S) (v : S) :
    (supportedIdealExponentMap K S I).toAdd v =
      FractionalIdeal.count K v.val (I.val : FractionalIdeal (𝓞 K)⁰ K) := by
  rfl

/-- Forgetting the supported-ideal subtype recovers the principal ideal. -/
theorem sUnitIdealMap_coe (S : Finset (HeightOneSpectrum (𝓞 K))) (x : sUnits K S) :
    (sUnitIdealMap K S x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toPrincipalIdeal (𝓞 K) K (x : Kˣ) := by
  rfl

/-- Prime exponents vanish outside the support; Janusz V.8.2's I(S₀). -/
theorem count_eq_zero_of_mem_supportedIdeals (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : supportedIdeals K S) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    FractionalIdeal.count K v (I.val : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  have hle : supportedIdeals K S ≤ (idealCountHom K v).ker := by
    refine (Subgroup.closure_le _).mpr fun u ⟨w, hw, hu⟩ => ?_
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    rw [idealCountHom_apply, hu, FractionalIdeal.count_maximal_coprime K v
      (fun h => hv (h ▸ hw))]
    rfl
  have h := congrArg Multiplicative.toAdd ((MonoidHom.mem_ker).mp (hle I.property))
  rw [idealCountHom_apply] at h
  exact h

/-- Unique factorization makes the supported coordinates injective. -/
theorem supportedIdealExponentMap_injective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (supportedIdealExponentMap K S) := by
  refine (injective_iff_map_eq_one _).mpr fun I hI => ?_
  have hcount : ∀ v, FractionalIdeal.count K v (I.val : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    intro v
    by_cases hv : v ∈ S
    · have h := congrFun (congrArg Multiplicative.toAdd hI) ⟨v, hv⟩
      rw [supportedIdealExponentMap_apply] at h
      exact h
    · exact count_eq_zero_of_mem_supportedIdeals K S I v hv
  have h := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
    (I := (I.val : FractionalIdeal (𝓞 K)⁰ K)) I.val.ne_zero
  simp only [hcount, zpow_zero, finprod_one] at h
  exact Subtype.ext (Units.ext h.symm)

/-- Every integer prime-exponent vector is realized by its finite ideal product. -/
theorem supportedIdealExponentMap_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (supportedIdealExponentMap K S) := by
  classical
  let P : S → supportedIdeals K S := fun v =>
    ⟨primeIdealUnit K v.val,
      Subgroup.subset_closure ⟨v.val, v.property, primeIdealUnit_coe K v.val⟩⟩
  have hP : ∀ w : S, supportedIdealExponentMap K S (P w) =
      Multiplicative.ofAdd (Pi.single w 1) := by
    intro w
    apply Multiplicative.toAdd.injective
    funext v
    rw [toAdd_ofAdd, supportedIdealExponentMap_apply]
    change FractionalIdeal.count K v.val
      ((primeIdealUnit K w.val : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = _
    rw [primeIdealUnit_coe]
    by_cases h : v = w
    · subst h
      rw [Pi.single_eq_same, FractionalIdeal.count_maximal, if_pos rfl]
    · rw [Pi.single_eq_of_ne h, FractionalIdeal.count_maximal_coprime K v.val
        (fun h' => h (Subtype.ext h'.symm))]
  intro f
  refine ⟨∏ w : S, P w ^ (Multiplicative.toAdd f w), ?_⟩
  rw [map_prod]
  simp_rw [map_zpow, hP]
  apply Multiplicative.toAdd.injective
  funext v
  simp [Finset.sum_apply, Pi.single_apply]

/-- Janusz V.8.2: I(S₀) is free abelian of rank |S₀|. -/
theorem supportedIdeals_equiv_exponents (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Nonempty (supportedIdeals K S ≃* Multiplicative (S → ℤ)) := by
  exact ⟨MulEquiv.ofBijective _ ⟨supportedIdealExponentMap_injective K S,
    supportedIdealExponentMap_surjective K S⟩⟩

/-- Janusz V.8.2's exact sequence starts with the ordinary units. -/
theorem sUnitIdealMap_ker_equiv_units (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Nonempty ((sUnitIdealMap K S).ker ≃* (𝓞 K)ˣ) := by
  let ι : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K)
  have hι : ∀ u : (𝓞 K)ˣ, toPrincipalIdeal (𝓞 K) K (ι u) = 1 := by
    intro u
    rw [toPrincipalIdeal_eq_iff, Units.val_one]
    change FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K u) = 1
    rw [← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr u.isUnit,
      FractionalIdeal.coeIdeal_top]
  have hmem : ∀ u : (𝓞 K)ˣ, ι u ∈ sUnits K S := by
    intro u
    change toPrincipalIdeal (𝓞 K) K (ι u) ∈ supportedIdeals K S
    rw [hι]
    exact one_mem _
  let f₀ : (𝓞 K)ˣ →* sUnits K S := ι.codRestrict (sUnits K S) hmem
  have hker : ∀ u, f₀ u ∈ (sUnitIdealMap K S).ker := by
    intro u
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [sUnitIdealMap_coe]
    exact hι u
  let f : (𝓞 K)ˣ →* (sUnitIdealMap K S).ker := f₀.codRestrict _ hker
  have hinj : Function.Injective f := by
    intro u w h
    exact NumberField.Units.coe_injective K
      (congrArg (fun x : (sUnitIdealMap K S).ker => (((x : sUnits K S) : Kˣ) : K)) h)
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨x, hx⟩, hxk⟩
    rw [MonoidHom.mem_ker] at hxk
    have h1 : toPrincipalIdeal (𝓞 K) K x = 1 := by
      have h := congrArg Subtype.val hxk
      rwa [sUnitIdealMap_coe] at h
    rw [toPrincipalIdeal_eq_iff, Units.val_one, ← FractionalIdeal.spanSingleton_one,
      FractionalIdeal.spanSingleton_eq_spanSingleton] at h1
    obtain ⟨z, hz⟩ := h1
    have hz' : algebraMap (𝓞 K) K (z : 𝓞 K) * (x : K) = 1 := by
      rw [← hz, Units.smul_def, Algebra.smul_def]
    refine ⟨z⁻¹, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change algebraMap (𝓞 K) K ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = (x : K)
    rw [map_units_inv (algebraMap (𝓞 K) K) z]
    exact inv_eq_of_mul_eq_one_right hz'
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩

/-- Janusz V.8.2: I(S₀)^h is contained in i(Kˢ), for h the class number. -/
theorem sUnitIdealMap_pow_card_mem_range (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : supportedIdeals K S) :
    I ^ Nat.card (ClassGroup (𝓞 K)) ∈ (sUnitIdealMap K S).range := by
  have h1 : ClassGroup.mk K (((I ^ Nat.card (ClassGroup (𝓞 K)) : supportedIdeals K S) :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ)) = 1 := by
    rw [Subgroup.coe_pow, map_pow, pow_card_eq_one']
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).mp h1
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hx
    exact Units.ne_zero _ hx
  have hxI : toPrincipalIdeal (𝓞 K) K (Units.mk0 x hx0) =
      ((I ^ Nat.card (ClassGroup (𝓞 K)) : supportedIdeals K S) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
    rw [toPrincipalIdeal_eq_iff, Units.val_mk0, hx]
  refine ⟨⟨Units.mk0 x hx0, ?_⟩, ?_⟩
  · change toPrincipalIdeal (𝓞 K) K (Units.mk0 x hx0) ∈ supportedIdeals K S
    rw [hxI]
    exact (I ^ Nat.card (ClassGroup (𝓞 K))).property
  · apply Subtype.ext
    rw [sUnitIdealMap_coe]
    exact hxI

/-- A subgroup containing a nonzero multiple of every vector has full rank. -/
theorem finrank_submodule_eq_of_nsmul_mem {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] (N : Submodule ℤ M)
    (n : ℕ) (hn : 0 < n) (hN : ∀ x : M, n • x ∈ N) :
    Module.finrank ℤ N = Module.finrank ℤ M := by
  obtain rfl : ‹Module ℤ M› = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  let g : M →ₗ[ℤ] N := LinearMap.codRestrict N (DistribSMul.toLinearMap ℤ M n) hN
  have hg : Function.Injective g := by
    intro x y hxy
    exact AddSubgroup.distribSMulToLinearMap_injective_of_isTorsionFree hn.ne'
      (congrArg Subtype.val hxy)
  exact le_antisymm (Submodule.finrank_le N) (LinearMap.finrank_le_finrank_of_injective hg)

/-- The intermediate group in I(S₀)^h ⊆ i(Kˢ) ⊆ I(S₀) has the same free rank. -/
theorem subgroup_equiv_of_pow_mem {G : Type*} [CommGroup G]
    [Module.Free ℤ (Additive G)] [Module.Finite ℤ (Additive G)]
    (H : Subgroup G) (n : ℕ) (hn : 0 < n) (hH : ∀ x : G, x ^ n ∈ H) :
    Nonempty (H ≃* G) := by
  let N : Submodule ℤ (Additive G) := H.toAddSubgroup.toIntSubmodule
  have hN : ∀ x : Additive G, n • x ∈ N := fun x => hH (Additive.toMul x)
  have hrank := finrank_submodule_eq_of_nsmul_mem N n hn hN
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank
  exact ⟨{ toFun := fun h => Additive.toMul (e ⟨Additive.ofMul (h : G), h.2⟩)
           invFun := fun g => ⟨Additive.toMul (e.symm (Additive.ofMul g) : Additive G),
             (e.symm (Additive.ofMul g)).2⟩
           left_inv := fun h => Subtype.ext (by simp)
           right_inv := fun g => by simp
           map_mul' := fun h₁ h₂ => by
             rw [← toMul_add, ← map_add]
             rfl }⟩

/-- Source projectivity step: an onto map to a free abelian group has a section. -/
theorem exists_monoidHom_rightInverse_of_free {G H : Type*} [CommGroup G] [CommGroup H]
    [Module.Free ℤ (Additive H)] (f : G →* H) (hf : Function.Surjective f) :
    ∃ s : H →* G, Function.RightInverse s f := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property (MonoidHom.toAdditive f).toIntLinearMap
    (LinearMap.id : Additive H →ₗ[ℤ] Additive H) hf
  refine ⟨MonoidHom.toAdditive.symm h.toAddMonoidHom, fun y => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun hh (Additive.ofMul y))

/-- A section splits a commutative-group map into its kernel and codomain. -/
theorem equiv_ker_prod_of_rightInverse {G H : Type*} [CommGroup G] [CommGroup H]
    (f : G →* H) (s : H →* G) (hs : Function.RightInverse s f) :
    Nonempty (G ≃* (f.ker × H)) := by
  refine ⟨{
    toFun := fun g => (⟨g * (s (f g))⁻¹, by rw [MonoidHom.mem_ker, map_mul, map_inv, hs (f g),
      mul_inv_cancel]⟩, f g)
    invFun := fun x => (x.1 : G) * s x.2
    left_inv := fun g => by simp
    right_inv := fun x => by
      have hx : f (x.1 : G) = 1 := x.1.property
      ext <;> simp [hx, hs x.2]
    map_mul' := fun g h => by
      ext <;> simp only [map_mul, Prod.mk_mul_mk, Subgroup.coe_mul, mul_inv]
      · rw [mul_mul_mul_comm]
  }⟩

/-- A commutative group isomorphic to a standard lattice is free and finite over `ℤ`. -/
theorem free_finite_of_mulEquiv {G ι : Type*} [CommGroup G] [Finite ι]
    (e : G ≃* Multiplicative (ι → ℤ)) :
    Module.Free ℤ (Additive G) ∧ Module.Finite ℤ (Additive G) := by
  let e' : Additive G ≃ₗ[ℤ] (ι → ℤ) := (MulEquiv.toAdditiveLeft e).toIntLinearEquiv
  exact ⟨Module.Free.of_equiv e'.symm, Module.Finite.equiv e'.symm⟩

/-- Janusz V.8.2: the principal supported ideals have the full supported-ideal rank. -/
theorem sUnitIdealMap_range_equiv_exponents (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Nonempty ((sUnitIdealMap K S).range ≃* Multiplicative (S → ℤ)) := by
  obtain ⟨e⟩ := supportedIdeals_equiv_exponents K S
  obtain ⟨hfree, hfin⟩ := free_finite_of_mulEquiv e
  obtain ⟨r⟩ := subgroup_equiv_of_pow_mem (sUnitIdealMap K S).range
    (Nat.card (ClassGroup (𝓞 K))) Nat.card_pos (sUnitIdealMap_pow_card_mem_range K S)
  exact ⟨r.trans e⟩

/-- Dirichlet's theorem gives the product used at the end of Janusz V.8.2. -/
theorem units_equiv_torsion_prod_free :
    Nonempty ((𝓞 K)ˣ ≃* (NumberField.Units.torsion K ×
      Multiplicative (Fin (NumberField.Units.rank K) → ℤ))) := by
  let φ : (NumberField.Units.torsion K ×
      Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) →* (𝓞 K)ˣ :=
    { toFun := fun x => (x.1 : (𝓞 K)ˣ) *
        ∏ i, (NumberField.Units.fundSystem K i) ^ (Multiplicative.toAdd x.2 i)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, toAdd_mul, Pi.add_apply,
          zpow_add, Finset.prod_mul_distrib]
        exact mul_mul_mul_comm _ _ _ _ }
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h := (NumberField.Units.exist_unique_eq_mul_prod (K := K) (φ x)).unique
        (y₁ := (x.1, Multiplicative.toAdd x.2)) (y₂ := (y.1, Multiplicative.toAdd y.2)) rfl hxy
      exact Prod.ext (congrArg Prod.fst h) (Multiplicative.toAdd.injective (congrArg Prod.snd h))
    · intro u
      obtain ⟨⟨ζ, e⟩, h, -⟩ := NumberField.Units.exist_unique_eq_mul_prod (K := K) u
      exact ⟨(ζ, Multiplicative.ofAdd e), h.symm⟩
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- A primitive nth root in K is a torsion unit of the integer ring. -/
theorem exists_torsion_primitiveRoot (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) :
    ∃ u : NumberField.Units.torsion K, IsPrimitiveRoot u n := by
  have hint : IsIntegral ℤ ζ := hζ.isIntegral hn
  let z : 𝓞 K := ⟨ζ, hint⟩
  have hz : z ^ n = 1 := by
    apply RingOfIntegers.coe_injective
    simpa [z] using hζ.pow_eq_one
  let u : (𝓞 K)ˣ := Units.ofPowEqOne z n hz hn.ne'
  have hu : u ∈ NumberField.Units.torsion K :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Units.pow_ofPowEqOne hz hn.ne'⟩
  refine ⟨⟨u, hu⟩, ?_⟩
  let g : NumberField.Units.torsion K →* K :=
    ((Units.coeHom K).comp (Units.map (algebraMap (𝓞 K) K))).comp
      (NumberField.Units.torsion K).subtype
  have hg : Function.Injective g := fun a b h => Subtype.ext (NumberField.Units.coe_injective K h)
  have hgu : g ⟨u, hu⟩ = ζ := by
    simp [g, u, z]
  rw [← hgu] at hζ
  exact (IsPrimitiveRoot.map_iff_of_injective hg).mp hζ

/-- The finite torsion factor contributes n to the power index in V.8.3. -/
theorem torsion_power_index (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    (powMonoidHom n : NumberField.Units.torsion K →*
      NumberField.Units.torsion K).range.index = n := by
  obtain ⟨u, hu⟩ := exists_torsion_primitiveRoot K n hn ζ hζ
  have hdvd : n ∣ Nat.card (NumberField.Units.torsion K) := by
    rw [hu.eq_orderOf]
    exact orderOf_dvd_natCard u
  rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right hdvd]

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
/-- The free abelian factor contributes n to the index in each coordinate. -/
theorem freeAbelian_power_index {ι : Type*} [Fintype ι] (n : ℕ) (hn : 0 < n) :
    (powMonoidHom n : Multiplicative (ι → ℤ) →*
      Multiplicative (ι → ℤ)).range.index = n ^ Fintype.card ι := by
  have h : (powMonoidHom n : Multiplicative (ι → ℤ) →* Multiplicative (ι → ℤ)).range =
      AddSubgroup.toSubgroup (nsmulAddMonoidHom (α := ι → ℤ) n).range := by
    ext x
    rw [MonoidHom.mem_range, Multiplicative.mem_toSubgroup, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Multiplicative.toAdd y, by simp⟩
    · rintro ⟨y, hy⟩
      refine ⟨Multiplicative.ofAdd y, ?_⟩
      apply Multiplicative.toAdd.injective
      simpa using hy
  rw [h, AddSubgroup.index_toSubgroup, AddSubgroup.index_range_nsmul,
    Module.finrank_fintype_fun_eq_card]

/-- Power indices transport through group equivalences. -/
theorem power_index_eq_of_mulEquiv {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.index =
      (powMonoidHom n : H →* H).range.index := by
  rw [← Subgroup.index_map_equiv (powMonoidHom n : G →* G).range e]
  congr 1
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨e z, by simp⟩
  · rintro ⟨w, rfl⟩
    exact ⟨e.symm w ^ n, ⟨e.symm w, rfl⟩, by simp⟩

/-- Power indices multiply for a product of commutative groups. -/
theorem power_index_prod {G H : Type*} [CommGroup G] [CommGroup H] (n : ℕ) :
    (powMonoidHom n : G × H →* G × H).range.index =
      (powMonoidHom n : G →* G).range.index *
        (powMonoidHom n : H →* H).range.index := by
  rw [← Subgroup.index_prod]
  congr 1
  ext ⟨a, b⟩
  simp only [MonoidHom.mem_range, powMonoidHom_apply, Subgroup.mem_prod, Prod.exists,
    Prod.pow_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨x, y, rfl, rfl⟩
    exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  · rintro ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
    exact ⟨x, y, rfl, rfl⟩

/-- The number of infinite places is one more than the unit rank. -/
theorem unit_rank_add_one :
    NumberField.Units.rank K + 1 = nrRealPlaces K + nrComplexPlaces K := by
  rw [NumberField.Units.rank, ← NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  exact Nat.sub_add_cancel Fintype.card_pos

/-- Janusz V.8.2: split the S-unit exact sequence over its free ideal image. -/
theorem sUnits_equiv_units_prod_free (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Nonempty (sUnits K S ≃* ((𝓞 K)ˣ × Multiplicative (S → ℤ))) := by
  obtain ⟨eR⟩ := sUnitIdealMap_range_equiv_exponents K S
  obtain ⟨eK⟩ := sUnitIdealMap_ker_equiv_units K S
  obtain ⟨hfree, -⟩ := free_finite_of_mulEquiv eR
  obtain ⟨s, hs⟩ := exists_monoidHom_rightInverse_of_free (sUnitIdealMap K S).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨e⟩ := equiv_ker_prod_of_rightInverse _ s hs
  exact ⟨e.trans (MulEquiv.prodCongr
    ((MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict _)).trans eK) eR)⟩

/-- Janusz V.8.3: S includes every infinite place, so the exponent counts finite primes
plus real and complex infinite places, each once. -/
theorem sUnits_power_index (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    (powMonoidHom n : sUnits K S →* sUnits K S).range.index =
      n ^ (S.card + nrRealPlaces K + nrComplexPlaces K) := by
  obtain ⟨e₁⟩ := sUnits_equiv_units_prod_free K S
  obtain ⟨e₂⟩ := units_equiv_torsion_prod_free K
  rw [power_index_eq_of_mulEquiv e₁ n, power_index_prod, power_index_eq_of_mulEquiv e₂ n,
    power_index_prod, torsion_power_index K n hn ζ hζ, freeAbelian_power_index n hn,
    freeAbelian_power_index n hn, Fintype.card_fin, Fintype.card_coe, add_assoc,
    ← unit_rank_add_one K]
  ring

end Cox.ClassFieldTheory
