/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevCyclotomic
import XYin.PhD.Cox.Theorem11_1.ChebotarevFixedField
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Cyclotomic crossing for abelian density

Source: AINTLIB Abelian.lean, revision `953409d221e42e247e32db31def5444fe60f3f87`, lines207–841. The
source is proof material, not an imported dependency.
-/

noncomputable section
open Filter NumberField Topology Set UniqueFactorizationMonoid
namespace Cox.Chebotarev

/-- Source: Abelian.lean:271–283 and597–610, the compositum generation calculation. -/
theorem cyclotomic_adjoin_sup_range_eq_top
    (F K M : Type*) [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M]
    [Algebra.IsAlgebraic F M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M]
    (ζ : M) (hζ : IsPrimitiveRoot ζ m) :
    IntermediateField.adjoin F {ζ} ⊔ (IsScalarTower.toAlgHom F K M).fieldRange = ⊤ := by
  have hζalg : IsAlgebraic F ζ := Algebra.IsAlgebraic.isAlgebraic ζ
  have hsubalg : (IsScalarTower.toAlgHom F K M).range ⊔ Algebra.adjoin F {ζ}
      = (⊤ : Subalgebra F M) := by
    have htop : (Algebra.adjoin K {ζ} : Subalgebra K M) = ⊤ :=
      IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ
    rw [← Algebra.Subalgebra.restrictScalars_adjoin (R := F) (S := K) (s := {ζ}), htop,
      Subalgebra.restrictScalars_top]
  apply IntermediateField.toSubalgebra_injective
  rw [IntermediateField.sup_toSubalgebra_of_isAlgebraic_left,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg,
    AlgHom.fieldRange_toSubalgebra, IntermediateField.top_toSubalgebra, sup_comm]
  exact hsubalg

/-- Source: Abelian.lean:336–344, recovering a fixed primitive root from character1. -/
theorem fixes_of_autToPow_eq_one
    (K M : Type*) [Field K] [Field M] [Algebra K M] (m : ℕ) [NeZero m]
    (ζ : M) (hζ : IsPrimitiveRoot ζ m) (g : Gal(M/K))
    (hg : hζ.autToPow K g = 1) : g ζ = ζ := by
  have hspec := hζ.autToPow_spec K g
  rw [hg] at hspec
  rw [← hspec, Units.val_one]
  rcases eq_or_lt_of_le (NeZero.one_le (n := m)) with h1 | h1
  · have hm1 : m = 1 := h1.symm
    subst hm1
    have : ζ = 1 := by simpa using hζ.pow_eq_one
    simp [this]
  · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega), pow_one]

/-- Source: Abelian.lean:350–360, an automorphism fixing generators fixes their algebra. -/
theorem algEquiv_eq_one_of_fixes_cyclotomic_generator
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    (ζ : M) (htop : Algebra.adjoin L {ζ} = ⊤) (g : Gal(M/K))
    (hL : ∀ x : L, g (algebraMap L M x) = algebraMap L M x) (hζ : g ζ = ζ) :
    g = 1 := by
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ Algebra.adjoin L {ζ} := htop ▸ Algebra.mem_top
  refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
  · intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; rw [hζ]; rfl
  · intro r; exact hL r
  · intro a b _ _ ha hb; rw [map_add, ha, hb]; rfl
  · intro a b _ _ ha hb; rw [map_mul, ha, hb]; rfl

/-- Source: Abelian.lean:419–425, a primitive root generates all m-th roots. -/
theorem adjoin_primitiveRoot_eq_adjoin_roots
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (m : ℕ) [NeZero m] (ζ : M) (hζ : IsPrimitiveRoot ζ m) :
    IntermediateField.adjoin K {ζ} = IntermediateField.adjoin K {b : M | b ^ m = 1} := by
  exact le_antisymm
    (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.subset_adjoin K _ hζ.pow_eq_one)))
    (IntermediateField.adjoin_le_iff.mpr fun x hx ↦ by
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one (Set.mem_setOf_eq ▸ hx)
      exact pow_mem (IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)) i)

/-- Source: Abelian.lean:426–427, fixed-field compositum via subgroup intersection. -/
theorem fixingSubgroup_fixedField_sup
    (K M : Type*) [Field K] [Field M] [Algebra K M] [FiniteDimensional K M]
    (H : Subgroup Gal(M/K)) (E : IntermediateField K M) :
    (IntermediateField.fixedField H ⊔ E).fixingSubgroup = H ⊓ E.fixingSubgroup := by
  rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField]

/-- Source: Abelian.lean:428–430, the trivial fixing subgroup has full fixed field. -/
theorem eq_top_of_fixingSubgroup_eq_bot
    (K M : Type*) [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (E : IntermediateField K M) (hE : E.fixingSubgroup = ⊥) : E = ⊤ := by
  have := congrArg IntermediateField.fixedField hE
  rwa [IsGalois.fixedField_fixingSubgroup, IntermediateField.fixedField_bot] at this

/-- Source: Abelian.lean:435–438, cyclotomic structure transported along full adjunction. -/
theorem isCyclotomic_of_primitiveRoot_adjoin_eq_top
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (m : ℕ) [NeZero m] (ζ : M) (hζ : IsPrimitiveRoot ζ m)
    (htop : IntermediateField.adjoin K {ζ} = ⊤) : IsCyclotomicExtension {m} K M := by
  haveI : FiniteDimensional K M := by
    have : FiniteDimensional K (IntermediateField.adjoin K {ζ}) :=
      IntermediateField.adjoin.finiteDimensional (hζ.isIntegral (NeZero.pos m)).tower_top
    rw [htop] at this
    exact (IntermediateField.topEquiv (F := K) (E := M)).toLinearEquiv.finiteDimensional
  haveI : Algebra.IsIntegral K M := Algebra.IsIntegral.of_finite K M
  haveI hcyc : IsCyclotomicExtension {m} K (IntermediateField.adjoin K {ζ}) :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := K) hζ
  rw [htop] at hcyc
  exact IsCyclotomicExtension.equiv (S := {m}) (A := K) (f := IntermediateField.topEquiv)

/-- Source: AINTLIB Abelian.lean:209, source-local crossing argument. -/
theorem pairwiseDisjoint_of_tag {α ι κ : Type*} (t : α → κ) (f : ι → κ)
    (hf : Function.Injective f) (S : ι → Set α) (htag : ∀ i, ∀ a ∈ S i, t a = f i) :
    (Set.univ : Set ι).PairwiseDisjoint S := by
  intro i _ j _ hij
  simp only [Function.onFun, Set.disjoint_left]
  intro a hi hj
  exact hij (hf ((htag i a hi).symm.trans (htag j a hj)))

/-- Source: AINTLIB Abelian.lean:232, source-local crossing argument. -/
theorem prime_dvd_natAbs_discr_cyclotomic_dvd
    (E : Type*) [Field E] [NumberField E] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} ℚ E]
    {p : ℕ} (hp : p.Prime) (hpd : p ∣ (NumberField.discr E).natAbs) : p ∣ m := by
  by_contra hpm
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  refine absurd (Int.ofNat_dvd_left.mpr hpd) ?_
  rw [NumberField.not_dvd_discr_iff_forall_liesOver E (𝓞 E) hpprime]
  intro P hPmax hlo
  haveI := hPmax.isPrime
  haveI := hlo
  have hspanbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hpprime.ne_zero
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspanbot P
  refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot).mpr ?_
  rw [← hlo.over]
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p E P hpm

/-- Source: Abelian.lean:287–296, a common discriminant prime contradicts admissibility. -/
theorem isCoprime_discr_of_cyclotomic
    (E K : Type*) [Field E] [NumberField E] [Field K] [NumberField K]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} ℚ E]
    (hcop : (NumberField.discr K).natAbs.Coprime m) :
    IsCoprime (NumberField.discr E) (NumberField.discr K) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  rw [Nat.dvd_gcd_iff] at hpdvd
  obtain ⟨hpa, hpb⟩ := hpdvd
  have hpm : p ∣ m := prime_dvd_natAbs_discr_cyclotomic_dvd E m hp hpa
  have hpgcd : p ∣ Nat.gcd (NumberField.discr K).natAbs m := Nat.dvd_gcd hpb hpm
  rw [hcop] at hpgcd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hpgcd)

/-- Source: Abelian.lean:297–300, the degree formula for disjoint number fields. -/
theorem finrank_coprime_discr_compositum
    (M : Type*) [Field M] [NumberField M] (E K : IntermediateField ℚ M)
    [IsGalois ℚ E] (hcop : IsCoprime (NumberField.discr E) (NumberField.discr K))
    (htop : E ⊔ K = ⊤) : Module.finrank K M = Module.finrank ℚ E := by
  have hld : E.LinearDisjoint K :=
    NumberField.linearDisjoint_of_isGalois_isCoprime_discr (L := M) E K hcop
  exact hld.finrank_right_eq_finrank htop

/-- Source: Abelian.lean:301–305, replacing a base field by its embedded range. -/
theorem finrank_fieldRange
    (F K M : Type*) [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] :
    Module.finrank K M = Module.finrank (IsScalarTower.toAlgHom F K M).fieldRange M := by
  let eK₂ : K ≃+* (IsScalarTower.toAlgHom F K M).fieldRange :=
    ((IsScalarTower.toAlgHom F K M : K →+* M)).rangeRestrictFieldEquiv
  refine Algebra.finrank_eq_of_equiv_equiv eK₂ (RingEquiv.refl M) ?_
  ext x
  change ((eK₂ x : M)) = (IsScalarTower.toAlgHom F K M : K →+* M) x
  rfl

/-- Source: AINTLIB Abelian.lean:257, source-local crossing argument. -/
theorem cyclotomicField_finrank_eq
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M]
    (hcop : ((NumberField.discr K).natAbs).Coprime m) :
    Module.finrank K M = m.totient := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) K M
    (Set.mem_singleton m) (NeZero.ne m)
  set K₁ : IntermediateField ℚ M := IntermediateField.adjoin ℚ {ζ} with hK₁def
  set K₂ : IntermediateField ℚ M := (IsScalarTower.toAlgHom ℚ K M).fieldRange with hK₂def
  haveI hK₁cyc : IsCyclotomicExtension {m} ℚ K₁ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ)
  haveI : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois (S := {m}) (K := ℚ) (L := K₁)
  have hfinK₁ : Module.finrank ℚ K₁ = m.totient :=
    IsCyclotomicExtension.finrank K₁ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  have hsup : K₁ ⊔ K₂ = ⊤ := by
    have hζalg : IsAlgebraic ℚ ζ := Algebra.IsAlgebraic.isAlgebraic ζ
    have hsubalg : (IsScalarTower.toAlgHom ℚ K M).range ⊔ Algebra.adjoin ℚ {ζ}
        = (⊤ : Subalgebra ℚ M) := by
      have htop : (Algebra.adjoin K {ζ} : Subalgebra K M) = ⊤ :=
        IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ
      rw [← Algebra.Subalgebra.restrictScalars_adjoin (R := ℚ) (S := K) (s := {ζ}), htop,
        Subalgebra.restrictScalars_top]
    apply IntermediateField.toSubalgebra_injective
    rw [hK₁def, hK₂def, IntermediateField.sup_toSubalgebra_of_isAlgebraic_left,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg,
      AlgHom.fieldRange_toSubalgebra, IntermediateField.top_toSubalgebra, sup_comm]
    exact hsubalg
  let eK₂ : K ≃+* K₂ := ((IsScalarTower.toAlgHom ℚ K M : K →+* M)).rangeRestrictFieldEquiv
  have hdiscrK₂ : NumberField.discr K₂ = NumberField.discr K :=
    (NumberField.discr_eq_discr_of_ringEquiv (f := eK₂)).symm
  have hcoprime : IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
    rw [hdiscrK₂, Int.isCoprime_iff_gcd_eq_one, Int.gcd]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    rw [Nat.dvd_gcd_iff] at hpdvd
    obtain ⟨hpa, hpb⟩ := hpdvd
    have hpm : p ∣ m := prime_dvd_natAbs_discr_cyclotomic_dvd K₁ m hp hpa
    have hpgcd : p ∣ Nat.gcd (NumberField.discr K).natAbs m := Nat.dvd_gcd hpb hpm
    rw [hcop] at hpgcd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpgcd)
  have hld : K₁.LinearDisjoint K₂ :=
    NumberField.linearDisjoint_of_isGalois_isCoprime_discr (L := M) K₁ K₂ hcoprime
  have hfr : Module.finrank K₂ M = Module.finrank ℚ K₁ :=
    hld.finrank_right_eq_finrank hsup
  have hrelabel : Module.finrank K M = Module.finrank K₂ M := by
    refine Algebra.finrank_eq_of_equiv_equiv eK₂ (RingEquiv.refl M) ?_
    ext x
    change ((eK₂ x : M)) = (IsScalarTower.toAlgHom ℚ K M : K →+* M) x
    rfl
  rw [hrelabel, hfr, hfinK₁]

/-- Source: Abelian.lean:326–329, cardinality of the compositum automorphism group. -/
theorem card_aut_cyclotomic_compositum
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (hcop : (NumberField.discr L).natAbs.Coprime m) :
    Nat.card Gal(M/K) = Nat.card Gal(L/K) * Nat.card (ZMod m)ˣ := by
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have hML : Module.finrank L M = m.totient := cyclotomicField_finrank_eq L M m hcop
  rw [IsGalois.card_aut_eq_finrank K M, IsGalois.card_aut_eq_finrank K L,
    ← Module.finrank_mul_finrank K L M, hML, Nat.card_eq_fintype_card (α := (ZMod m)ˣ),
    ZMod.card_units_eq_totient]

/-- Source: Abelian.lean:330–360, faithfulness of restriction and cyclotomic character. -/
theorem compositum_charProd_injective
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (ζ : M) (hζ : IsPrimitiveRoot ζ m) :
    Function.Injective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K)) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  rw [MonoidHom.prod_apply, Prod.mk_eq_one] at hσ
  obtain ⟨hσL, hσζ⟩ := hσ
  have hζfix : σ ζ = ζ := fixes_of_autToPow_eq_one K M m ζ hζ σ hσζ
  have hLfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
    intro x
    have hcomm := σ.restrictNormal_commutes L x
    have hrn : σ.restrictNormal L = (1 : Gal(L/K)) := hσL
    rw [hrn] at hcomm
    simpa using hcomm.symm
  exact algEquiv_eq_one_of_fixes_cyclotomic_generator K L M ζ
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) σ hLfix hζfix

/-- Source: AINTLIB Abelian.lean:314, source-local crossing argument. -/
theorem compositum_charProd_bijective
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (hcop : ((NumberField.discr L).natAbs).Coprime m) (ζ : M) (hζ : IsPrimitiveRoot ζ m) :
    Function.Bijective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K)) := by
  haveI : FiniteDimensional K M := inferInstance
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  set χK : Gal(M/K) →* (ZMod m)ˣ := hζ.autToPow K with hχK
  set Φ : Gal(M/K) →* Gal(L/K) × (ZMod m)ˣ :=
    (AlgEquiv.restrictNormalHom L).prod χK with hΦ
  have hML : Module.finrank L M = m.totient := cyclotomicField_finrank_eq L M m hcop
  have hcardMK : Nat.card Gal(M/K) = Nat.card Gal(L/K) * Nat.card (ZMod m)ˣ := by
    rw [IsGalois.card_aut_eq_finrank K M, IsGalois.card_aut_eq_finrank K L,
      ← Module.finrank_mul_finrank K L M, hML, Nat.card_eq_fintype_card (α := (ZMod m)ˣ),
      ZMod.card_units_eq_totient]
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    rw [hΦ, MonoidHom.prod_apply, Prod.mk_eq_one] at hσ
    obtain ⟨hσL, hσζ⟩ := hσ
    have hζfix : σ ζ = ζ := by
      have hspec := hζ.autToPow_spec K σ
      rw [hχK] at hσζ
      rw [hσζ] at hspec
      rw [← hspec, Units.val_one]
      rcases eq_or_lt_of_le (NeZero.one_le (n := m)) with h1 | h1
      · have hm1 : m = 1 := h1.symm
        subst hm1
        have : ζ = 1 := by simpa using hζ.pow_eq_one
        simp [this]
      · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega), pow_one]
    have hLfix : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
      intro x
      have hcomm := σ.restrictNormal_commutes L x
      have hrn : σ.restrictNormal L = (1 : Gal(L/K)) := hσL
      rw [hrn] at hcomm
      simpa using hcomm.symm
    have htop : Algebra.adjoin L {ζ} = (⊤ : Subalgebra L M) :=
      IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ Algebra.adjoin L {ζ} := htop ▸ Algebra.mem_top
    refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
    · intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; rw [hζfix]; rfl
    · intro r; exact hLfix r
    · intro a b _ _ ha hb; rw [map_add, ha, hb]; rfl
    · intro a b _ _ ha hb; rw [map_mul, ha, hb]; rfl
  exact (Nat.bijective_iff_injective_and_card _).mpr ⟨hΦinj, by rw [hcardMK, Nat.card_prod]⟩

/-- Source: AINTLIB Abelian.lean:369, source-local crossing argument. -/
theorem autToPow_L_bijective
    (L M : Type*) [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra L M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (hcop : ((NumberField.discr L).natAbs).Coprime m) (ζ : M) (hζ : IsPrimitiveRoot ζ m) :
    Function.Bijective (hζ.autToPow L) := by
  haveI : IsGalois L M := IsCyclotomicExtension.isGalois {m} L M
  have hML : Module.finrank L M = m.totient := cyclotomicField_finrank_eq L M m hcop
  have hcardML : Nat.card Gal(M/L) = Nat.card (ZMod m)ˣ := by
    rw [IsGalois.card_aut_eq_finrank L M, hML, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient]
  exact (Nat.bijective_iff_injective_and_card _).mpr ⟨hζ.autToPow_injective L, hcardML⟩

/-- Source: AINTLIB Abelian.lean:411, source-local crossing argument. -/
theorem compositum_isCyclotomic_over_fixedField
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (g : Gal(M/K))
    (_hmeet : Subgroup.zpowers g ⊓
      (IntermediateField.adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥) :
    letI := (IntermediateField.fixedField (Subgroup.zpowers g)).isScalarTower_mid'
    IsCyclotomicExtension {m} ↥(IntermediateField.fixedField (Subgroup.zpowers g)) M := by
  set F : IntermediateField K M := IntermediateField.fixedField (Subgroup.zpowers g)
  set Kμ : IntermediateField K M := IntermediateField.adjoin K {b : M | b ^ m = 1}
  obtain ⟨ζ, hζ⟩ : ∃ r : M, IsPrimitiveRoot r m :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M (Set.mem_singleton m) (NeZero.ne m)
  have hadjζ : IntermediateField.adjoin K {ζ} = Kμ :=
    le_antisymm
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
        (IntermediateField.subset_adjoin K _ hζ.pow_eq_one)))
      (IntermediateField.adjoin_le_iff.mpr fun x hx ↦ by
        obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one (Set.mem_setOf_eq ▸ hx)
        exact pow_mem (IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)) i)
  have hsup : (F ⊔ Kμ).fixingSubgroup = ⊥ := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField, _hmeet]
  have htop : F ⊔ Kμ = ⊤ := by
    have := congrArg IntermediateField.fixedField hsup
    rwa [IsGalois.fixedField_fixingSubgroup, IntermediateField.fixedField_bot] at this
  have htopF : IntermediateField.adjoin (↥F) {ζ} = ⊤ := by
    apply IntermediateField.restrictScalars_injective K
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, hadjζ, htop]
    rfl
  haveI : Algebra.IsIntegral ↥F M := Algebra.IsIntegral.of_finite ↥F M
  haveI hcyc : IsCyclotomicExtension {m} ↥F (IntermediateField.adjoin (↥F) {ζ}) :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := ↥F) hζ
  rw [htopF] at hcyc
  exact IsCyclotomicExtension.equiv (S := {m}) (A := ↥F) (f := IntermediateField.topEquiv)

/-- Source: AINTLIB Abelian.lean:452, source-local crossing argument. -/
theorem smul_algebraMap_eq_repl
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (σ : Gal(M/K)) (y : 𝓞 L) :
    σ • (algebraMap (𝓞 L) (𝓞 M) y) = algebraMap (𝓞 L) (𝓞 M) ((σ.restrictNormal L) • y) := by
  haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
  have hbridgeM : ∀ (g : M ≃ₐ[K] M) (x : 𝓞 M), ((g • x : 𝓞 M) : M) = g • (x : M) := fun g x ↦
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := M ≃ₐ[K] M) (R := 𝓞 M) (S := M) g x 1).symm
  have hbridgeL : ∀ (g : L ≃ₐ[K] L) (z : 𝓞 L), ((g • z : 𝓞 L) : L) = g • ((z : L)) := fun g z ↦
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := L ≃ₐ[K] L) (R := 𝓞 L) (S := L) g z 1).symm
  have hcoe : ∀ z : 𝓞 L, ((algebraMap (𝓞 L) (𝓞 M) z : 𝓞 M) : M) = algebraMap L M (z : L) :=
    fun z ↦ by
      rw [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 M) M,
        RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 L) L M]
  rw [RingOfIntegers.ext_iff, hbridgeM, hcoe y, hcoe ((σ.restrictNormal L) • y), hbridgeL,
    AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes]

/-- Source: AINTLIB Abelian.lean:476, source-local crossing argument. -/
theorem isArithFrobAt_restrictNormal_repl
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (σ : Gal(M/K)) (𝔓 : Ideal (𝓞 M))
    (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    IsArithFrobAt (𝓞 K) (σ.restrictNormal L) (𝔓.under (𝓞 L)) := by
  haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
  have hunder : (𝔓.under (𝓞 L)).under (𝓞 K) = 𝔓.under (𝓞 K) := Ideal.under_under 𝔓
  intro y
  rw [hunder, Ideal.under, Ideal.mem_comap, map_sub, map_pow,
    MulSemiringAction.toAlgHom_apply, ← smul_algebraMap_eq_repl K L M σ y]
  exact hσ (algebraMap (𝓞 L) (𝓞 M) y)

/-- Source: AINTLIB Abelian.lean:489, source-local crossing argument. -/
theorem frobeniusClass_proj_isPrime_aux
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M]
    (σ : Gal(L/K)) (τM : Gal(M/K)) (_hτM : AlgEquiv.restrictNormalHom L τM = σ)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (_hunrM : UnramifiedIn K M 𝔭) (_hunrL : UnramifiedIn K L 𝔭)
    (_hfr : frobeniusClass K M 𝔭 = ConjClasses.mk τM) :
    frobeniusClass K L 𝔭 = ConjClasses.mk σ := by
  obtain ⟨𝔓, h𝔓p, h𝔓lo, -⟩ := exists_prime_liesOver K M 𝔭 (UnramifiedIn.ne_bot K M _hunrM)
  haveI := h𝔓p
  haveI := h𝔓lo
  haveI : Finite (𝓞 M ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
    (ne_bot_of_ramificationIdx_eq_one K M (UnramifiedIn.ramificationIdx_eq_one K M _hunrM 𝔓 h𝔓lo))
  set σM : Gal(M/K) := arithFrobAt (𝓞 K) Gal(M/K) 𝔓
  have hMfrobσM : IsArithFrobAt (𝓞 K) σM 𝔓 := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(M/K) 𝔓
  have hconjM : IsConj σM τM := ConjClasses.mk_eq_mk_iff_isConj.mp
    ((frobeniusClass_eq_mk_of_isArithFrobAt K M 𝔭 _hunrM σM 𝔓 hMfrobσM h𝔓lo).symm.trans _hfr)
  haveI : (𝔓.under (𝓞 L)).IsPrime := Ideal.IsPrime.under (𝓞 L) 𝔓
  haveI : (𝔓.under (𝓞 L)).LiesOver 𝔭 := ⟨((Ideal.under_under 𝔓).trans h𝔓lo.over.symm).symm⟩
  rw [frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 _hunrL (σM.restrictNormal L) (𝔓.under (𝓞 L))
    (isArithFrobAt_restrictNormal_repl K L M σM 𝔓 hMfrobσM) inferInstance]
  refine ConjClasses.mk_eq_mk_iff_isConj.mpr ?_
  have hconjL := MonoidHom.map_isConj (AlgEquiv.restrictNormalHom L) hconjM
  rwa [_hτM] at hconjL

/-- Source: AINTLIB Abelian.lean:521, source-local crossing argument. -/
theorem frobeniusClass_proj
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M]
    (σ : Gal(L/K)) (τM : Gal(M/K)) (_hτM : AlgEquiv.restrictNormalHom L τM = σ)
    (𝔭 : Ideal (𝓞 K)) (_hunrM : UnramifiedIn K M 𝔭) (_hunrL : UnramifiedIn K L 𝔭)
    (_hfr : frobeniusClass K M 𝔭 = ConjClasses.mk τM) :
    frobeniusClass K L 𝔭 = ConjClasses.mk σ := by
  by_cases hp : 𝔭.IsPrime
  · haveI := hp
    exact frobeniusClass_proj_isPrime_aux K L M σ τM _hτM 𝔭 _hunrM _hunrL _hfr
  · have hMjunk : frobeniusClass K M 𝔭 = ConjClasses.mk 1 := by
      rw [frobeniusClass, dif_neg fun h ↦ hp h.1]
    have hLjunk : frobeniusClass K L 𝔭 = ConjClasses.mk 1 := by
      rw [frobeniusClass, dif_neg fun h ↦ hp h.1]
    have hconj : IsConj (1 : Gal(M/K)) τM :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hMjunk.symm.trans _hfr)
    have hτM1 : τM = 1 := isConj_one_right.mp hconj
    have hσ1 : σ = 1 := by rw [← _hτM, hτM1, map_one]
    rw [hLjunk, hσ1]

/-- Source: AINTLIB Abelian.lean:580, source-local crossing argument. -/
theorem isGalois_compositum_base
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] (M : Type*) [Field M] [NumberField M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [IsCyclotomicExtension {m} L M] : IsGalois K M := by
  obtain ⟨ζ, hζ⟩ : ∃ r : M, IsPrimitiveRoot r m :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M (Set.mem_singleton m) (NeZero.ne m)
  haveI : FiniteDimensional K M := inferInstance
  haveI hsep : Algebra.IsSeparable K M := inferInstance
  set A : IntermediateField K M := (IsScalarTower.toAlgHom K L M).fieldRange with hA
  set B : IntermediateField K M := IntermediateField.adjoin K {ζ} with hB
  haveI hAnormal : Normal K A :=
    Normal.of_algEquiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L M))
  haveI hBcyc : IsCyclotomicExtension {m} K B :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := K)
  haveI hBgal : IsGalois K B := IsCyclotomicExtension.isGalois (S := {m}) (K := K) (L := B)
  haveI hBnormal : Normal K B := hBgal.to_normal
  have hsup : A ⊔ B = ⊤ := by
    have hζalg : IsAlgebraic K ζ := Algebra.IsAlgebraic.isAlgebraic ζ
    have hsubalg : (IsScalarTower.toAlgHom K L M).range ⊔ Algebra.adjoin K {ζ}
        = (⊤ : Subalgebra K M) := by
      have htop : (Algebra.adjoin L {ζ} : Subalgebra L M) = ⊤ :=
        IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ
      rw [← Algebra.Subalgebra.restrictScalars_adjoin (R := K) (S := L) (s := {ζ}), htop,
        Subalgebra.restrictScalars_top]
    apply IntermediateField.toSubalgebra_injective
    rw [hA, hB, IntermediateField.sup_toSubalgebra_of_isAlgebraic_left,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg,
      AlgHom.fieldRange_toSubalgebra, IntermediateField.top_toSubalgebra]
    exact hsubalg
  haveI hnormal : Normal K M := by
    have h := IntermediateField.normal_sup K M A B
    rw [hsup] at h
    exact Normal.of_algEquiv (IntermediateField.topEquiv (F := K) (E := M))
  exact IsGalois.mk

/-- Source: AINTLIB Abelian.lean:620, source-local crossing argument. -/
theorem unramifiedIn_tower_descend
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K L] [IsGalois K M]
    (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K M 𝔭) : UnramifiedIn K L 𝔭 := by
  haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
  refine ⟨hunr.1, fun 𝔮 h𝔮max h𝔮lo ↦ ?_⟩
  haveI := h𝔮max
  haveI := h𝔮lo
  haveI h𝔮p : 𝔮.IsPrime := h𝔮max.isPrime
  have h𝔮bot : 𝔮 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔮
  obtain ⟨𝔓, _, h𝔓p, h𝔓comap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 M) 𝔮 ⊥ (by simp)
  haveI := h𝔓p
  haveI h𝔓lo𝔮 : 𝔓.LiesOver 𝔮 := ⟨h𝔓comap.symm⟩
  have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔮bot 𝔓
  haveI h𝔓max : 𝔓.IsMaximal := h𝔓p.isMaximal h𝔓bot
  have h𝔮under : Ideal.under (𝓞 L) 𝔓 = 𝔮 := h𝔓lo𝔮.over.symm
  have h𝔭under : Ideal.under (𝓞 K) 𝔮 = 𝔭 := h𝔮lo.over.symm
  haveI h𝔓lo𝔭 : 𝔓.LiesOver 𝔭 := ⟨by rw [← h𝔭under, ← h𝔮under, Ideal.under_under]⟩
  have hunderP : Ideal.under (𝓞 K) 𝔓 = 𝔭 := h𝔓lo𝔭.over.symm
  have hP1 : Ideal.ramificationIdx (Ideal.under (𝓞 K) 𝔓) 𝔓 = 1 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔓bot).mp (hunr.2 𝔓 h𝔓max h𝔓lo𝔭)
  rw [hunderP] at hP1
  have htower := Ideal.ramificationIdx_algebra_tower (R := 𝓞 K) (S := 𝓞 L) (T := 𝓞 M)
    (p := 𝔭) (P := 𝔮) (Q := 𝔓) (Ideal.map_ne_bot_of_ne_bot h𝔮bot)
    (Ideal.map_ne_bot_of_ne_bot hunr.1) (by rw [Ideal.map_le_iff_le_comap, h𝔓comap])
  rw [hP1] at htower
  have he𝔮 : Ideal.ramificationIdx 𝔭 𝔮 = 1 := Nat.eq_one_of_mul_eq_one_right htower.symm
  refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔮bot).mpr ?_
  rw [h𝔭under]
  exact he𝔮

/-- Source: AINTLIB Abelian.lean:658, source-local crossing argument. -/
theorem autToPow_eq_one_of_fixes
    (K M : Type*) [Field K] [Field M] [Algebra K M] (m : ℕ) [NeZero m]
    (ζ : M) (hζ : IsPrimitiveRoot ζ m) (g : Gal(M/K)) (hg : g ζ = ζ) :
    hζ.autToPow K g = 1 := by
  have hspec := hζ.autToPow_spec K g
  rw [hg] at hspec
  set u : (ZMod m)ˣ := hζ.autToPow K g with hu
  have hmod : (u : ZMod m).val ≡ 1 [MOD m] := by
    have hisu : IsUnit ζ := hζ.isUnit (NeZero.ne m)
    lift ζ to Mˣ using hisu with z hz
    have hzp : IsPrimitiveRoot z m := by rwa [IsPrimitiveRoot.coe_units_iff] at hζ
    have hord : orderOf z = m := (IsPrimitiveRoot.eq_orderOf hzp).symm
    have h' : z ^ (u : ZMod m).val = z ^ (1 : ℕ) := by
      apply Units.ext
      push_cast
      rwa [pow_one]
    rwa [pow_eq_pow_iff_modEq, hord] at h'
  have hu1 : (u : ZMod m) = 1 := by
    have hcast : ((u : ZMod m).val : ZMod m) = (1 : ZMod m) := by
      rw [← Nat.cast_one]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    rwa [ZMod.natCast_val, ZMod.cast_id] at hcast
  exact Units.ext hu1

/-- Source: AINTLIB Abelian.lean:687, source-local crossing argument. -/
theorem zpowers_inf_fixingSubgroup_eq_bot_aux
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K L] [IsGalois K M]
    (m : ℕ) [NeZero m] (ζ : M) (hζ : IsPrimitiveRoot ζ m) (σ : Gal(L/K)) (τ : (ZMod m)ˣ)
    (hτ : Nat.card Gal(L/K) ∣ orderOf τ) (s : Gal(M/K))
    (hsrestr : AlgEquiv.restrictNormalHom L s = σ) (hschar : hζ.autToPow K s = τ)
    (hΦbij : Function.Bijective ((AlgEquiv.restrictNormalHom L).prod (hζ.autToPow K))) :
    Subgroup.zpowers s ⊓
        (IntermediateField.adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥ := by
  rw [eq_bot_iff]
  rintro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨⟨k, hk⟩, hgfix⟩ := hg
  simp only at hk
  have hgζ : g ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ g).mp hgfix ζ <|
      IntermediateField.subset_adjoin K _ hζ.pow_eq_one
  have hχg : hζ.autToPow K g = 1 := autToPow_eq_one_of_fixes K M m ζ hζ g hgζ
  have hχgτ : τ ^ k = 1 := by
    rw [← hschar, ← map_zpow, hk]
    exact hχg
  have hGk : (Nat.card Gal(L/K) : ℤ) ∣ k :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hτ) (orderOf_dvd_iff_zpow_eq_one.mpr hχgτ)
  have hσk : σ ^ k = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp
      (dvd_trans (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard σ)) hGk)
  have hrestrg : AlgEquiv.restrictNormalHom L g = 1 := by rw [← hk, map_zpow, hsrestr, hσk]
  rw [Subgroup.mem_bot]
  apply hΦbij.injective
  rw [MonoidHom.prod_apply, MonoidHom.prod_apply, hrestrg, hχg, map_one, map_one]

/-- Source: AINTLIB Abelian.lean:723, source-local crossing argument. -/
theorem density_crossing_fibre_aux
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K L] [IsGalois K M]
    [IsMulCommutative Gal(M/K)] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) (s : Gal(M/K))
    (hgate : Subgroup.zpowers s ⊓
      (IntermediateField.adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K M 𝔭 ∧
        frobeniusClass K M 𝔭 = ConjClasses.mk s}
      ((Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹) := by
  set F : IntermediateField K M := IntermediateField.fixedField (Subgroup.zpowers s) with hF
  haveI : IsScalarTower K ↥F M := F.isScalarTower_mid'
  haveI : IsCyclotomicExtension {m} ↥F M :=
    compositum_isCyclotomic_over_fixedField K L M m s hgate
  set σE : Gal(M/↥F) :=
    IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers s) ⟨s, Subgroup.mem_zpowers s⟩
  have hlift := density_lift_through_fixedField K M s F σE
    (by ext x; rfl) rfl (chebotarev_cyclotomic (K := ↥F) (L := M) m hm4 σE)
  have hcarrier : Nat.card (ConjClasses.mk s).carrier = 1 := by
    letI : CommMonoid Gal(M/K) := IsMulCommutative.instCommMonoid
    have hcar : (ConjClasses.mk s).carrier = {s} := by
      ext a
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
        isConj_iff_eq, Set.mem_singleton_iff]
    rw [hcar, Nat.card_coe_set_eq, Set.ncard_singleton]
  have hcardMK : Nat.card Gal(M/K) = Nat.card Gal(L/K) * Nat.card (ZMod m)ˣ := by
    rw [IsGalois.card_aut_eq_finrank K M, IsGalois.card_aut_eq_finrank K L,
      ← Module.finrank_mul_finrank K L M, cyclotomicField_finrank_eq L M m hcop,
      Nat.card_eq_fintype_card (α := (ZMod m)ˣ), ZMod.card_units_eq_totient]
  rw [hcarrier, hcardMK] at hlift
  simpa using hlift

/-- Source: AINTLIB Abelian.lean:773, source-local crossing argument. -/
theorem exists_crossing_family_tagged
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (_hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    ∃ (t : Ideal (𝓞 K) → (ZMod m)ˣ)
      (S : {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} → Set (Ideal (𝓞 K))),
      (∀ τ, S τ ⊆ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ}) ∧
      (∀ τ, ∀ 𝔭 ∈ S τ, t 𝔭 = (τ : (ZMod m)ˣ)) ∧
      (∀ τ, HasDirichletDensity (S τ)
          ((Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹)) := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  let M := CyclotomicField m L
  haveI : IsGalois K M := isGalois_compositum_base K L m M
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  haveI : FiniteDimensional K M := inferInstance
  obtain ⟨ζ, hζ⟩ : ∃ r : M, IsPrimitiveRoot r m :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M (Set.mem_singleton m) (NeZero.ne m)
  set χK : Gal(M/K) →* (ZMod m)ˣ := hζ.autToPow K with hχK
  have hΦbij : Function.Bijective ((AlgEquiv.restrictNormalHom L).prod χK) :=
    compositum_charProd_bijective K L M m hcop ζ hζ
  set equivΦ : Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ :=
    MulEquiv.ofBijective _ hΦbij with hequivΦ
  set e2 : Gal(M/L) ≃* (ZMod m)ˣ :=
    MulEquiv.ofBijective (hζ.autToPow L) (autToPow_L_bijective L M m hcop ζ hζ) with he2
  haveI : IsMulCommutative Gal(M/L) :=
    .of_comm fun a b ↦ e2.injective (by rw [map_mul, map_mul]; exact mul_comm (e2 a) (e2 b))
  haveI hGcomm : ∀ x y : Gal(L/K), x * y = y * x := fun x y ↦ mul_comm' x y
  haveI : IsMulCommutative Gal(M/K) :=
    .of_comm fun a b ↦ equivΦ.injective (by
      rw [map_mul, map_mul, Prod.mul_def, Prod.mul_def, hGcomm, mul_comm
        ((equivΦ a).2) ((equivΦ b).2)])
  set σM : (ZMod m)ˣ → Gal(M/K) := fun τ ↦ equivΦ.symm (σ, τ) with hσM
  have hσMpair : ∀ τ, (AlgEquiv.restrictNormalHom L (σM τ), χK (σM τ)) = (σ, τ) :=
    fun τ ↦ equivΦ.apply_symm_apply (σ, τ)
  have hσMrestr : ∀ τ, AlgEquiv.restrictNormalHom L (σM τ) = σ :=
    fun τ ↦ congrArg Prod.fst (hσMpair τ)
  have hσMchar : ∀ τ, χK (σM τ) = τ :=
    fun τ ↦ congrArg Prod.snd (hσMpair τ)
  refine ⟨fun 𝔭 ↦ χK (frobeniusClass K M 𝔭).out,
    fun τ ↦ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K M 𝔭 ∧
      frobeniusClass K M 𝔭 = ConjClasses.mk (σM τ)}, ?_, ?_, ?_⟩
  · rintro τ 𝔭 ⟨hp, hunrM, hfr⟩
    have hunrL : UnramifiedIn K L 𝔭 := unramifiedIn_tower_descend K L M 𝔭 hunrM
    exact ⟨hp, hunrL,
      frobeniusClass_proj K L M σ (σM τ) (hσMrestr τ) 𝔭 hunrM hunrL hfr⟩
  · rintro τ 𝔭 ⟨-, -, hfr⟩
    have hconj : IsConj (frobeniusClass K M 𝔭).out (σM (τ : (ZMod m)ˣ)) := by
      rw [hfr]
      exact ConjClasses.mk_eq_mk_iff_isConj.mp (Quotient.out_eq _)
    change χK (frobeniusClass K M 𝔭).out = (τ : (ZMod m)ˣ)
    rw [isConj_iff_eq.mp (χK.map_isConj hconj), hσMchar]
  · rintro ⟨τ, hτ⟩
    exact density_crossing_fibre_aux K L M m hm4 hcop (σM τ)
      (zpowers_inf_fixingSubgroup_eq_bot_aux K L M m ζ hζ σ τ hτ (σM τ) (hσMrestr τ)
        (hσMchar τ) hΦbij)

/-- Source: AINTLIB Abelian.lean:831, source-local crossing argument. -/
theorem exists_cyclotomicCrossing_fibres
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    ∃ S : {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} → Set (Ideal (𝓞 K)),
      (Set.univ : Set {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}).PairwiseDisjoint S ∧
      (∀ τ, S τ ⊆ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ}) ∧
      (∀ τ, HasDirichletDensity (S τ)
          ((Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹)) := by
  obtain ⟨t, S, hsub, htag, hd⟩ := exists_crossing_family_tagged K L σ m hm hm4 hcop
  exact ⟨S, pairwiseDisjoint_of_tag t Subtype.val Subtype.val_injective S htag, hsub, hd⟩

end Cox.Chebotarev
