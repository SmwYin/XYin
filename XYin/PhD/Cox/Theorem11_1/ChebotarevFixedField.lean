/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.RamificationInertia.Unramified
import XYin.PhD.Cox.Theorem11_1.ChebotarevFrobenius
import XYin.PhD.Cox.Theorem11_1.ChebotarevDensity

/-!
# Fixed-field density transfer

Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87` is not an imported dependency.
Contracts are adapted to pinned Lean 4.30.0. Local prerequisites precede their consumers. See the
declaration records for exact source matches and remaining port boundaries.
-/

noncomputable section
open Filter NumberField Topology Set UniqueFactorizationMonoid
open scoped ENNReal Pointwise
namespace Cox.Chebotarev
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]
variable {S : Set (Ideal (𝓞 K))} {δ : ℝ}

/-- Planning source: FixedFieldDensity.lean:55; statement placeholder. -/
theorem frobeniusFibre_card_eq_of_isConj
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (_hunr : UnramifiedIn K L 𝔭)
    (σ σ' : Gal(L/K)) (hc : IsConj σ σ') :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ 𝔓}
      = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ' 𝔓} := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm c) fun 𝔓 ↦ ?_)
  simp only [MulAction.toPerm_apply]
  constructor
  · rintro ⟨hp, hP, hne, hfrob⟩
    haveI := hp
    haveI := hP
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · rw [← Ideal.smul_bot c]
      exact (MulAction.injective c).ne hne
    · exact hc ▸ hfrob.conj c
  · rintro ⟨hp, hP, hne, hfrob⟩
    haveI := hp
    haveI := hP
    have hsmul : c⁻¹ • (c • 𝔓) = 𝔓 := inv_smul_smul c 𝔓
    haveI hp' : 𝔓.IsPrime := hsmul ▸ (inferInstance : (c⁻¹ • (c • 𝔓)).IsPrime)
    haveI hP' : 𝔓.LiesOver 𝔭 := hsmul ▸ (inferInstance : (c⁻¹ • (c • 𝔓)).LiesOver 𝔭)
    have hne' : 𝔓 ≠ ⊥ := by
      rw [← hsmul, ← Ideal.smul_bot c⁻¹]
      exact (MulAction.injective c⁻¹).ne hne
    refine ⟨hp', hP', hne', ?_⟩
    have hconj := hfrob.conj c⁻¹
    rwa [hsmul, ← hc, show c⁻¹ * (c * σ * c⁻¹) * c⁻¹⁻¹ = σ by group] at hconj

/-- Planning source: FixedFieldDensity.lean:92; statement placeholder. -/
theorem card_primesAbove_eq_card_carrier_mul_frobeniusFibre
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hCfrob : frobeniusClass K L 𝔭 = C)
    (hequi : ∀ σ' : Gal(L/K), IsConj σ σ' →
      Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
          IsArithFrobAt (𝓞 K) σ 𝔓}
        = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
          IsArithFrobAt (𝓞 K) σ' 𝔓}) :
    Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}
      = Nat.card C.carrier
        * Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
          IsArithFrobAt (𝓞 K) σ 𝔓} := by
  have hpbot : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L hunr
  haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal hpbot
  haveI : Finite (𝔭.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite 𝔭 (𝓞 L)).to_subtype
  haveI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} :=
    Finite.of_injective
      (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} ↦
        (⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩ : 𝔭.primesOver (𝓞 L)))
      fun _ _ hab ↦ Subtype.ext (by simpa using hab)
  haveI : Fintype C.carrier := Fintype.ofFinite _
  have hfinP : ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭), Finite (𝓞 L ⧸ 𝔓) :=
    fun 𝔓 _ hP ↦ UnramifiedIn.finite_quotient K L hunr 𝔓 hP
  have hmem : ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭),
      haveI := hfinP 𝔓 hP
      arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ∈ C.carrier := by
    intro 𝔓 _ hP
    haveI := hfinP 𝔓 hP
    rw [ConjClasses.mem_carrier_iff_mk_eq, ← frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr _ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) hP, hCfrob]
  have hconj : ∀ g : C.carrier, IsConj σ g.1 := by
    rintro ⟨g, hg⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq] at hg
    exact ConjClasses.mk_eq_mk_iff_isConj.mp (hσ.trans hg.symm)
  let F : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} → C.carrier := fun 𝔓 ↦
    haveI := 𝔓.2.1
    haveI := hfinP 𝔓.1 𝔓.2.2.1
    ⟨arithFrobAt (𝓞 K) Gal(L/K) 𝔓.1, hmem 𝔓.1 𝔓.2.2.1⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv F), Nat.card_sigma]
  have hfib : ∀ g : C.carrier,
      Nat.card {𝔓 // F 𝔓 = g}
        = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
            IsArithFrobAt (𝓞 K) σ 𝔓} := by
    intro g
    rw [hequi g.1 (hconj g)]
    refine Nat.card_congr ⟨fun x ↦ ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2, ?_⟩,
      fun x ↦ ⟨⟨x.1, by obtain ⟨hp, hP, hne, _⟩ := x.2; exact ⟨hp, hP, hne⟩⟩, ?_⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
    · haveI := x.1.2.1
      haveI := hfinP x.1.1 x.1.2.2.1
      rw [← Subtype.ext_iff.mp x.2]
      exact IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) x.1.1
    · obtain ⟨hp, hP, hne, hg⟩ := x.2
      haveI := hp
      haveI := hP
      haveI := hfinP x.1 hP
      haveI : Algebra.IsUnramifiedAt (𝓞 K) x.1 :=
        (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hne).mpr
          (UnramifiedIn.ramificationIdx_eq_one K L hunr x.1 hP)
      exact Subtype.ext (eq_arithFrobAt_of_isArithFrobAt K L x.1 g.1 hg).symm
  simp_rw [hfib]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]

/-- Planning source: FixedFieldDensity.lean:162; statement placeholder. -/
theorem count_frobenius_eq_sigma_mul_card_carrier
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (_hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (_hCfrob : frobeniusClass K L 𝔭 = C) :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭)
        (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ 𝔓}
      * Nat.card C.carrier
      = Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} :=
  (mul_comm _ _).trans (card_primesAbove_eq_card_carrier_mul_frobeniusFibre K L σ C _hσ 𝔭 hunr
    _hCfrob fun σ' hc ↦ frobeniusFibre_card_eq_of_isConj K L 𝔭 hunr σ σ' hc).symm

/-- Planning source: FixedFieldDensity.lean:186; statement placeholder. -/
theorem count_primes_above_with_frobenius_eq_sigma
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (_hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (_hCfrob : frobeniusClass K L 𝔭 = C) :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭)
        (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ 𝔓}
      * orderOf σ * Nat.card C.carrier
      = Nat.card Gal(L/K) := by
  rw [mul_right_comm,
    count_frobenius_eq_sigma_mul_card_carrier K L σ C _hσ 𝔭 hunr _hCfrob]
  exact card_primesAbove_mul_orderOf_eq K L σ C _hσ 𝔭 hunr _hCfrob

/-- Planning source: FixedFieldDensity.lean:233; statement placeholder. -/
theorem arithFrobAt_restrictScalars_eq {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] [IsGalois K L] (E : IntermediateField K L)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunrK : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1)
    (_hunrE : Ideal.ramificationIdx (𝔓.under (𝓞 ↥E)) 𝔓 = 1)
    (hnorm : Nat.card (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))) :
    haveI : IsScalarTower K ↥E L := E.isScalarTower_mid'
    haveI : Finite (𝓞 L ⧸ 𝔓) :=
      Ideal.finiteQuotientOfFreeOfNeBot 𝔓 (ne_bot_of_ramificationIdx_eq_one K L hunrK)
    haveI : IsGalois (↥E) L := IsGalois.tower_top_intermediateField E
    (arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓).restrictScalars K = arithFrobAt (𝓞 K) Gal(L/K) 𝔓 := by
  haveI : IsScalarTower K ↥E L := E.isScalarTower_mid'
  haveI : IsGalois (↥E) L := IsGalois.tower_top_intermediateField E
  haveI : IsGaloisGroup Gal(L/(↥E)) (↥E) L := IsGaloisGroup.of_isGalois (↥E) L
  haveI hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hunrK
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  set σE := arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓 with hσE
  have hKfrob1 : IsArithFrobAt (𝓞 K) (σE.restrictScalars K) 𝔓 := by
    intro x
    have hact : (σE.restrictScalars K) • x = σE • x := Subtype.ext (by
      change (σE.restrictScalars K) • (x : L) = σE • (x : L)
      rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictScalars_apply])
    change (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) (σE.restrictScalars K)) x
      - x ^ Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) ∈ 𝔓
    rw [show x ^ Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))
          = x ^ Nat.card (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) by rw [hnorm],
      show (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) (σE.restrictScalars K)) x = σE • x by
        rw [← hact]
        rfl]
    exact IsArithFrobAt.arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓 x
  have hmem := hKfrob1.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
  rw [inertiaGroup_trivial_of_unramified K L 𝔓 hunrK, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

/-- Planning source: FixedFieldDensity.lean:296; statement placeholder. -/
theorem card_stabilizer_eq_orderOf {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓) :
    Nat.card (MulAction.stabilizer Gal(L/K) 𝔓) = orderOf σ := by
  haveI := hPK
  have hraK := UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 hPK
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hraK
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := UnramifiedIn.ne_bot K L hunrK
  haveI : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  haveI : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  haveI : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    letI : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
    letI : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    haveI : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpbot
    haveI : Algebra.IsAlgebraic (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hinertK : (𝔓.under (𝓞 K)).inertiaDeg 𝔓 = orderOf σ := by
    rw [Ideal.inertiaDeg_algebraMap, orderOf_eq_finrank_of_isArithFrobAt K L σ 𝔓 hraK hfrob]
  rw [Ideal.card_stabilizer_eq (G := Gal(L/K)) (𝔓.under (𝓞 K)) hpbot 𝔓,
    Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K), hraK, one_mul,
    Ideal.inertiaDegIn_eq_inertiaDeg (𝔓.under (𝓞 K)) 𝔓 Gal(L/K), hinertK]

/-- Planning source: FixedFieldDensity.lean:306; statement placeholder. -/
theorem stabilizer_eq_zpowers_of_frobenius {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓) :
    MulAction.stabilizer Gal(L/K) 𝔓 = Subgroup.zpowers σ := by
  have hmem : σ ∈ MulAction.stabilizer Gal(L/K) 𝔓 := hfrob.mem_stabilizer
  exact (Subgroup.eq_of_le_of_card_ge (by rwa [Subgroup.zpowers_le])
    (by rw [Nat.card_zpowers, card_stabilizer_eq_orderOf σ 𝔓 hunrK hPK hfrob])).symm

/-- Planning source: FixedFieldDensity.lean:273; statement placeholder. -/
theorem stabilizer_intermediate_eq_top_of_frobenius {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (_horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    MulAction.stabilizer
        Gal(L/↥(IntermediateField.fixedField (Subgroup.zpowers σ))) 𝔓 = ⊤ := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  have hstab : Subgroup.zpowers σ = MulAction.stabilizer Gal(L/K) 𝔓 :=
    (stabilizer_eq_zpowers_of_frobenius σ 𝔓 hunrK hPK hfrob).symm
  rw [eq_top_iff]
  intro τ _
  rw [MulAction.mem_stabilizer_iff]
  change τ • 𝔓 = 𝔓
  have hmemfix : τ.restrictScalars K
      ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField (Subgroup.zpowers σ)) :=
    fun x ↦ τ.commutes x
  rw [IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ)] at hmemfix
  have hstabmem : τ.restrictScalars K ∈ MulAction.stabilizer Gal(L/K) 𝔓 := hstab ▸ hmemfix
  exact MulAction.mem_stabilizer_iff.mp hstabmem

/-- Planning source: FixedFieldDensity.lean:359; statement placeholder. -/
theorem ramificationIdx_intermediate_eq_one {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] (E : IntermediateField K L)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    Ideal.ramificationIdx (𝔓.under (𝓞 ↥E)) 𝔓 = 1 := by
  haveI : IsScalarTower K ↥E L := E.isScalarTower_mid'
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 ↥E)) := Ideal.over_under (A := 𝓞 ↥E) (P := 𝔓)
  haveI : (𝔓.under (𝓞 ↥E)).LiesOver (𝔓.under (𝓞 K)) := inferInstance
  have htower := Ideal.ramificationIdx_algebra_tower' (𝔓.under (𝓞 K)) (𝔓.under (𝓞 ↥E)) 𝔓
  rw [hunr] at htower
  exact Nat.eq_one_of_mul_eq_one_left htower.symm

/-- Planning source: FixedFieldDensity.lean:379; statement placeholder. -/
theorem inertiaDeg_over_E_eq_orderOf {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).inertiaDeg 𝔓 =
      orderOf σ := by
  set E := IntermediateField.fixedField (Subgroup.zpowers σ) with hE
  haveI : IsScalarTower K ↥E L := E.isScalarTower_mid'
  haveI : IsGalois (↥E) L := IsGalois.tower_top_intermediateField _
  have hraK := UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 hPK
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hraK
  haveI : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  haveI hPPE : 𝔓.LiesOver (𝔓.under (𝓞 ↥E)) := Ideal.over_under (A := 𝓞 ↥E) (P := 𝔓)
  have hpEbot : 𝔓.under (𝓞 ↥E) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 ↥E) hPbot
  haveI : (𝔓.under (𝓞 ↥E)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 ↥E)).IsPrime).isMaximal hpEbot
  have hraE : Ideal.ramificationIdx (𝔓.under (𝓞 ↥E)) 𝔓 = 1 :=
    ramificationIdx_intermediate_eq_one E 𝔓 hraK
  haveI : Algebra.IsSeparable (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) (𝓞 L ⧸ 𝔓) := by
    letI : Field (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) := Ideal.Quotient.field _
    letI : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    haveI : Finite (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpEbot
    haveI : Algebra.IsAlgebraic (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) (𝓞 L ⧸ 𝔓) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hstabE : MulAction.stabilizer Gal(L/(↥E)) 𝔓 = ⊤ :=
    stabilizer_intermediate_eq_top_of_frobenius σ 𝔓 hunrK hPK hfrob horderE
  have hcardE := Ideal.card_stabilizer_eq (G := Gal(L/(↥E))) (𝔓.under (𝓞 ↥E)) hpEbot 𝔓
  rw [hstabE, Subgroup.card_top,
    Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 ↥E)) 𝔓 Gal(L/(↥E)), hraE, one_mul,
    Ideal.inertiaDegIn_eq_inertiaDeg (𝔓.under (𝓞 ↥E)) 𝔓 Gal(L/(↥E))] at hcardE
  rw [← hcardE, horderE]

/-- Planning source: FixedFieldDensity.lean:325; statement placeholder. -/
theorem inertiaDeg_under_E_eq_one_of_frobenius {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    (𝔓.under (𝓞 K)).inertiaDeg
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) = 1 := by
  set E := IntermediateField.fixedField (Subgroup.zpowers σ) with hE
  haveI : IsScalarTower K ↥E L := E.isScalarTower_mid'
  have hraK := UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 hPK
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hraK
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := UnramifiedIn.ne_bot K L hunrK
  haveI : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  haveI : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  haveI hPEp : (𝔓.under (𝓞 ↥E)).IsPrime := inferInstance
  haveI hPK' : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  haveI hPEK : (𝔓.under (𝓞 ↥E)).LiesOver (𝔓.under (𝓞 K)) := inferInstance
  haveI hPPE : 𝔓.LiesOver (𝔓.under (𝓞 ↥E)) := Ideal.over_under (A := 𝓞 ↥E) (P := 𝔓)
  have hpEbot : 𝔓.under (𝓞 ↥E) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 ↥E) hPbot
  haveI : (𝔓.under (𝓞 ↥E)).IsMaximal := hPEp.isMaximal hpEbot
  have hinertTower : (𝔓.under (𝓞 K)).inertiaDeg 𝔓
      = (𝔓.under (𝓞 K)).inertiaDeg (𝔓.under (𝓞 ↥E))
        * (𝔓.under (𝓞 ↥E)).inertiaDeg 𝔓 :=
    Ideal.inertiaDeg_algebra_tower (𝔓.under (𝓞 K)) (𝔓.under (𝓞 ↥E)) 𝔓
  have hinertK : (𝔓.under (𝓞 K)).inertiaDeg 𝔓 = orderOf σ := by
    rw [Ideal.inertiaDeg_algebraMap, orderOf_eq_finrank_of_isArithFrobAt K L σ 𝔓 hraK hfrob]
  have hfPE : (𝔓.under (𝓞 ↥E)).inertiaDeg 𝔓 = orderOf σ :=
    inertiaDeg_over_E_eq_orderOf σ 𝔓 hunrK hPK hfrob horderE
  have hpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  rw [hinertK, hfPE] at hinertTower
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact hinertTower.symm)

/-- Planning source: FixedFieldDensity.lean:386; statement placeholder. -/
theorem residue_card_under_E_eq_of_frobenius {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    Nat.card (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ⧸
      𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
      = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := UnramifiedIn.ne_bot K L hunrK
  haveI : (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).LiesOver
      (𝔓.under (𝓞 K)) := inferInstance
  have hinertPK : (𝔓.under (𝓞 K)).inertiaDeg
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) = 1 :=
    inertiaDeg_under_E_eq_one_of_frobenius σ 𝔓 hunrK hPK hfrob horderE
  have hnormP := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver
    (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) (𝔓.under (𝓞 K))
    inferInstance hpbot
  simp only [Submodule.cardQuot_apply, Ideal.absNorm_apply] at hnormP
  rw [hnormP, hinertPK, pow_one]

/-- Planning source: FixedFieldDensity.lean:398; statement placeholder. -/
theorem eq_of_liesOver_under_E_of_frobenius {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (𝔔 : Ideal (𝓞 L)) [𝔔.IsPrime]
    (hQ : haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      𝔔.LiesOver (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))) :
    𝔔 = 𝔓 := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  haveI : IsGaloisGroup Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
      (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L := IsGaloisGroup.of_isGalois _ L
  set E := IntermediateField.fixedField (Subgroup.zpowers σ) with hE
  haveI := hQ
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 ↥E)) := Ideal.over_under (A := 𝓞 ↥E) (P := 𝔓)
  have hstabE : MulAction.stabilizer Gal(L/(↥E)) 𝔓 = ⊤ :=
    stabilizer_intermediate_eq_top_of_frobenius σ 𝔓 hunrK hPK hfrob horderE
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (𝔓.under (𝓞 ↥E)) 𝔓 𝔔 Gal(L/(↥E))
  rw [← hτ, MulAction.mem_stabilizer_iff.mp (hstabE ▸ Subgroup.mem_top τ)]

/-- Planning source: FixedFieldDensity.lean:426; statement placeholder. -/
theorem arithFrobAt_E_eq_of_isArithFrobAt {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)))
    (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (_horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hraE : Ideal.ramificationIdx
        (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = 1)
    (hnorm : Nat.card (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
          ⧸ 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
        = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
      (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 hPK))
    haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
      IsGalois.tower_top_intermediateField _
    arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
      Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = σE := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  have hraK : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1 :=
    UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 hPK
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hraK
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot).mpr hraK
  have hbridge := arithFrobAt_restrictScalars_eq
    (IntermediateField.fixedField (Subgroup.zpowers σ)) 𝔓 hraK hraE hnorm
  rw [(eq_arithFrobAt_of_isArithFrobAt K L 𝔓 σ hfrob).symm] at hbridge
  exact AlgEquiv.restrictScalars_injective K (hbridge.trans hσE.symm)

/-- Planning source: FixedFieldDensity.lean:518; statement placeholder. -/
theorem eq_of_isArithFrobAt_of_frobeniusClass_eq_mk {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : UnramifiedIn K L 𝔭) (σ τ : Gal(L/K))
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭)
    (hfrob : IsArithFrobAt (𝓞 K) τ 𝔓)
    (hclass : frobeniusClass K L 𝔭 = ConjClasses.mk σ) : τ = σ := by
  have hcl := frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr τ 𝔓 hfrob hP
  rw [hclass] at hcl
  letI : CommMonoid Gal(L/K) := IsMulCommutative.instCommMonoid
  exact (isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hcl)).symm

/-- Planning source: FixedFieldDensity.lean:471; statement placeholder. -/
theorem exists_arithFrobAt_over_fibrePrime {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) [P.IsPrime]
    (hunrP : UnramifiedIn K L (P.under (𝓞 K)))
    (hPunr : UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P)
    (hPfrob : frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
      = ConjClasses.mk σE)
    (hPdeg : (P.under (𝓞 K)).inertiaDeg P = 1) (hPbot : P ≠ ⊥) :
    ∃ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver P) (_ : 𝔓 ≠ ⊥),
      𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) = P ∧
        IsArithFrobAt (𝓞 K) σ 𝔓 := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  obtain ⟨𝔓, h𝔓p, h𝔓lo, h𝔓bot⟩ := exists_prime_liesOver
    (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L P hPbot
  haveI := h𝔓p
  haveI := h𝔓lo
  have hPeq : 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) = P :=
    h𝔓lo.over.symm
  haveI hPPE : 𝔓.LiesOver (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
    Ideal.over_under (A := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) (P := 𝔓)
  have hunderK : 𝔓.under (𝓞 K) = P.under (𝓞 K) := by
    rw [← Ideal.under_under (B := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) 𝔓, hPeq]
  have hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)) := hunderK ▸ hunrP
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  have hinertPK1 : (𝔓.under (𝓞 K)).inertiaDeg
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) = 1 := by
    rw [hPeq, hunderK]
    exact hPdeg
  have hraE : Ideal.ramificationIdx
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = 1 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔓bot).mp
      (hPunr.2 𝔓 (h𝔓p.isMaximal h𝔓bot) (hPeq ▸ hPPE))
  have hnorm : Nat.card (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
        ⧸ 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
      = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) := by
    have hnP := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) (𝔓.under (𝓞 K))
      inferInstance (UnramifiedIn.ne_bot K L hunrK)
    simp only [Submodule.cardQuot_apply, Ideal.absNorm_apply] at hnP ⊢
    rw [hnP, hinertPK1, pow_one]
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 h𝔓bot
  have hfrEeqσE : arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
      Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = σE := by
    letI : CommMonoid Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
      IsMulCommutative.instCommMonoid
    have hcl := frobeniusClass_eq_mk_of_isArithFrobAt
      (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L P hPunr _ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
        Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓) (hPeq ▸ hPPE)
    rw [hPfrob] at hcl
    exact isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hcl.symm)
  have hfrobK : arithFrobAt (𝓞 K) Gal(L/K) 𝔓 = σ := by
    have hbridge := arithFrobAt_restrictScalars_eq
      (IntermediateField.fixedField (Subgroup.zpowers σ)) 𝔓
      (UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 inferInstance) hraE hnorm
    rw [hfrEeqσE, hσE] at hbridge
    exact hbridge.symm
  exact ⟨𝔓, h𝔓p, hPeq ▸ hPPE, h𝔓bot, hPeq,
    hfrobK ▸ IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓⟩

/-- Planning source: FixedFieldDensity.lean:546; statement placeholder. -/
theorem under_E_mem_fibre_of_isArithFrobAt {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) (hPbot : 𝔓 ≠ ⊥)
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) ∈
        {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
          P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
          frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
            = ConjClasses.mk σE ∧ (P.under (𝓞 K)).inertiaDeg P = 1} := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  haveI := hP
  have hunderK : 𝔓.under (𝓞 K) = 𝔭 := hP.over.symm
  have hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)) := hunderK ▸ hunr
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  have hraE := ramificationIdx_intermediate_eq_one
    (IntermediateField.fixedField (Subgroup.zpowers σ)) 𝔓
    (UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 inferInstance)
  have hinPK := inertiaDeg_under_E_eq_one_of_frobenius σ 𝔓 hunrK inferInstance hfrob horderE
  have hnorm := residue_card_under_E_eq_of_frobenius σ 𝔓 hunrK inferInstance hfrob horderE
  have hfrE := arithFrobAt_E_eq_of_isArithFrobAt σ σE hσE 𝔓 hunrK inferInstance hfrob horderE
    hraE hnorm
  have hunram : UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) := by
    refine ⟨Ideal.IsIntegral.comap_ne_bot _ hPbot, fun 𝔔 h𝔔max h𝔔lo ↦ ?_⟩
    haveI := h𝔔max.isPrime
    have h𝔔eq : 𝔔 = 𝔓 := eq_of_liesOver_under_E_of_frobenius σ 𝔓 hunrK inferInstance hfrob
      horderE 𝔔 h𝔔lo
    subst h𝔔eq
    exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot).mpr hraE
  haveI hPPE : 𝔓.LiesOver (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
    Ideal.over_under (A := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) (P := 𝔓)
  refine ⟨inferInstance, hunram, ?_, ?_⟩
  · rw [frobeniusClass_eq_mk_of_isArithFrobAt
      (↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
      L (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) hunram _ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
        Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓) hPPE,
      ConjClasses.mk_eq_mk_iff_isConj]
    exact isConj_iff.mpr ⟨1, by simp [hfrE]⟩
  · rw [show (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).under (𝓞 K)
        = 𝔓.under (𝓞 K) from Ideal.under_under 𝔓]
    exact hinPK

/-- Planning source: FixedFieldDensity.lean:680; statement placeholder. -/
theorem frobeniusClass_under_eq_of_mem_fibre {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (_horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) [P.IsPrime]
    (hunrP : UnramifiedIn K L (P.under (𝓞 K)))
    (hPunr : UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P)
    (hPfrob : frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
      = ConjClasses.mk σE)
    (hPdeg : (P.under (𝓞 K)).inertiaDeg P = 1) (hPbot : P ≠ ⊥) :
    frobeniusClass K L (P.under (𝓞 K)) = ConjClasses.mk σ := by
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  obtain ⟨𝔓, h𝔓p, h𝔓lo, h𝔓bot, hPeq, hfrobK⟩ :=
    exists_arithFrobAt_over_fibrePrime σ σE hσE P hunrP hPunr hPfrob hPdeg hPbot
  haveI := h𝔓p
  haveI := h𝔓lo
  have hunderK : P.under (𝓞 K) = 𝔓.under (𝓞 K) := by
    rw [← hPeq, Ideal.under_under]
  have hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)) := hunderK ▸ hunrP
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  rw [hunderK,
    frobeniusClass_eq_mk_of_isArithFrobAt K L (𝔓.under (𝓞 K)) hunrK _ 𝔓 hfrobK inferInstance]

/-- Planning source: FixedFieldDensity.lean:615; statement placeholder. -/
theorem card_fibre_E_eq_card_fibre_L
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (_hCfrob : frobeniusClass K L 𝔭 = ConjClasses.mk σ) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
        P ∈ {P | P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
              ∧ frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
                = ConjClasses.mk σE
              ∧ (P.under (𝓞 K)).inertiaDeg P = 1} ∧ P.LiesOver 𝔭 ∧ P ≠ ⊥}
      = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
          IsArithFrobAt (𝓞 K) σ 𝔓} := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  refine (Nat.card_congr (Equiv.ofBijective
      (fun 𝔓 ↦ ⟨𝔓.1.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))),
        by obtain ⟨_, hP, hPbot, hfrob⟩ := 𝔓.2
           haveI := hP
           refine ⟨under_E_mem_fibre_of_isArithFrobAt σ σE hσE horderE 𝔭 hunr 𝔓.1 hP hPbot hfrob,
             ?_, Ideal.IsIntegral.comap_ne_bot _ hPbot⟩
           haveI : (𝔓.1.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).LiesOver
               (𝔓.1.under (𝓞 K)) := inferInstance
           rwa [← hP.over] at this⟩)
      ⟨?_, ?_⟩)).symm
  · rintro ⟨𝔓₁, h𝔓₁, hP₁, hP₁bot, hfrob₁⟩ ⟨𝔓₂, h𝔓₂, hP₂, hP₂bot, hfrob₂⟩ hΦ
    haveI := h𝔓₁
    haveI := h𝔓₂
    haveI := hP₁
    haveI := hP₂
    have hunderK₁ : 𝔓₁.under (𝓞 K) = 𝔭 := hP₁.over.symm
    have hunrK₁ : UnramifiedIn K L (𝔓₁.under (𝓞 K)) := hunderK₁ ▸ hunr
    haveI : 𝔓₁.LiesOver (𝔓₁.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓₁)
    have hΦ' : 𝔓₂.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
        = 𝔓₁.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) :=
      congrArg Subtype.val hΦ |>.symm
    haveI hP₂lo : 𝔓₂.LiesOver
        (𝔓₁.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) := by
      haveI : 𝔓₂.LiesOver
        (𝔓₂.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
        Ideal.over_under (A := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) (P := 𝔓₂)
      rwa [hΦ'] at this
    exact Subtype.ext (eq_of_liesOver_under_E_of_frobenius σ 𝔓₁ hunrK₁ inferInstance hfrob₁
      horderE 𝔓₂ hP₂lo).symm
  · rintro ⟨P, ⟨hPp, hPunr, hPfrob, hPdeg⟩, hPlo, hPbot⟩
    haveI := hPp
    haveI := hPlo
    have hunrP : UnramifiedIn K L (P.under (𝓞 K)) := hPlo.over.symm ▸ hunr
    obtain ⟨𝔓, h𝔓p, h𝔓lo, h𝔓bot, hPeq, hfrobK⟩ :=
      exists_arithFrobAt_over_fibrePrime σ σE hσE P hunrP hPunr hPfrob hPdeg hPbot
    haveI := h𝔓p
    haveI := h𝔓lo
    have hunderK : 𝔓.under (𝓞 K) = 𝔭 := by
      rw [← Ideal.under_under (B := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) 𝔓,
        hPeq]
      exact hPlo.over.symm
    haveI hPK𝔓 : 𝔓.LiesOver 𝔭 := hunderK ▸ Ideal.over_under (A := 𝓞 K) (P := 𝔓)
    exact ⟨⟨𝔓, h𝔓p, hPK𝔓, h𝔓bot, hfrobK⟩, Subtype.ext hPeq⟩

/-- Planning source: FixedFieldDensity.lean:712; statement placeholder. -/
theorem tsum_comp_eq_card_fibre_smul {β γ D : Type*}
    [DivisionRing D] [UniformSpace D] [IsUniformAddGroup D]
    [CompleteSpace D] [T2Space D] [IsTopologicalRing D]
    (g : β → γ) (h : γ → D) (c : D)
    (hsumm : Summable fun b ↦ h (g b))
    (hcard : ∀ y, (Nat.card (g ⁻¹' {y} : Set β) : D) = c) :
    ∑' b, h (g b) = c * ∑' y, h y := by
  rw [← (hsumm.hasSum.tsum_fiberwise g).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun y ↦ ?_
  rw [tsum_congr fun b : (g ⁻¹' {y} : Set β) ↦ congrArg h b.2, tsum_const, nsmul_eq_mul, hcard]

/-- Planning source: FixedFieldDensity.lean:727; statement placeholder. -/
theorem card_fibre_T1_over_prime {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr𝔭 : UnramifiedIn K L 𝔭)
    (hfrob𝔭 : frobeniusClass K L 𝔭 = ConjClasses.mk σ) :
    (orderOf σ * Nat.card (ConjClasses.mk σ).carrier) *
        Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
          P ∈ {P | P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
                ∧ frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
                  = ConjClasses.mk σE ∧ (P.under (𝓞 K)).inertiaDeg P = 1}
            ∧ P.LiesOver 𝔭 ∧ P ≠ ⊥}
      = Nat.card Gal(L/K) := by
  rw [card_fibre_E_eq_card_fibre_L K L σ σE hσE horderE 𝔭 hunr𝔭 hfrob𝔭, mul_comm, ← mul_assoc]
  exact count_primes_above_with_frobenius_eq_sigma K L σ (ConjClasses.mk σ) rfl 𝔭 hunr𝔭 hfrob𝔭

/-- Planning source: FixedFieldDensity.lean:755; statement placeholder. -/
theorem primeIdealZetaSum_fibre_eq_smul
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    {s : ℝ} (hs : 1 < s) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    primeIdealZetaSum
        {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
          P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
          frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
            = ConjClasses.mk σE ∧ (P.under (𝓞 K)).inertiaDeg P = 1 ∧
          UnramifiedIn K L (P.under (𝓞 K))} s
      = ((Nat.card Gal(L/K) : ℝ) / (orderOf σ * Nat.card (ConjClasses.mk σ).carrier))
        * primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
            frobeniusClass K L 𝔭 = ConjClasses.mk σ} s := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  set Sset := {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
    frobeniusClass K L 𝔭 = ConjClasses.mk σ} with hSset
  set T₁set := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
    frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P = ConjClasses.mk σE ∧
    (P.under (𝓞 K)).inertiaDeg P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))} with hT₁set
  set S' := {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ Sset ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} with hS'
  have hgmem : ∀ P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥},
      P.1.under (𝓞 K) ∈ Sset ∧ (P.1.under (𝓞 K)).IsPrime ∧ P.1.under (𝓞 K) ≠ ⊥ := by
    rintro ⟨P, ⟨hPp, hPunr, hPfrob, hPdeg, hunrP⟩, _, hPbot⟩
    haveI := hPp
    refine ⟨⟨inferInstance, hunrP, ?_⟩, inferInstance, UnramifiedIn.ne_bot K L hunrP⟩
    exact frobeniusClass_under_eq_of_mem_fibre σ σE hσE horderE P hunrP hPunr hPfrob hPdeg hPbot
  set g : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} → S' :=
    fun P ↦ ⟨P.1.under (𝓞 K), hgmem P⟩ with hg
  have hnormeq : ∀ P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥},
      (Ideal.absNorm P.1 : ℝ) = (Ideal.absNorm (P.1.under (𝓞 K)) : ℝ) := by
    rintro ⟨P, ⟨hPp, _, _, hPdeg, _⟩, _, hPbot⟩
    haveI := hPp
    have hpbot : P.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
    haveI : P.LiesOver (P.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := P)
    have hpow := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P (P.under (𝓞 K)) inferInstance hpbot
    rw [hPdeg, pow_one] at hpow
    rw [hpow]
  have hcardfib : ∀ 𝔭 : S', (orderOf σ * Nat.card (ConjClasses.mk σ).carrier) *
      Nat.card {P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} // g P = 𝔭} = Nat.card Gal(L/K) := by
    intro 𝔭
    obtain ⟨hp𝔭, hunr𝔭, hfrob𝔭⟩ := 𝔭.2.1
    haveI := hp𝔭
    have hreindex : Nat.card {P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} // g P = 𝔭}
        = Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
            P ∈ {P | P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
                  L P ∧ frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
                  = ConjClasses.mk σE ∧ (P.under (𝓞 K)).inertiaDeg P = 1}
              ∧ P.LiesOver 𝔭.1 ∧ P ≠ ⊥} := by
      refine Nat.card_congr ⟨fun x ↦ ⟨x.1.1, ?_, ?_, x.1.2.2.2⟩,
        fun y ↦ ⟨⟨y.1, ?_, y.2.1.1, y.2.2.2⟩, ?_⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
      · exact ⟨x.1.2.1.1, x.1.2.1.2.1, x.1.2.1.2.2.1, x.1.2.1.2.2.2.1⟩
      · exact ⟨(congrArg Subtype.val x.2).symm ▸ (Ideal.over_under (A := 𝓞 K) (P := x.1.1)).over⟩
      · haveI := y.2.1.1
        have hunderK : y.1.under (𝓞 K) = 𝔭.1 := (y.2.2.1).over.symm
        exact ⟨y.2.1.1, y.2.1.2.1, y.2.1.2.2.1, y.2.1.2.2.2, by rw [hunderK]; exact hunr𝔭⟩
      · exact Subtype.ext (y.2.2.1).over.symm
    rw [hreindex]
    exact card_fibre_T1_over_prime σ σE hσE horderE 𝔭.1 hunr𝔭 hfrob𝔭
  have hordC_pos : (0 : ℝ) < orderOf σ * Nat.card (ConjClasses.mk σ).carrier := by
    have h₁ : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
    have : Nonempty (ConjClasses.mk σ).carrier := ⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩
    have h₂ : 0 < Nat.card (ConjClasses.mk σ).carrier := Nat.card_pos
    positivity
  set h : S' → ℝ := fun 𝔭 ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) with hh
  have hequivfib : ∀ 𝔭 : S', (g ⁻¹' {𝔭} : Set _) ≃
      {P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} // g P = 𝔭} :=
    fun 𝔭 ↦ Equiv.subtypeEquivRight fun _ ↦ Iff.rfl
  have hcard : ∀ 𝔭 : S', (Nat.card (g ⁻¹' {𝔭} : Set _) : ℝ)
      = (Nat.card Gal(L/K) : ℝ) / (orderOf σ * Nat.card (ConjClasses.mk σ).carrier) := by
    intro 𝔭
    rw [Nat.card_congr (hequivfib 𝔭), eq_div_iff hordC_pos.ne', mul_comm, ← hcardfib 𝔭]
    push_cast
    ring
  rw [primeIdealZetaSum_def (↥(IntermediateField.fixedField (Subgroup.zpowers σ))),
    primeIdealZetaSum_def K,
    tsum_congr (fun P ↦ congrArg (· ^ (-s)) (hnormeq P)),
    show (fun P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} ↦
      (Ideal.absNorm (P.1.under (𝓞 K)) : ℝ) ^ (-s)) = (fun P ↦ h (g P)) from rfl]
  exact tsum_comp_eq_card_fibre_smul g h _
    ((summable_prime_absNorm_rpow _ T₁set hs).congr fun P ↦ congrArg (· ^ (-s)) (hnormeq P))
    hcard

/-- The finite constant-fibre sum inside FixedFieldDensity.lean:886–889. -/
theorem ennreal_tsum_const_finite {α : Type*} [Finite α] (c : ℝ≥0∞) :
    ∑' _ : α, c = (Nat.card α : ℝ≥0∞) * c := by
  haveI := Fintype.ofFinite α
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- Planning source: FixedFieldDensity.lean:877; statement placeholder. -/
theorem tsum_comp_le_card_fibre_mul {β γ : Type*} (g : β → γ) (f : γ → ℝ≥0∞) (d : ℕ)
    (hfin : ∀ y, Finite (g ⁻¹' {y} : Set β)) (hfib : ∀ y, Nat.card (g ⁻¹' {y} : Set β) ≤ d) :
    ∑' b, f (g b) ≤ (d : ℝ≥0∞) * ∑' y, f y := by
  rw [← ENNReal.tsum_fiberwise (fun b ↦ f (g b)) g, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun y ↦ ?_)
  rw [tsum_congr (fun b : (g ⁻¹' {y} : Set β) ↦ by rw [b.2])]
  haveI := hfin y
  letI := Fintype.ofFinite (g ⁻¹' {y} : Set β)
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  gcongr
  exact_mod_cast hfib y

/-- Planning source: FixedFieldDensity.lean:892; statement placeholder. -/
theorem tsum_real_comp_le_card_fibre_mul {β γ : Type*} (g : β → γ) (FA : β → ℝ)
    (FK : γ → ℝ) (d : ℕ) (hsummA : Summable FA) (hsummK : Summable FK) (hnonnegA : ∀ b, 0 ≤ FA b)
    (hnonnegK : ∀ y, 0 ≤ FK y) (hterm : ∀ b, FA b ≤ FK (g b))
    (hfin : ∀ y, Finite (g ⁻¹' {y} : Set β)) (hfib : ∀ y, Nat.card (g ⁻¹' {y} : Set β) ≤ d) :
    ∑' b, FA b ≤ (d : ℝ) * ∑' y, FK y := by
  have hchain : ∑' b, ENNReal.ofReal (FA b)
      ≤ (d : ℝ≥0∞) * ∑' y, ENNReal.ofReal (FK y) :=
    calc ∑' b, ENNReal.ofReal (FA b) ≤ ∑' b, ENNReal.ofReal (FK (g b)) :=
          ENNReal.tsum_le_tsum fun b ↦ ENNReal.ofReal_le_ofReal (hterm b)
      _ ≤ (d : ℝ≥0∞) * ∑' y, ENNReal.ofReal (FK y) :=
          tsum_comp_le_card_fibre_mul g (ENNReal.ofReal <| FK ·) d hfin hfib
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonnegA hsummA,
    ← ENNReal.ofReal_tsum_of_nonneg hnonnegK hsummK] at hchain
  rw [← ENNReal.toReal_ofReal (tsum_nonneg hnonnegA),
    ← ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg d) (tsum_nonneg hnonnegK)),
    ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hchain

/-- Planning source: FixedFieldDensity.lean:914; statement placeholder. -/
theorem absNorm_rpow_neg_le_under_sq {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] (σ : Gal(L/K))
    (P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) [P.IsPrime]
    (hPb : P ≠ ⊥) {s : ℝ} (hs : 1 < s) (hdeg : 2 ≤ (P.under (𝓞 K)).inertiaDeg P) :
    (Ideal.absNorm P : ℝ) ^ (-s) ≤ (Ideal.absNorm (P.under (𝓞 K)) : ℝ) ^ (-(2 : ℝ)) := by
  have hppr : (P.under (𝓞 K)).IsPrime := inferInstance
  have hpbot : P.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb
  haveI : P.LiesOver (P.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := P)
  have hpow := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P (P.under (𝓞 K)) hppr hpbot
  have hn2 : 2 ≤ Ideal.absNorm (P.under (𝓞 K)) := by
    have h0 : Ideal.absNorm (P.under (𝓞 K)) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hpbot
    have h1 : Ideal.absNorm (P.under (𝓞 K)) ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr hppr.ne_top
    omega
  rw [hpow, Nat.cast_pow,
    ← Real.rpow_natCast (Ideal.absNorm (P.under (𝓞 K)) : ℝ) ((P.under (𝓞 K)).inertiaDeg P),
    ← Real.rpow_mul (by positivity)]
  refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_of_lt hn2) ?_
  nlinarith [mul_le_mul (show (2 : ℝ) ≤ ((P.under (𝓞 K)).inertiaDeg P : ℝ) by exact_mod_cast hdeg)
    hs.le (by norm_num) (by positivity : (0 : ℝ) ≤ ((P.under (𝓞 K)).inertiaDeg P : ℝ))]

/-- Planning source: FixedFieldDensity.lean:936; statement placeholder. -/
theorem card_primesOver_le_finrank {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (σ : Gal(L/K))
    [NoZeroSMulDivisors (𝓞 K) (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥) :
    Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
        P.IsPrime ∧ P.LiesOver 𝔭}
      ≤ Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) := by
  letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  rw [show {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
        P.IsPrime ∧ P.LiesOver 𝔭}
      = ↥(𝔭.primesOver (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) from rfl,
    Nat.card_coe_set_eq, ← IsDedekindDomain.coe_primesOverFinset h𝔭, Set.ncard_coe_finset]
  exact Ideal.card_primesOverFinset_le_finrank (R := 𝓞 K)
    (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
    (K := K) (L := ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) h𝔭

-- `[IsGalois K L]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Planning source: FixedFieldDensity.lean:958; statement placeholder. -/
theorem primeIdealZetaSum_degTwo_le (σ : Gal(L/K)) {s : ℝ}
    (hs : 1 < s) (Aset : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))))
    (hA : Aset = {P | P.IsPrime ∧ P ≠ ⊥ ∧
      UnramifiedIn K L (P.under (𝓞 K)) ∧ 2 ≤ (P.under (𝓞 K)).inertiaDeg P}) :
    primeIdealZetaSum Aset s
      ≤ (Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) : ℝ)
        * primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) 2 := by
  letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : NoZeroSMulDivisors (𝓞 K)
      (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) :=
    ⟨fun {c x} h ↦ by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp (fun h ↦ RingOfIntegers.algebraMap.injective K _ (by rwa [map_zero])) id⟩
  set AP := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
    P ∈ Aset ∧ P.IsPrime ∧ P ≠ ⊥} with hAP
  set KP := {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (univ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} with hKP
  have hunder : ∀ P : AP, (P.1.under (𝓞 K)).IsPrime ∧ P.1.under (𝓞 K) ≠ ⊥ := by
    rintro ⟨P, hPA, hPp, hPb⟩
    haveI := hPp
    exact ⟨inferInstance, Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb⟩
  set g : AP → KP := fun P ↦ ⟨P.1.under (𝓞 K), mem_univ _, (hunder P).1, (hunder P).2⟩ with hg
  have hterm : ∀ P : AP, (Ideal.absNorm P.1 : ℝ) ^ (-s)
      ≤ (Ideal.absNorm (g P).1 : ℝ) ^ (-(2 : ℝ)) := by
    rintro ⟨P, hPA, hPp, hPb⟩
    haveI := hPp
    rw [hA] at hPA
    exact absNorm_rpow_neg_le_under_sq σ P hPb hs hPA.2.2.2
  have hinj : ∀ 𝔭 : KP, Finite (g ⁻¹' {𝔭} : Set AP) ∧
      Nat.card (g ⁻¹' {𝔭} : Set AP)
        ≤ Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) := by
    intro 𝔭
    haveI := 𝔭.2.2.1
    haveI : 𝔭.1.IsMaximal := 𝔭.2.2.1.isMaximal 𝔭.2.2.2
    have hmem : ∀ P : (g ⁻¹' {𝔭} : Set AP), P.1.1.IsPrime ∧ P.1.1.LiesOver 𝔭.1 := by
      rintro ⟨⟨P, hPA, hPp, hPb⟩, hgP⟩
      haveI := hPp
      exact ⟨hPp, ⟨(congrArg Subtype.val hgP : P.under (𝓞 K) = 𝔭.1) ▸
        (Ideal.over_under (A := 𝓞 K) (P := P)).over⟩⟩
    set hmap : (g ⁻¹' {𝔭} : Set AP) → {P : Ideal (𝓞 ↥(IntermediateField.fixedField
        (Subgroup.zpowers σ))) // P.IsPrime ∧ P.LiesOver 𝔭.1} := fun P ↦ ⟨P.1.1, hmem P⟩ with hhmap
    have hmapinj : Function.Injective hmap := by
      rintro ⟨⟨P, hP⟩, hgP⟩ ⟨⟨Q, hQ⟩, hgQ⟩ hPQ
      exact Subtype.ext (Subtype.ext (by simpa only [hhmap, Subtype.mk.injEq] using hPQ))
    haveI : Finite {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
        P.IsPrime ∧ P.LiesOver 𝔭.1} :=
      (IsDedekindDomain.primesOver_finite 𝔭.1 _).to_subtype
    exact ⟨Finite.of_injective hmap hmapinj, (Nat.card_le_card_of_injective hmap hmapinj).trans
      (card_primesOver_le_finrank σ 𝔭.1 𝔭.2.2.2)⟩
  rw [primeIdealZetaSum_def (↥(IntermediateField.fixedField (Subgroup.zpowers σ))),
    primeIdealZetaSum_def K]
  exact tsum_real_comp_le_card_fibre_mul g _ _ _ (summable_prime_absNorm_rpow _ Aset (by linarith))
    (summable_prime_absNorm_rpow K (univ : Set (Ideal (𝓞 K))) (by norm_num))
    (fun _ ↦ by positivity)
    (fun _ ↦ by positivity) hterm (fun 𝔭 ↦ (hinj 𝔭).1) (fun 𝔭 ↦ (hinj 𝔭).2)

-- `[IsGalois K L]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Planning source: FixedFieldDensity.lean:1016; statement placeholder. -/
theorem ramifiedBelow_finite (σ : Gal(L/K))
    (Bset : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))))
    (hB : Bset = {P | P.IsPrime ∧ P ≠ ⊥ ∧ ¬ UnramifiedIn K L (P.under (𝓞 K))}) :
    Bset.Finite := by
  apply Set.Finite.subset ((finite_ramifiedIn K L).biUnion (t := fun 𝔭 ↦
    (𝔭.primesOver (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))) ?_)
  · rw [hB]
    rintro P ⟨hPp, hPb, hPnu⟩
    haveI := hPp
    exact Set.mem_biUnion ⟨inferInstance, Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb, hPnu⟩
      ⟨hPp, Ideal.over_under (A := 𝓞 K) (P := P)⟩
  · rintro 𝔭 ⟨hp, hb, -⟩
    haveI := hp
    haveI : 𝔭.IsMaximal := hp.isMaximal hb
    exact IsDedekindDomain.primesOver_finite 𝔭 _

/-- Planning source: FixedFieldDensity.lean:1042; statement placeholder. -/
theorem primeIdealZetaSum_T2_div_univ_tendsto_zero
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (T₂set : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))))
    (hT₂ : T₂set = {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
        P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
        frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
          = ConjClasses.mk σE} \
      {P ∈ {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
          P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
          frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
            = ConjClasses.mk σE} |
        (P.under (𝓞 K)).inertiaDeg P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))}) :
    Tendsto (fun s : ℝ ↦ primeIdealZetaSum T₂set s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
        (Subgroup.zpowers σ))))) s) (𝓝[>] 1) (𝓝 0) := by
  haveI : IsGalois ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    IsGalois.tower_top_intermediateField _
  set Aset := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ P ≠ ⊥ ∧ UnramifiedIn K L (P.under (𝓞 K)) ∧
    2 ≤ (P.under (𝓞 K)).inertiaDeg P} with hAdef
  set Bset := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ P ≠ ⊥ ∧ ¬ UnramifiedIn K L (P.under (𝓞 K))} with hBdef
  have hsub : T₂set ⊆ Aset ∪ Bset := by
    rw [hT₂]
    rintro P ⟨⟨hPp, hPunr, hPfr⟩, hPnotT1⟩
    haveI := hPp
    simp only [Set.mem_setOf_eq, not_and] at hPnotT1
    have hPb : P ≠ ⊥ := UnramifiedIn.ne_bot _ L hPunr
    by_cases hunrK : UnramifiedIn K L (P.under (𝓞 K))
    · refine Or.inl ⟨hPp, hPb, hunrK, ?_⟩
      have hdegne : (P.under (𝓞 K)).inertiaDeg P ≠ 1 := fun hdeg1 ↦
        hPnotT1 ⟨hPp, hPunr, hPfr⟩ hdeg1 hunrK
      have hppr : (P.under (𝓞 K)).IsPrime := inferInstance
      haveI : (P.under (𝓞 K)).IsMaximal :=
        hppr.isMaximal (Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb)
      haveI : P.LiesOver (P.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := P)
      have hpos : 0 < (P.under (𝓞 K)).inertiaDeg P := Ideal.inertiaDeg_pos' _ _
      omega
    · exact Or.inr ⟨hPp, hPb, hunrK⟩
  have hdisj : Disjoint Aset Bset := by
    rw [Set.disjoint_left]
    rintro P ⟨-, -, hunrK, -⟩ ⟨-, -, hnunrK⟩
    exact hnunrK hunrK
  have hBfin : Bset.Finite := ramifiedBelow_finite K L σ Bset hBdef
  refine tendsto_primeIdealZetaSum_div_univ_zero_of_le_const
    (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) T₂set
    ((Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) : ℝ)
        * primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) 2
      + (Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
          P ∈ Bset ∧ P.IsPrime ∧ P ≠ ⊥} : ℝ)) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  calc primeIdealZetaSum T₂set s ≤ primeIdealZetaSum (Aset ∪ Bset) s :=
        primeIdealZetaSum_le_of_subset (↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
          hsub hs
    _ = primeIdealZetaSum Aset s + primeIdealZetaSum Bset s :=
        primeIdealZetaSum_union_of_disjoint (↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
          hdisj hs
    _ ≤ _ := add_le_add (primeIdealZetaSum_degTwo_le K L σ hs Aset hAdef)
        (primeIdealZetaSum_le_card_of_finite
          (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) hBfin (by linarith))

-- `[IsGalois K L]` comes from the section `variable`; the planned signature keeps it.
set_option linter.unusedSectionVars false in
/-- Planning source: FixedFieldDensity.lean:205; statement placeholder. -/
theorem univ_ratio_E_K_tendsto_one (E : IntermediateField K L) :
    Tendsto (fun s : ℝ ↦ primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥E))) s
        / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) (𝓝[>] 1) (𝓝 1) := by
  have hcancel := (primeIdealZetaSum_univ_tendsto_log (↥E)).div
    (primeIdealZetaSum_univ_tendsto_log K) one_ne_zero
  rw [one_div_one] at hcancel
  refine hcancel.congr' ?_
  filter_upwards [tendsto_log_one_div_sub_one_atTop.eventually_gt_atTop 0] with s hs
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hs.ne']

/-- Planning source: FixedFieldDensity.lean:1106; statement placeholder. -/
theorem isMulCommutative_galGroup_fixedField {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] (σ : Gal(L/K)) :
    IsMulCommutative Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
  .of_comm fun a b ↦ by
    obtain ⟨x, rfl⟩ := (IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)).surjective a
    obtain ⟨y, rfl⟩ := (IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)).surjective b
    rw [← map_mul _ x y, ← map_mul _ y x, mul_comm' x y]

/-- Planning source: FixedFieldDensity.lean:1116; statement placeholder. -/
theorem card_galGroup_fixedField_eq_orderOf {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L]
    [Algebra K L] (σ : Gal(L/K)) :
    Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) = orderOf σ := by
  rw [← Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)).toEquiv,
    Nat.card_zpowers]

/-- Planning source: FixedFieldDensity.lean:1139; statement placeholder. -/
theorem density_lift_through_fixedField
    (σ : Gal(L/K)) (E : IntermediateField K L) (σE : Gal(L/E))
    (hσE : letI : IsScalarTower K ↥E L := E.isScalarTower_mid'; σE.restrictScalars K = σ)
    (_hEfix : E = IntermediateField.fixedField (Subgroup.zpowers σ))
    (_hab : HasDirichletDensity
        {P : Ideal (𝓞 ↥E) | P.IsPrime ∧ UnramifiedIn ↥E L P ∧
          frobeniusClass ↥E L P = ConjClasses.mk σE}
        ((Nat.card Gal(L/E) : ℝ)⁻¹)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card Gal(L/K)) := by
  subst _hEfix
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsMulCommutative Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
    isMulCommutative_galGroup_fixedField σ
  have horderE' :
      orderOf σ = Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
    (card_galGroup_fixedField_eq_orderOf σ).symm
  set Tset := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
    frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
      = ConjClasses.mk σE} with hTset
  set T₁set := {P ∈ Tset | (P.under (𝓞 K)).inertiaDeg P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))}
    with hT₁set
  set T₂set := Tset \ T₁set with hT₂set
  have hT₁sub : T₁set ⊆ Tset := fun x hx ↦ hx.1
  have hsplit : ∀ {s : ℝ}, 1 < s → primeIdealZetaSum Tset s
      = primeIdealZetaSum T₁set s + primeIdealZetaSum T₂set s := by
    intro s hs
    rw [(Set.union_diff_cancel hT₁sub).symm,
      primeIdealZetaSum_union_of_disjoint (↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
        Set.disjoint_sdiff_right hs]
  have hleafB : Tendsto (fun s : ℝ ↦ primeIdealZetaSum T₂set s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
        (Subgroup.zpowers σ))))) s) (𝓝[>] 1) (𝓝 0) :=
    primeIdealZetaSum_T2_div_univ_tendsto_zero K L σ σE T₂set hT₂set
  have htendT₁ : Tendsto (fun s : ℝ ↦ primeIdealZetaSum T₁set s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
        (Subgroup.zpowers σ))))) s) (𝓝[>] 1)
      (𝓝 ((Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ)⁻¹)) := by
    have := _hab.sub hleafB
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [mem_Ioi] at hs
    rw [hsplit hs]
    ring
  rw [HasDirichletDensity]
  have hmain : Tendsto
      (fun s : ℝ ↦ ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * (primeIdealZetaSum T₁set s
              / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
                (Subgroup.zpowers σ))))) s)
          * (primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
              (Subgroup.zpowers σ))))) s
              / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s))
      (𝓝[>] 1)
      (𝓝 (((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * (Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ)⁻¹ * 1)) :=
    ((htendT₁.const_mul _).mul (univ_ratio_E_K_tendsto_one K L _))
  have hval : ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * (Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ)⁻¹ * 1
      = (Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card Gal(L/K) := by
    have hordpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
    rw [← horderE', mul_one]
    field_simp
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    (primeIdealZetaSum_univ_tendsto_atTop (↥(IntermediateField.fixedField
      (Subgroup.zpowers σ)))).eventually_gt_atTop 0] with s hs hEpos
  simp only [mem_Ioi] at hs
  have hT₁flat : T₁set = {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
      P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
      frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P = ConjClasses.mk σE ∧
      (P.under (𝓞 K)).inertiaDeg P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))} := by
    rw [hT₁set, hTset]
    ext P
    simp only [Set.mem_setOf_eq]
    tauto
  have hleafA := primeIdealZetaSum_fibre_eq_smul K L σ σE hσE horderE' hs
  rw [← hT₁flat] at hleafA
  have hc_pos : (0 : ℝ) < orderOf σ * Nat.card (ConjClasses.mk σ).carrier := by
    have h₁ : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
    have : Nonempty (ConjClasses.mk σ).carrier := ⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩
    have h₂ : 0 < Nat.card (ConjClasses.mk σ).carrier := Nat.card_pos
    positivity
  have hG_pos : (0 : ℝ) < Nat.card Gal(L/K) := by exact_mod_cast Nat.card_pos
  have hAB : ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
      * ((Nat.card Gal(L/K) : ℝ) / (orderOf σ * Nat.card (ConjClasses.mk σ).carrier)) = 1 := by
    rw [div_mul_div_comm, mul_comm ((orderOf σ : ℝ) * _), div_self (by positivity)]
  have hSeq : primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
      = ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * primeIdealZetaSum T₁set s := by
    rw [hleafA, ← mul_assoc, hAB, one_mul]
  rw [hSeq, mul_assoc ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K)),
    div_mul_div_cancel₀ hEpos.ne']
  ring

end Cox.Chebotarev
