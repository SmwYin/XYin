/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevFrobenius
import XYin.PhD.Cox.Theorem11_1.ChebotarevDensity
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-! # Coprime Frobenius generation
Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87`.
-/
noncomputable section
open NumberField Filter Topology Set
open scoped Pointwise
namespace Cox.Chebotarev

/-- Planning source: Frobenius.lean:369; ideal-count child. -/
theorem exists_prime_dvd_natCast_mem (K : Type*) [Field K]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (n : ℕ) (hn1 : 1 < n) (hmem : (n : 𝓞 K) ∈ 𝔭) :
    ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ (r : 𝓞 K) ∈ 𝔭 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨r, hr, k, rfl⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    have hkpos : 0 < k := Nat.pos_of_ne_zero <| by rintro rfl; simp at hn1
    have hcast : ((r * k : ℕ) : 𝓞 K) = (r : 𝓞 K) * (k : 𝓞 K) := by push_cast; ring
    rw [hcast] at hmem
    rcases ‹𝔭.IsPrime›.mem_or_mem hmem with hrm | hkm
    · exact ⟨r, hr, ⟨k, rfl⟩, hrm⟩
    · by_cases hk1 : k = 1
      · subst hk1
        simp only [Nat.cast_one] at hkm
        exact absurd (Ideal.eq_top_of_isUnit_mem _ hkm isUnit_one) ‹𝔭.IsPrime›.ne_top
      · have hklt : k < r * k := (Nat.lt_mul_iff_one_lt_left hkpos).mpr hr.one_lt
        obtain ⟨s, hs, hsdvd, hsm⟩ := ih k hklt (by omega) hkm
        exact ⟨s, hs, hsdvd.trans ⟨r, by ring⟩, hsm⟩

/-- Planning source: Frobenius.lean:391; ideal-count child. -/
theorem exists_primeFactor_natCast_mem_of_not_coprime (K : Type*) [Field K] [NumberField K] (m : ℕ)
    [NeZero m] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥)
    (hncop : ¬ (Ideal.absNorm 𝔭).Coprime m) :
    ∃ p ∈ m.primeFactors, (p : 𝓞 K) ∈ 𝔭 := by
  have hN0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ h𝔭 (Ideal.absNorm_eq_zero_iff.mp h)
  have hN1' : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ ‹𝔭.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  obtain ⟨r, hr, hrdvd, hrm⟩ :=
    exists_prime_dvd_natCast_mem K 𝔭 _ (by omega) (Ideal.absNorm_mem 𝔭)
  have hNdvd : Ideal.absNorm 𝔭 ∣ r ^ Module.finrank ℤ (𝓞 K) := by
    have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hrm)
    rwa [Ideal.absNorm_span_singleton, show ((r : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (r : ℤ) by
        push_cast; rfl, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (hncop : Nat.gcd (Ideal.absNorm 𝔭) m ≠ 1)
  have hpr : p ∣ r ^ Module.finrank ℤ (𝓞 K) := (hpdvd.trans (Nat.gcd_dvd_left _ _)).trans hNdvd
  have hpeqr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpr)
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), NeZero.ne m⟩,
    hpeqr ▸ hrm⟩

/-- Planning source: Frobenius.lean:412; ideal-count child. -/
theorem finite_primes_natCast_mem (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p ≠ 0) :
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (p : 𝓞 K) ∈ 𝔭}.Finite := by
  classical
  have hspan : (Ideal.span {(p : 𝓞 K)}) ≠ 0 := by
    simp only [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  have hfin := Ideal.finite_factors (R := 𝓞 K) hspan
  apply Set.Finite.ofFinset (hfin.toFinset.image (·.asIdeal))
  intro 𝔭
  simp only [Set.Finite.mem_toFinset, Finset.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, v.ne_bot, (Ideal.dvd_iff_le.mp hv) (Ideal.mem_span_singleton_self _)⟩
  · rintro ⟨hprime, hne, hmem⟩
    exact ⟨⟨𝔭, hprime, hne⟩, Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem),
      rfl⟩

/-- Planning source: Frobenius.lean:431; ideal-count child. -/
theorem finite_badPrimes (K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m] :
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Ideal.absNorm 𝔭).Coprime m}.Finite := by
  classical
  refine Set.Finite.subset
    (Set.Finite.biUnion (s := (↑m.primeFactors : Set ℕ)) (Set.toFinite _) fun p _ ↦
      finite_primes_natCast_mem K p ?_) ?_
  · exact Nat.pos_of_mem_primeFactors (by assumption) |>.ne'
  · rintro 𝔭 ⟨hprime, hne, hncop⟩
    have := hprime
    obtain ⟨p, hp, hpmem⟩ := exists_primeFactor_natCast_mem_of_not_coprime K m 𝔭 hne hncop
    exact Set.mem_biUnion hp ⟨hprime, hne, hpmem⟩

/-- Planning source: CyclotomicNormResidue.lean:51; ideal-count child. -/
theorem cyclotomic_frobenius_acts_as_norm_power
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (𝔭 : Ideal (𝓞 K))
    [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) :
    haveI : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 hP
    ∀ ζ : L, ζ ∈ primitiveRoots m L →
      arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ζ = ζ ^ Ideal.absNorm 𝔭 := by
  haveI : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 hP
  intro ζ hζmem
  set φ := arithFrobAt (𝓞 K) Gal(L/K) 𝔓
  have hζ : IsPrimitiveRoot ζ m := (mem_primitiveRoots (NeZero.pos m)).mp hζmem
  set z : 𝓞 L := ⟨ζ, hζ.isIntegral (NeZero.pos m)⟩
  have hzc : (algebraMap (𝓞 L) L) z = ζ := rfl
  have hzpow : z ^ m = 1 := RingOfIntegers.ext (by simpa using hζ.pow_eq_one)
  set q := Ideal.absNorm 𝔭
  have h𝔭ne : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L hunr
  have hcopP : (Ideal.absNorm 𝔓).Coprime m := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓 𝔭 ‹𝔭.IsPrime› h𝔭ne]
    exact Nat.Coprime.pow_left _ hcop
  have hN1 : Ideal.absNorm 𝔓 ≠ 1 := fun h ↦ ‹𝔓.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hmnotmem : (m : 𝓞 L) ∉ 𝔓 := by
    intro hmem
    have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    rw [Ideal.absNorm_span_singleton, show ((m : ℕ) : 𝓞 L) = algebraMap ℤ (𝓞 L) (m : ℤ) by
        push_cast; rfl, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
    exact hN1 ((hcopP.pow_right _).eq_one_of_dvd hd)
  have hqcard : q = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) := by
    change Ideal.absNorm 𝔭 = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))
    rw [show 𝔭 = 𝔓.under (𝓞 K) from Ideal.LiesOver.over (p := 𝔭) (P := 𝔓),
      Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have key := (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).apply_of_pow_eq_one hzpow hmnotmem
  rw [← hqcard] at key
  have hmap := congrArg (algebraMap (𝓞 L) L) key
  rwa [map_pow,
    show (algebraMap (𝓞 L) L) ((MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) φ) z) = φ ζ from rfl,
    hzc] at hmap

/-- Planning source: CyclotomicNormResidue.lean:91; ideal-count child. -/
theorem pow_natModEq_of_pow_eq {S : Type*} [CommRing S] [IsDomain S] {μ : S} {n : ℕ}
    [NeZero n] (hμ : IsPrimitiveRoot μ n) {a b : ℕ} (h : μ ^ a = μ ^ b) : a ≡ b [MOD n] :=
  hμ.eq_orderOf ▸ (hμ.isOfFinOrder (NeZero.ne n)).pow_eq_pow_iff_modEq.mp h

/-- Planning source: CyclotomicNormResidue.lean:100; ideal-count child. -/
theorem autToPow_frobeniusClass_out
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ m) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m) :
    hζ.autToPow K ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) =
      ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop := by
  obtain ⟨𝔓, h𝔓prime, h𝔓lo, _⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  haveI := h𝔓prime
  haveI := h𝔓lo
  haveI : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 h𝔓lo
  set φ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) Gal(L/K) 𝔓
  have hclass : frobeniusClass K L 𝔭 = ConjClasses.mk φ :=
    frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr φ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) h𝔓lo
  have hconj : IsConj ((frobeniusClass K L 𝔭).out) φ := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, ← hclass, ConjClasses.mk, Quotient.out_eq]
  rw [isConj_iff_eq.mp ((hζ.autToPow K).map_isConj hconj)]
  have hact : φ ζ = ζ ^ Ideal.absNorm 𝔭 :=
    cyclotomic_frobenius_acts_as_norm_power K L m 𝔭 hunr hcop 𝔓 h𝔓lo ζ
      ((mem_primitiveRoots (NeZero.pos m)).mpr hζ)
  have hspec := hζ.autToPow_spec K φ
  rw [hact] at hspec
  apply Units.ext
  rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val ((hζ.autToPow K φ : (ZMod m)ˣ) : ZMod m)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (pow_natModEq_of_pow_eq hζ hspec)

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem smul_algebraMap_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (F : IntermediateField K L) [IsGalois K F]
    (σ : L ≃ₐ[K] L) (y : 𝓞 F) :
    haveI : IsScalarTower K F L := F.isScalarTower_mid'
    σ • (algebraMap (𝓞 F) (𝓞 L) y) = algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y) := by
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  have hbridgeL : ∀ (g : L ≃ₐ[K] L) (x : 𝓞 L), ((g • x : 𝓞 L) : L) = g • (x : L) := fun g x ↦
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := L ≃ₐ[K] L) (R := 𝓞 L) (S := L) g x 1).symm
  have hbridgeF : ∀ (g : F ≃ₐ[K] F) (z : 𝓞 F), ((g • z : 𝓞 F) : F) = g • ((z : F)) := fun g z ↦
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := F ≃ₐ[K] F) (R := 𝓞 F) (S := F) g z 1).symm
  have hcoe : ∀ z : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 L) z : 𝓞 L) : L) = algebraMap F L (z : F) :=
    fun z ↦ by
      rw [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 L) L,
        RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 F) F L]
  rw [RingOfIntegers.ext_iff]
  change ((σ • algebraMap (𝓞 F) (𝓞 L) y : 𝓞 L) : L)
      = ((algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y) : 𝓞 L) : L)
  rw [hbridgeL, hcoe y, hcoe ((σ.restrictNormal F) • y), hbridgeF, AlgEquiv.smul_def,
    AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes]

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem isArithFrobAt_restrictNormal
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (F : IntermediateField K L) [IsGalois K F] (σ : L ≃ₐ[K] L)
    (𝔓 : Ideal (𝓞 L)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    haveI : IsScalarTower K F L := F.isScalarTower_mid'
    IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F)) := by
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  intro y
  rw [Ideal.under_under 𝔓, Ideal.under, Ideal.mem_comap, map_sub, map_pow,
    show (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 F) (σ.restrictNormal F)) y
        = (σ.restrictNormal F) • y from rfl, ← smul_algebraMap_eq K L F σ y]
  exact hσ (algebraMap (𝓞 F) (𝓞 L) y)

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem unramifiedIn_intermediateField
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (F : IntermediateField K L) [IsGalois K F]
    (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K L 𝔭) :
    UnramifiedIn K (↥F) 𝔭 := by
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  haveI : IsScalarTower (𝓞 K) (𝓞 F) (𝓞 L) := inferInstance
  refine ⟨hunr.1, fun 𝔮 h𝔮max h𝔮lo ↦ ?_⟩
  haveI := h𝔮lo
  haveI := h𝔮max.isPrime
  obtain ⟨𝔓, h𝔓prime, h𝔓lo, -⟩ := exists_prime_liesOver (↥F) L 𝔮
    (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔮)
  haveI := h𝔓prime
  haveI := h𝔓lo
  haveI : 𝔓.LiesOver 𝔭 := ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓, h𝔓lo.over.symm, h𝔮lo.over.symm]⟩
  haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    hunr.2 𝔓 (h𝔓prime.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)) inferInstance
  exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) 𝔮 𝔓

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem frobeniusClass_fixedField_eq_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    haveI : IsGalois K (IntermediateField.fixedField H) :=
      IsGalois.of_fixedField_normal_subgroup H
    frobeniusClass K (↥(IntermediateField.fixedField H)) 𝔭 = ConjClasses.mk 1 := by
  set F := IntermediateField.fixedField H with hF
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  obtain ⟨𝔓, h𝔓p, h𝔓lo, -⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  haveI := h𝔓p
  haveI := h𝔓lo
  haveI : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 h𝔓lo
  set σ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) Gal(L/K) 𝔓
  have hclass : frobeniusClass K L 𝔭 = ConjClasses.mk σ :=
    frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr σ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) h𝔓lo
  have hconj : IsConj σ ((frobeniusClass K L 𝔭).out) := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, hclass.symm, ConjClasses.mk, Quotient.out_eq]
  have hσeq : σ = (frobeniusClass K L 𝔭).out := by
    obtain ⟨c, hc⟩ := hconj
    rw [SemiconjBy, mul_comm' (c : Gal(L/K)) σ] at hc
    exact mul_right_cancel hc
  have hσfix : σ ∈ F.fixingSubgroup := by
    rw [hF, IntermediateField.fixingSubgroup_fixedField]
    exact hσeq ▸ hmem
  have hrestr : σ.restrictNormal F = 1 :=
    MonoidHom.mem_ker.mp <| (IntermediateField.restrictNormalHom_ker F).ge hσfix
  have h𝔮lo : (𝔓.under (𝓞 F)).LiesOver 𝔭 :=
    ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓]; exact h𝔓lo.over⟩
  haveI := h𝔮lo
  have hfrobF : IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F)) :=
    isArithFrobAt_restrictNormal K L F σ 𝔓 (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
  rw [frobeniusClass_eq_mk_of_isArithFrobAt K (↥F) 𝔭 (unramifiedIn_intermediateField K L F 𝔭 hunr)
    (σ.restrictNormal F) (𝔓.under (𝓞 F)) hfrobF h𝔮lo, hrestr]

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem finrank_residue_fixedField_eq_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    haveI : IsGalois K (IntermediateField.fixedField H) :=
      IsGalois.of_fixedField_normal_subgroup H
    haveI : NumberField (IntermediateField.fixedField H) :=
      NumberField.of_intermediateField _
    ∀ 𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 →
      Module.finrank (𝓞 K ⧸ 𝔮.under (𝓞 K)) (𝓞 ↥(IntermediateField.fixedField H) ⧸ 𝔮) = 1 := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  have hunrF : UnramifiedIn K (↥F) 𝔭 := unramifiedIn_intermediateField K L F 𝔭 hunr
  have hfc : frobeniusClass K (↥F) 𝔭 = ConjClasses.mk (1 : Gal(↥F/K)) :=
    frobeniusClass_fixedField_eq_one K L H 𝔭 hunr hmem
  intro 𝔮 h𝔮p h𝔮lo
  haveI := h𝔮p
  haveI := h𝔮lo
  rw [finrank_residue_eq_orderOf K (↥F) (1 : Gal(↥F/K)) (ConjClasses.mk 1) rfl 𝔭 hunrF hfc 𝔮
    h𝔮lo, orderOf_one]

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem card_primesOver_fixedField_eq_finrank
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    Nat.card {𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)) //
        𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} =
      Module.finrank K ↥(IntermediateField.fixedField H) := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  have hunrF : UnramifiedIn K (↥F) 𝔭 := unramifiedIn_intermediateField K L F 𝔭 hunr
  have hresdeg := finrank_residue_fixedField_eq_one K L H 𝔭 hunr hmem
  obtain ⟨𝔮₀, h𝔮₀p, h𝔮₀lo, -⟩ := exists_prime_liesOver K (↥F) 𝔭 (UnramifiedIn.ne_bot K L hunr)
  haveI := h𝔮₀p
  haveI := h𝔮₀lo
  have hcard := card_primesAbove_mul_finrank_eq K (↥F) 𝔭 hunrF 𝔮₀ h𝔮₀lo
  rw [hresdeg 𝔮₀ h𝔮₀p h𝔮₀lo, mul_one] at hcard
  rw [hcard, IsGalois.card_aut_eq_finrank K (↥F)]

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem absNorm_eq_of_liesOver_fixedField
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    haveI : IsGalois K (IntermediateField.fixedField H) :=
      IsGalois.of_fixedField_normal_subgroup H
    haveI : NumberField (IntermediateField.fixedField H) :=
      NumberField.of_intermediateField _
    ∀ 𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 →
      Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭 := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  have hresdeg := finrank_residue_fixedField_eq_one K L H 𝔭 hunr hmem
  intro 𝔮 h𝔮p h𝔮lo
  haveI := h𝔮p
  haveI := h𝔮lo
  have hinert : (𝔮.under (𝓞 K)).inertiaDeg 𝔮 = 1 := by
    rw [Ideal.inertiaDeg_algebraMap]
    exact hresdeg 𝔮 h𝔮p h𝔮lo
  have hunder : 𝔮.under (𝓞 K) = 𝔭 := h𝔮lo.over.symm
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔮 (𝔮.under (𝓞 K)) inferInstance
    (hunder ▸ UnramifiedIn.ne_bot K L hunr), hinert, pow_one, hunder]

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem primeIdealZetaSum_unramified_coprime_div_log_tendsto_one (K L : Type*) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (m : ℕ) [NeZero m] :
    Filter.Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s
          / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  set Uc : Set (Ideal (𝓞 K)) :=
    {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m}
  set D : Set (Ideal (𝓞 K)) :=
    {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m)}
  have hdisj : Disjoint Uc D :=
    Set.disjoint_left.mpr fun 𝔭 hc hd ↦ hd.2.2 ⟨hc.2.1, hc.2.2⟩
  have hcover : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ Uc ∪ D := fun 𝔭 hp hne ↦ by
    by_cases h : UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m
    · exact Or.inl ⟨hp, h.1, h.2⟩
    · exact Or.inr ⟨hp, hne, h⟩
  have hDfin : D.Finite := by
    refine ((finite_ramifiedIn K L).union (finite_badPrimes K m)).subset ?_
    rintro 𝔭 ⟨hp, hne, hnot⟩
    by_cases hunr : UnramifiedIn K L 𝔭
    · exact Or.inr ⟨hp, hne, fun hcop ↦ hnot ⟨hunr, hcop⟩⟩
    · exact Or.inl ⟨hp, hne, hunr⟩
  obtain ⟨CD, hCD⟩ : ∃ CD : ℝ, ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), primeIdealZetaSum D s ≤ CD := by
    refine ⟨Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ D ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Ioi] at hs
    exact primeIdealZetaSum_le_card_of_finite K hDfin (by linarith)
  have hDzero : Filter.Tendsto (fun s : ℝ ↦ primeIdealZetaSum D s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have hL := tendsto_log_one_div_sub_one_atTop
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop tendsto_const_nhds hL (a := CD))
    filter_upwards [hCD, hL.eventually_gt_atTop 0] with s hub hLpos
    have hDnn : 0 ≤ primeIdealZetaSum D s := by
      rw [primeIdealZetaSum_def K]
      exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (div_nonneg hDnn hLpos.le)]
    gcongr
  have hcomb : Filter.Tendsto (fun s : ℝ ↦
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s / Real.log (1 / (s - 1))
        - primeIdealZetaSum D s / Real.log (1 / (s - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    simpa using (primeIdealZetaSum_univ_tendsto_log K).sub hDzero
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hadd : primeIdealZetaSum Uc s + primeIdealZetaSum D s =
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s := by
    rw [← primeIdealZetaSum_union_of_disjoint K hdisj hs,
      primeIdealZetaSum_eq_univ_of_forall_prime_mem K hcover s]
  rw [← sub_div, ← hadd, add_sub_cancel_right]

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem finite_primesLiesOver_ne_bot (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (F : IntermediateField K L) [IsGalois K F]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal] :
    haveI : NumberField F := NumberField.of_intermediateField F
    Finite {𝔮 : Ideal (𝓞 ↥F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} := by
  haveI : NumberField F := NumberField.of_intermediateField F
  haveI : Finite (𝔭.primesOver (𝓞 ↥F)) :=
    (IsDedekindDomain.primesOver_finite 𝔭 (𝓞 ↥F)).to_subtype
  refine Finite.of_injective (β := 𝔭.primesOver (𝓞 ↥F)) (fun y ↦ ⟨y.1, y.2.1, y.2.2.1⟩)
    fun a b hab ↦ Subtype.ext ?_
  exact congrArg (Subtype.val : 𝔭.primesOver (𝓞 ↥F) → _) hab

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem primeIdealZetaSum_under_eq_finrank_mul (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (m : ℕ) [IsMulCommutative Gal(L/K)]
    (H : Subgroup Gal(L/K))
    (hsplit : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → UnramifiedIn K L 𝔭 → (Ideal.absNorm 𝔭).Coprime m →
      Nat.card {𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)) //
          𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} = Module.finrank K ↥(IntermediateField.fixedField H)
        ∧ ∀ 𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 →
            Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭)
    {s : ℝ} (hs : 1 < s) :
    haveI : IsGalois K (IntermediateField.fixedField H) :=
      IsGalois.of_fixedField_normal_subgroup H
    haveI : NumberField (IntermediateField.fixedField H) := NumberField.of_intermediateField _
    primeIdealZetaSum {𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)) | 𝔮.IsPrime ∧
        UnramifiedIn K L (𝔮.under (𝓞 K)) ∧ (Ideal.absNorm (𝔮.under (𝓞 K))).Coprime m} s
      = (Module.finrank K ↥(IntermediateField.fixedField H) : ℝ) * primeIdealZetaSum
          {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  set U : Set (Ideal (𝓞 K)) :=
    {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m}
  set V : Set (Ideal (𝓞 F)) :=
    {𝔮 | 𝔮.IsPrime ∧ UnramifiedIn K L (𝔮.under (𝓞 K)) ∧ (Ideal.absNorm (𝔮.under (𝓞 K))).Coprime m}
  set IU := {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ U ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}
  set IV := {𝔮 : Ideal (𝓞 F) // 𝔮 ∈ V ∧ 𝔮.IsPrime ∧ 𝔮 ≠ ⊥}
  have hφ_mem : ∀ 𝔮 : IV, (𝔮.1.under (𝓞 K)) ∈ U ∧ (𝔮.1.under (𝓞 K)).IsPrime
      ∧ (𝔮.1.under (𝓞 K)) ≠ ⊥ := fun 𝔮 ↦ by
    haveI := 𝔮.2.2.1
    exact ⟨⟨inferInstance, 𝔮.2.1.2.1, 𝔮.2.1.2.2⟩, inferInstance,
      Ideal.IsIntegral.comap_ne_bot (𝓞 K) 𝔮.2.2.2⟩
  set φ : IV → IU := fun 𝔮 ↦ ⟨𝔮.1.under (𝓞 K), hφ_mem 𝔮⟩
  set e := Equiv.sigmaFiberEquiv φ
  have hsummSig : Summable (fun p : Σ 𝔭 : IU, {𝔮 : IV // φ 𝔮 = 𝔭} ↦
      (Ideal.absNorm (e p).1 : ℝ) ^ (-s)) :=
    (e.summable_iff (f := fun 𝔮 : IV ↦ (Ideal.absNorm 𝔮.1 : ℝ) ^ (-s))).mpr
      (summable_prime_absNorm_rpow F V hs)
  rw [primeIdealZetaSum_def F, ← e.tsum_eq (fun 𝔮 : IV ↦ (Ideal.absNorm (𝔮.1) : ℝ) ^ (-s)),
    hsummSig.tsum_sigma, primeIdealZetaSum_def K, ← tsum_mul_left]
  refine tsum_congr (fun 𝔭 ↦ ?_)
  haveI := 𝔭.2.2.1
  have hfibeq : {𝔮 : IV // φ 𝔮 = 𝔭} ≃
      {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭.1 ∧ 𝔮 ≠ ⊥} :=
    { toFun := fun x ↦ ⟨x.1.1, x.1.2.2.1, ⟨(Subtype.ext_iff.mp x.2).symm⟩, x.1.2.2.2⟩
      invFun := fun y ↦ ⟨⟨y.1, ⟨y.2.1, by
          haveI := y.2.1
          haveI := y.2.2.1
          exact (y.2.2.1.over ▸ 𝔭.2.1.2 : UnramifiedIn K L (y.1.under (𝓞 K)) ∧
            (Ideal.absNorm (y.1.under (𝓞 K))).Coprime m)⟩, y.2.1, y.2.2.2⟩,
        Subtype.ext (haveI := y.2.2.1; y.2.2.1.over.symm)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hconst : ∀ x : {𝔮 : IV // φ 𝔮 = 𝔭}, (Ideal.absNorm (e ⟨𝔭, x⟩).1 : ℝ) ^ (-s)
      = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun x ↦ by
    change (Ideal.absNorm x.1.1 : ℝ) ^ (-s) = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
    rw [(hsplit 𝔭.1 𝔭.2.2.1 𝔭.2.1.2.1 𝔭.2.1.2.2).2 x.1.1 x.1.2.2.1 ⟨(Subtype.ext_iff.mp x.2).symm⟩]
  haveI : 𝔭.1.IsMaximal := 𝔭.2.2.1.isMaximal 𝔭.2.2.2
  haveI : Finite {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭.1 ∧ 𝔮 ≠ ⊥} :=
    finite_primesLiesOver_ne_bot K L F 𝔭.1
  haveI : Finite {𝔮 : IV // φ 𝔮 = 𝔭} := Finite.of_equiv _ hfibeq.symm
  rw [tsum_congr hconst, tsum_const, Nat.card_congr hfibeq,
    (hsplit 𝔭.1 𝔭.2.2.1 𝔭.2.1.2.1 𝔭.2.1.2.2).1, nsmul_eq_mul, mul_comm]

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem finrank_mul_unramified_coprime_le_univ (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (m : ℕ)
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      (Ideal.absNorm 𝔭).Coprime m → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H)
    {s : ℝ} (hs : 1 < s) :
    (Module.finrank K ↥(IntermediateField.fixedField H) : ℝ) *
        primeIdealZetaSum
          {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s
      ≤ primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField H)))) s := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  have hsplit : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → UnramifiedIn K L 𝔭 → (Ideal.absNorm 𝔭).Coprime m →
      Nat.card {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} = Module.finrank K ↥F
        ∧ ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 → Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭 :=
    fun 𝔭 h𝔭p h𝔭unr h𝔭cop ↦
      ⟨card_primesOver_fixedField_eq_finrank K L H 𝔭 h𝔭unr
          (hH 𝔭 h𝔭p (UnramifiedIn.ne_bot K L h𝔭unr) h𝔭unr h𝔭cop),
        absNorm_eq_of_liesOver_fixedField K L H 𝔭 h𝔭unr
          (hH 𝔭 h𝔭p (UnramifiedIn.ne_bot K L h𝔭unr) h𝔭unr h𝔭cop)⟩
  rw [← primeIdealZetaSum_under_eq_finrank_mul K L m H hsplit hs]
  exact primeIdealZetaSum_le_of_subset F (Set.subset_univ _) hs

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime (K L : Type*) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (m : ℕ) [NeZero m]
    [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      (Ideal.absNorm 𝔭).Coprime m → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    Module.finrank K (IntermediateField.fixedField H) ≤ 1 := by
  set F := IntermediateField.fixedField H
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  set d : ℕ := Module.finrank K ↥F
  rw [← Nat.cast_le (α := ℝ), Nat.cast_one]
  set A : ℝ → ℝ := fun s ↦ primeIdealZetaSum
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s
  set B : ℝ → ℝ := fun s ↦
    primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 ↥F))) s
  have hAtend : Filter.Tendsto (fun s ↦ A s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    primeIdealZetaSum_unramified_coprime_div_log_tendsto_one K L m
  have hBtend : Filter.Tendsto (fun s ↦ B s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    primeIdealZetaSum_univ_tendsto_log (↥F)
  have hLpos : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), 0 < Real.log (1 / (s - 1)) :=
    tendsto_log_one_div_sub_one_atTop.eventually_gt_atTop 0
  have hev : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
      (d : ℝ) * (A s / Real.log (1 / (s - 1))) ≤ B s / Real.log (1 / (s - 1)) := by
    filter_upwards [hLpos, self_mem_nhdsWithin] with s hLs hs1
    simp only [Set.mem_Ioi] at hs1
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (finrank_mul_unramified_coprime_le_univ K L m H hH hs1) hLs.le
  have hlim := le_of_tendsto_of_tendsto (hAtend.const_mul (d : ℝ)) hBtend hev
  simpa using hlim

/-- Planning source: CyclotomicNormResidue.lean; coprime generation child. -/
theorem subgroup_eq_top_of_forall_frobenius_mem_of_coprime
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      (Ideal.absNorm 𝔭).Coprime m → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    H = ⊤ := by
  rw [← Subgroup.card_eq_iff_eq_top]
  have hfk : Module.finrank K (IntermediateField.fixedField H) = 1 :=
    le_antisymm (finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime K L m H hH)
      Module.finrank_pos
  have htower := Module.finrank_mul_finrank K (IntermediateField.fixedField H) L
  rw [hfk, one_mul] at htower
  rw [IsGalois.card_aut_eq_finrank K L, ← htower, IntermediateField.finrank_fixedField_eq_card H]

end Cox.Chebotarev
