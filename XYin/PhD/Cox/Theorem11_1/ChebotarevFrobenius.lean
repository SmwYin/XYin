/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevDefs
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Frobenius and ramification algebra

Source AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87` is not an imported dependency.
Contracts are adapted to pinned Lean 4.30.0. Local prerequisites precede their consumers. See the
declaration records for exact source matches and remaining port boundaries.
-/

noncomputable section
open Filter NumberField Topology Set UniqueFactorizationMonoid
open scoped Pointwise
namespace Cox.Chebotarev
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]
variable {S : Set (Ideal (𝓞 K))} {δ : ℝ}

/-- The Galois group acts faithfully on `𝓞 L` (AINTLIB Frobenius.lean:135). -/
private instance faithfulSMul_galois : FaithfulSMul Gal(L/K) (𝓞 L) :=
  IsGaloisGroup.faithful (𝓞 K)

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- Planning source: Frobenius.lean:78; statement placeholder. -/
theorem exists_prime_liesOver
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hnz : 𝔭 ≠ ⊥) :
    ∃ 𝔓 : Ideal (𝓞 L), 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥ := by
  obtain ⟨𝔓, hp, hcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by simp)
  have : 𝔓.LiesOver 𝔭 := ⟨hcomap.symm⟩
  exact ⟨𝔓, hp, ⟨hcomap.symm⟩, Ideal.ne_bot_of_liesOver_of_ne_bot hnz 𝔓⟩

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- Planning source: Frobenius.lean:72; statement placeholder. -/
theorem UnramifiedIn.ne_bot {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) :
    𝔭 ≠ ⊥ :=
  hunr.1

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- Planning source: Frobenius.lean:66; statement placeholder. -/
theorem ne_bot_of_ramificationIdx_eq_one
    {𝔓 : Ideal (𝓞 L)} (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) : 𝔓 ≠ ⊥ := by
  rintro rfl
  simp at hunr

omit [IsGalois K L] in
/-- Planning source: Frobenius.lean:90; statement placeholder. -/
theorem UnramifiedIn.ramificationIdx_eq_one
    {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hP : 𝔓.LiesOver 𝔭) : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1 := by
  have h𝔓 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓
  have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 := hunr.2 𝔓 (‹𝔓.IsPrime›.isMaximal h𝔓) hP
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔓).mp this

omit [IsGalois K L] in
/-- Planning source: Frobenius.lean:102; statement placeholder. -/
theorem UnramifiedIn.finite_quotient
    {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hP : 𝔓.LiesOver 𝔭) : Finite (𝓞 L ⧸ 𝔓) :=
  Ideal.finiteQuotientOfFreeOfNeBot 𝔓
    (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hP))

/-- Planning source: Frobenius.lean:140; statement placeholder. -/
theorem eq_arithFrobAt_of_isArithFrobAt
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] [Finite (𝓞 L ⧸ 𝔓)] [Algebra.IsUnramifiedAt (𝓞 K) 𝔓]
    (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    σ = arithFrobAt (𝓞 K) Gal(L/K) 𝔓 :=
  MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L) <|
    AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) 𝔓.primeCompl_le_nonZeroDivisors

/-- Planning source: Frobenius.lean:151; statement placeholder. -/
theorem isConj_of_isArithFrobAt
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (σ σ' : Gal(L/K)) (𝔓 𝔓' : Ideal (𝓞 L)) [𝔓.IsPrime] [𝔓'.IsPrime]
    (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) (hσ' : IsArithFrobAt (𝓞 K) σ' 𝔓')
    (hP : 𝔓.LiesOver 𝔭) (hP' : 𝔓'.LiesOver 𝔭) :
    IsConj σ σ' := by
  have := hP
  have := hP'
  have : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 hP
  have : Finite (𝓞 L ⧸ 𝔓') := UnramifiedIn.finite_quotient K L hunr 𝔓' hP'
  have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    hunr.2 𝔓 (‹𝔓.IsPrime›.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)) hP
  have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓' :=
    hunr.2 𝔓' (‹𝔓'.IsPrime›.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓')) hP'
  rw [eq_arithFrobAt_of_isArithFrobAt K L 𝔓 σ hσ,
    eq_arithFrobAt_of_isArithFrobAt K L 𝔓' σ' hσ']
  exact isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔓 𝔓' (hP.over.symm.trans hP'.over)

/-- Planning source: Frobenius.lean:174; statement placeholder. -/
theorem exists_frobeniusClass
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) :
    ∃ C : ConjClasses Gal(L/K),
      ∀ (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (_ : IsArithFrobAt (𝓞 K) σ 𝔓)
        (_ : 𝔓.LiesOver 𝔭), C = ConjClasses.mk σ := by
  obtain ⟨𝔓₀, hp₀, hlo₀, _⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  have := hp₀
  have : Finite (𝓞 L ⧸ 𝔓₀) := UnramifiedIn.finite_quotient K L hunr 𝔓₀ hlo₀
  refine ⟨ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀), fun σ 𝔓 _ hσ hP ↦ ?_⟩
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_of_isArithFrobAt K L 𝔭 hunr
    (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) σ 𝔓₀ 𝔓
    (hσ := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) (hσ' := hσ) (hP := hlo₀) (hP' := hP))

/-- Planning source: Frobenius.lean:193; statement placeholder. -/
def frobeniusClass (𝔭 : Ideal (𝓞 K)) : ConjClasses Gal(L/K) :=
  open Classical in
  if h : 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 then
    have := h.1
    (exists_frobeniusClass K L 𝔭 h.2).choose
  else
    ConjClasses.mk 1

/-- Planning source: Main.lean:73–75 (named abbreviation of source set); statement placeholder. -/
def frobeniusClassPrimes (C : ConjClasses Gal(L/K)) : Set (Ideal (𝓞 K)) :=
  {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C}

/-- Planning source: Frobenius.lean:203; statement placeholder. -/
theorem frobeniusClass_eq_mk_of_isArithFrobAt
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hσ : IsArithFrobAt (𝓞 K) σ 𝔓)
    (hP : 𝔓.LiesOver 𝔭) :
    frobeniusClass K L 𝔭 = ConjClasses.mk σ := by
  rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, hunr⟩]
  exact (exists_frobeniusClass K L 𝔭 hunr).choose_spec σ 𝔓 hσ hP

omit [IsGalois K L] in
/-- Planning source: Frobenius.lean:333; statement placeholder. -/
theorem finite_ramifiedIn :
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}.Finite := by
  let : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    FractionRing.liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
  have : IsScalarTower (𝓞 K) (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    FractionRing.isScalarTower_liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
  have hbot : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact differentIdeal_ne_bot
  apply Set.Finite.subset
    ((Ideal.finite_factors hbot).image (fun v ↦ (v.asIdeal).under (𝓞 K)))
  rintro 𝔭 ⟨-, h𝔭bot, hnunr⟩
  simp only [UnramifiedIn, not_and, not_forall] at hnunr
  obtain ⟨𝔓, h𝔓max, h𝔓lo, h𝔓nu⟩ := hnunr h𝔭bot
  have := h𝔓max.isPrime
  have := h𝔓lo
  have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭bot 𝔓
  have hdvd : 𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    by_contra h
    exact h𝔓nu (not_dvd_differentIdeal_iff.mp h)
  exact ⟨⟨𝔓, h𝔓max.isPrime, h𝔓bot⟩, hdvd, h𝔓lo.over.symm⟩

/-- Planning source: Frobenius.lean:110; statement placeholder. -/
theorem inertiaGroup_trivial_of_unramified
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    Ideal.inertia Gal(L/K) 𝔓 = ⊥ := by
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hunr
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
  have : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  have : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  haveI : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpbot
  have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    let : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
    let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    haveI : Algebra.IsAlgebraic (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hcard : Nat.card (Ideal.inertia Gal(L/K) 𝔓) =
      Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (𝔓.under (𝓞 K)) hpbot 𝔓,
      Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K)]
  rw [Subgroup.eq_bot_iff_card, hcard, hunr]

/-- Planning source: Frobenius.lean:216; statement placeholder. -/
theorem orderOf_eq_finrank_of_isArithFrobAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (h : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    orderOf σ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L h
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
  have : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  have : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot).mpr h
  rw [eq_arithFrobAt_of_isArithFrobAt K L 𝔓 σ hσ]
  let : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
  let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) :=
    Ideal.finiteQuotientOfFreeOfNeBot (𝔓.under (𝓞 K)) hpbot
  have : Algebra.IsAlgebraic (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  let : Fintype (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Fintype.ofFinite _
  set g₀ : MulAction.stabilizer Gal(L/K) 𝔓 :=
    ⟨arithFrobAt (𝓞 K) Gal(L/K) 𝔓,
      IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) 𝔓⟩ with hg₀
  have hres : Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀
      = FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    ext x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hg₀, Ideal.Quotient.stabilizerHom_apply,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← Nat.card_eq_fintype_card]
    exact (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).mk_apply b
  have hinj : Function.Injective (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom]
    show (Ideal.inertia Gal(L/K) 𝔓).subgroupOf (MulAction.stabilizer Gal(L/K) 𝔓) = ⊥
    rw [inertiaGroup_trivial_of_unramified K L 𝔓 h, Subgroup.bot_subgroupOf]
  calc orderOf (arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
      = orderOf g₀ := by rw [hg₀, Subgroup.orderOf_mk]
    _ = orderOf (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀) :=
        (orderOf_injective _ hinj g₀).symm
    _ = orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic
          (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓)) := by rw [hres]
    _ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
        FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic _ _

/-- Planning source: Frobenius.lean:301; statement placeholder. -/
theorem finrank_residue_eq_orderOf
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hCfrob : frobeniusClass K L 𝔭 = C)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hlo : 𝔓.LiesOver 𝔭) :
    Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) = orderOf σ := by
  have hra := UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hlo
  have : Finite (𝓞 L ⧸ 𝔓) := UnramifiedIn.finite_quotient K L hunr 𝔓 hlo
  obtain ⟨c, hc⟩ : IsConj (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) σ := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj,
      ← frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr _ 𝔓
        (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) hlo, hCfrob, hσ]
  rw [← hc.orderOf_eq,
    orderOf_eq_finrank_of_isArithFrobAt K L _ 𝔓 hra (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)]

/-- Planning source: Frobenius.lean:264; statement placeholder. -/
theorem card_primesAbove_mul_finrank_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (𝔓₀ : Ideal (𝓞 L)) [𝔓₀.IsPrime] (hlo : 𝔓₀.LiesOver 𝔭) :
    Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}
        * Module.finrank (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) = Nat.card Gal(L/K) := by
  have hpbot : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L hunr
  have he : Ideal.ramificationIdx (𝔓₀.under (𝓞 K)) 𝔓₀ = 1 :=
    UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓₀ hlo
  have hP0bot : 𝔓₀ ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L he
  have hunder : 𝔓₀.under (𝓞 K) = 𝔭 := hlo.over.symm
  have hp_under_bot : 𝔓₀.under (𝓞 K) ≠ ⊥ := hunder ▸ hpbot
  have : 𝔓₀.IsMaximal := ‹𝔓₀.IsPrime›.isMaximal hP0bot
  have : (𝔓₀.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓₀.under (𝓞 K)).IsPrime).isMaximal hp_under_bot
  have : Finite (𝓞 L ⧸ 𝔓₀) := UnramifiedIn.finite_quotient K L hunr 𝔓₀ hlo
  haveI : Finite (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hp_under_bot
  have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) := by
    let : Field (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) := Ideal.Quotient.field _
    let : Field (𝓞 L ⧸ 𝔓₀) := Ideal.Quotient.field _
    haveI : Algebra.IsAlgebraic (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have H := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
    (G := Gal(L/K)) (𝔓₀.under (𝓞 K)) 𝔓₀
  rw [inertiaGroup_trivial_of_unramified K L 𝔓₀ he, Subgroup.card_bot, mul_one] at H
  have hset : (𝔓₀.under (𝓞 K)).primesOver (𝓞 L)
      = {𝔓 : Ideal (𝓞 L) | 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} := by
    ext 𝔓
    refine ⟨fun ⟨hp, hlo'⟩ ↦ ?_, fun ⟨hp, hlo', _⟩ ↦ ?_⟩
    · have := hlo'
      exact ⟨hp, hunder ▸ hlo', Ideal.ne_bot_of_liesOver_of_ne_bot hp_under_bot 𝔓⟩
    · exact ⟨hp, hunder ▸ hlo'⟩
  rwa [hset, ← Nat.card_coe_set_eq] at H

/-- Planning source: Frobenius.lean:321; statement placeholder. -/
theorem card_primesAbove_mul_orderOf_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (_hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (_hCfrob : frobeniusClass K L 𝔭 = C) :
    Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} * orderOf σ
      = Nat.card Gal(L/K) := by
  obtain ⟨𝔓₀, hp₀, hlo₀, _⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  rw [← finrank_residue_eq_orderOf K L σ C _hσ 𝔭 hunr _hCfrob 𝔓₀ hlo₀]
  exact card_primesAbove_mul_finrank_eq K L 𝔭 hunr 𝔓₀ hlo₀

end Cox.Chebotarev
