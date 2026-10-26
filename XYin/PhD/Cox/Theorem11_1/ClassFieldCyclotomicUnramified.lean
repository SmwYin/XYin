/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import XYin.PhD.Cox.Theorem11_1.ChebotarevDefs

/-!
# Cyclotomic unramifiedness away from the root order

Janusz V.5.4 uses cyclotomic Frobenius at primes coprime to the root order. The root-reduction step
is I.9 Exercise3, printed44/PDF55; the inertia criterion is III.1.2(b), printed95/PDF106. These
contracts reuse Mathlib's root-subgroup injection and inertia cardinality.
-/

namespace Cox.ClassFieldTheory.CyclotomicUnramified

open NumberField
open scoped Pointwise

/-- Coprimality of a residue norm persists in a finite extension above that prime. -/
theorem absNorm_coprime_of_liesOver
    {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Module.Free ℤ R] [Module.Free ℤ S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p]
    (hp : p.IsPrime) (hp0 : p ≠ ⊥) (m : ℕ) (hcop : p.absNorm.Coprime m) :
    P.absNorm.Coprime m := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P p hp hp0]
  exact Nat.Coprime.pow_left _ hcop

/-- Inertia fixes a primitive root whose order is coprime to the residue norm. -/
theorem inertia_fixes_primitiveRoot
    {K E : Type*} [Field K] [Field E] [NumberField E] [Algebra K E]
    (m : ℕ) [NeZero m] (ζ : E) (hζ : IsPrimitiveRoot ζ m)
    (P : Ideal (𝓞 E)) (hP : P.absNorm ≠ 1) (hcop : P.absNorm.Coprime m)
    (σ : Gal(E/K)) (hσ : σ ∈ P.inertia Gal(E/K)) : σ ζ = ζ := by
  set z : 𝓞 E := ⟨ζ, hζ.isIntegral (NeZero.pos m)⟩ with hz
  have hzm : z ^ m = 1 := RingOfIntegers.ext (by simpa using hζ.pow_eq_one)
  have hσzm : (σ • z) ^ m = 1 := by rw [← smul_pow', hzm, smul_one]
  have hmem : σ • z - z ∈ P := (AddSubgroup.mem_inertia.mp hσ) z
  have heq : rootsOfUnity.mkOfPowEq (σ • z) hσzm = rootsOfUnity.mkOfPowEq z hzm := by
    apply Ideal.rootsOfUnityMapQuot_injective m hP hcop
    ext
    simpa [Ideal.rootsOfUnityMapQuot] using Ideal.Quotient.eq.mpr hmem
  have hσz : σ • z = z := by
    simpa using congrArg (fun u : rootsOfUnity m (𝓞 E) ↦ ((u : (𝓞 E)ˣ) : 𝓞 E)) heq
  exact congrArg (algebraMap (𝓞 E) E) hσz

/-- Fixing the primitive cyclotomic generator makes the inertia subgroup trivial. -/
theorem inertia_eq_bot_of_coprime_absNorm
    {K E : Type*} [Field K] [Field E] [NumberField E] [Algebra K E]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K E]
    (P : Ideal (𝓞 E)) (hP : P.absNorm ≠ 1) (hcop : P.absNorm.Coprime m) :
    P.inertia Gal(E/K) = ⊥ := by
  have hζ := IsCyclotomicExtension.zeta_spec m K E
  refine (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ ↦ ?_
  have hfix := inertia_fixes_primitiveRoot m _ hζ P hP hcop σ hσ
  apply AlgEquiv.coe_algHom_injective
  exact (hζ.powerBasis K).algHom_ext (by simpa using hfix)

attribute [local instance] Ideal.Quotient.field in
/-- Trivial inertia gives ramification index one under the residue-separability hypothesis. -/
theorem ramificationIdx_eq_one_of_inertia_eq_bot
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
    [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
    [Module.IsTorsionFree R S]
    (p : Ideal R) (hp : p ≠ ⊥) (P : Ideal S)
    [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)]
    (hI : P.inertia G = ⊥) : Ideal.ramificationIdx p P = 1 := by
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := G) p hp P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G, hI, Subgroup.card_bot] at hcard
  exact hcard.symm

/-- A nonzero prime is unramified in a cyclotomic extension of coprime root order. -/
theorem unramifiedIn_cyclotomic_of_coprime
    (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K E]
    (p : Ideal (𝓞 K)) [p.IsPrime] (hp0 : p ≠ ⊥) (hcop : p.absNorm.Coprime m) :
    Cox.Chebotarev.UnramifiedIn K E p := by
  haveI : IsGalois K E := IsCyclotomicExtension.isGalois {m} K E
  refine ⟨hp0, fun P hPmax hPlo ↦ ?_⟩
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have hpmax : p.IsMaximal := ‹p.IsPrime›.isMaximal hp0
  let : Field (𝓞 K ⧸ p) := Ideal.Quotient.field _
  let : Field (𝓞 E ⧸ P) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot p hp0
  haveI : Algebra.IsAlgebraic (𝓞 K ⧸ p) (𝓞 E ⧸ P) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 E ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hcopP : P.absNorm.Coprime m := absNorm_coprime_of_liesOver p P ‹_› hp0 m hcop
  have hN1 : P.absNorm ≠ 1 := fun h ↦ hPmax.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hI := inertia_eq_bot_of_coprime_absNorm (K := K) m P hN1 hcopP
  have he := ramificationIdx_eq_one_of_inertia_eq_bot (G := Gal(E/K)) p hp0 P hI
  rw [show p = P.under (𝓞 K) from hPlo.over] at he
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP0).mpr he

end Cox.ClassFieldTheory.CyclotomicUnramified
