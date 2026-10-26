/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldPrimeEvaluation
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinAuxiliaryCore

/-!
# The arithmetic Frobenius prime assignment

Janusz III.2–3, printed pp.98 and103: in an abelian extension the actual Frobenius class
representative acts arithmetically at every prime above the chosen base prime. Restricting its
prime-power product defines `arithmeticArtin`. Surjectivity is separate.
-/

open NumberField IsDedekindDomain Cox.Chebotarev
open scoped nonZeroDivisors IsMulCommutative
noncomputable section
namespace Cox.ClassFieldTheory

/-- The actual Frobenius representative acts arithmetically at each prime above q. -/
theorem frobeniusClass_out_isArithFrobAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L]
    (q : Ideal (𝓞 K)) [q.IsPrime] (hU : UnramifiedIn K L q)
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P.LiesOver q) :
    IsArithFrobAt (𝓞 K) (frobeniusClass K L q).out P := by
  haveI : Finite (𝓞 L ⧸ P) := UnramifiedIn.finite_quotient K L hU P hP
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hU.1 P
  haveI : Algebra.IsUnramifiedAt (𝓞 K) P := hU.2 P (‹P.IsPrime›.isMaximal hP0) hP
  have hσ := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) P
  have h := frobeniusClass_eq_mk_of_isArithFrobAt K L q hU _ P hσ hP
  have heq : (frobeniusClass K L q).out = arithFrobAt (𝓞 K) Gal(L/K) P := by
    apply ConjClasses.mk_injective
    rw [← h]
    exact Quotient.out_eq' _
  rw [heq]
  exact hσ

/-- The prime-power Frobenius assignment restricted to the prime-to-modulus ideal group. -/
def arithmeticArtin
    (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] :
    coprimeIdeals K m →* Gal(L/K) :=
  (primeEvaluation K (fun v => (frobeniusClass K L v.asIdeal).out)).comp
    (coprimeIdeals K m).subtype

/-- On a represented prime ideal, the concrete map has its assigned Frobenius value. -/
theorem arithmeticArtin_prime
    (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (q : Ideal (𝓞 K)) (hq : q.IsPrime) (hq0 : q ≠ ⊥)
    (u : coprimeIdeals K m)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q) :
    arithmeticArtin K m L u = (frobeniusClass K L q).out := by
  let v : HeightOneSpectrum (𝓞 K) := ⟨q, hq, hq0⟩
  have hv : (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = primeIdealUnit K v :=
    Units.ext (hu.trans (primeIdealUnit_coe K v).symm)
  change primeEvaluation K _ (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = _
  rw [hv, primeEvaluation_primeIdealUnit]

/-- Unramifiedness outside the modulus makes the concrete map satisfy the Artin condition. -/
theorem arithmeticArtin_isArtinMap
    (K : Type*) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (hU : IsUnramifiedAway K m L) : IsArtinMap K m L (arithmeticArtin K m L) := by
  intro q hq hq0 hqm u hu P hP x
  haveI : q.IsPrime := hq
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver q := hP.2
  have hUq : UnramifiedIn K L q :=
    ArtinAuxiliary.unramifiedIn_of_ramificationIdx_eq_one K L q hq0 (hU q hq hq0 hqm)
  have hfrob := frobeniusClass_out_isArithFrobAt K L q hUq P hP.2
  rw [arithmeticArtin_prime K m L q hq hq0 u hu]
  have h := hfrob x
  rw [← Ideal.over_def P q] at h
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact h

end Cox.ClassFieldTheory
