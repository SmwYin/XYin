/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldTheory
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicDegree
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! # The coprime-degree step in Janusz V.11.2
Printed p.186/PDF197 has a degree typo: it is [Z′ : Z], not [E′ : Z′],
that divides q−1. The contracts below use the corrected degree and actual prime ideals.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

variable (K E : Type*) [Field K] [hNF_K : NumberField K] [Field E] [hNF_E : NumberField E]
  [Algebra K E]

omit hNF_K hNF_E in
/-- Lagrange applied to the faithful action on a primitive root gives degree divisibility. -/
theorem cyclotomic_finrank_dvd_prime_pred (q : ℕ) (hq : q.Prime)
    [IsCyclotomicExtension {q} K E] : Module.finrank K E ∣ q - 1 := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  letI : Fact q.Prime := ⟨hq⟩
  simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using
    cyclotomic_finrank_dvd_card_units K E q

include hNF_K hNF_E in
/-- In a Galois number-field extension each ramification index divides the extension degree. -/
theorem ramificationIdx_dvd_finrank [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    [hvw : w.asIdeal.LiesOver v.asIdeal] :
    Ideal.ramificationIdx v.asIdeal w.asIdeal ∣ Module.finrank K E := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.ne_bot (𝓞 E)
    (E ≃ₐ[K] E)
  rw [IsGalois.card_aut_eq_finrank,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (E ≃ₐ[K] E)] at h
  exact ⟨(v.asIdeal.primesOver (𝓞 E)).ncard * v.asIdeal.inertiaDegIn (𝓞 E), by
    rw [← h]
    ring⟩

include hNF_K hNF_E in
/-- In a Galois number-field extension each residue degree divides the extension degree. -/
theorem inertiaDeg_dvd_finrank [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    [hvw : w.asIdeal.LiesOver v.asIdeal] :
    Ideal.inertiaDeg v.asIdeal w.asIdeal ∣ Module.finrank K E := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.ne_bot (𝓞 E)
    (E ≃ₐ[K] E)
  rw [IsGalois.card_aut_eq_finrank,
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal (E ≃ₐ[K] E)] at h
  exact ⟨(v.asIdeal.primesOver (𝓞 E)).ncard * v.asIdeal.ramificationIdxIn (𝓞 E), by
    rw [← h]
    ring⟩

variable (B F : Type*) [Field B] [hNF_B : NumberField B] [Field F] [hNF_F : NumberField F]
  [Algebra K B] [Algebra K F] [Algebra E F] [Algebra B F]
  [IsScalarTower K E F] [IsScalarTower K B F]

include hNF_K hNF_E hNF_B hNF_F in
-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- If an upper prime is unramified over B, its E/K ramification divides the B/K index. -/
theorem ramificationIdx_dvd_of_upper_eq_one
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (v' : HeightOneSpectrum (𝓞 B)) (w' : HeightOneSpectrum (𝓞 F))
    [hvw : w.asIdeal.LiesOver v.asIdeal] [hvv' : v'.asIdeal.LiesOver v.asIdeal]
    [hww' : w'.asIdeal.LiesOver w.asIdeal] [hv'w' : w'.asIdeal.LiesOver v'.asIdeal]
    (hupper : Ideal.ramificationIdx v'.asIdeal w'.asIdeal = 1) :
    Ideal.ramificationIdx v.asIdeal w.asIdeal ∣
      Ideal.ramificationIdx v.asIdeal v'.asIdeal := by
  have h1 := Ideal.ramificationIdx_algebra_tower' v.asIdeal w.asIdeal w'.asIdeal
  have h2 := Ideal.ramificationIdx_algebra_tower' v.asIdeal v'.asIdeal w'.asIdeal
  rw [hupper, mul_one] at h2
  exact ⟨_, h2.symm.trans h1⟩

include hNF_K hNF_E hNF_B hNF_F in
-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- If the upper residue degree over B is one, its E/K degree divides the B/K degree. -/
theorem inertiaDeg_dvd_of_upper_eq_one
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (v' : HeightOneSpectrum (𝓞 B)) (w' : HeightOneSpectrum (𝓞 F))
    [hvw : w.asIdeal.LiesOver v.asIdeal] [hvv' : v'.asIdeal.LiesOver v.asIdeal]
    [hww' : w'.asIdeal.LiesOver w.asIdeal] [hv'w' : w'.asIdeal.LiesOver v'.asIdeal]
    (hupper : Ideal.inertiaDeg v'.asIdeal w'.asIdeal = 1) :
    Ideal.inertiaDeg v.asIdeal w.asIdeal ∣ Ideal.inertiaDeg v.asIdeal v'.asIdeal := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : v'.asIdeal.IsMaximal := v'.isMaximal
  have h1 := Ideal.inertiaDeg_algebra_tower v.asIdeal w.asIdeal w'.asIdeal
  have h2 := Ideal.inertiaDeg_algebra_tower v.asIdeal v'.asIdeal w'.asIdeal
  rw [hupper, mul_one] at h2
  exact ⟨_, h2.symm.trans h1⟩

include hNF_K hNF_E hNF_B hNF_F in
/-- Coprime global degrees and upper unramifiedness force the lower ramification index to one. -/
theorem ramificationIdx_eq_one_of_coprime_baseChange [IsGalois K E] [IsGalois K B]
    (hcop : Nat.Coprime (Module.finrank K E) (Module.finrank K B))
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (v' : HeightOneSpectrum (𝓞 B)) (w' : HeightOneSpectrum (𝓞 F))
    [hvw : w.asIdeal.LiesOver v.asIdeal] [hvv' : v'.asIdeal.LiesOver v.asIdeal]
    [hww' : w'.asIdeal.LiesOver w.asIdeal] [hv'w' : w'.asIdeal.LiesOver v'.asIdeal]
    (he : Ideal.ramificationIdx v'.asIdeal w'.asIdeal = 1) :
    Ideal.ramificationIdx v.asIdeal w.asIdeal = 1 := by
  exact Nat.eq_one_of_dvd_coprimes hcop (ramificationIdx_dvd_finrank K E v w)
    ((ramificationIdx_dvd_of_upper_eq_one K E B F v w v' w' he).trans
      (ramificationIdx_dvd_finrank K B v v'))

include hNF_K hNF_E hNF_B hNF_F in
/-- Coprime global degrees and upper residue degree one force the lower residue degree to one. -/
theorem inertiaDeg_eq_one_of_coprime_baseChange [IsGalois K E] [IsGalois K B]
    (hcop : Nat.Coprime (Module.finrank K E) (Module.finrank K B))
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (v' : HeightOneSpectrum (𝓞 B)) (w' : HeightOneSpectrum (𝓞 F))
    [hvw : w.asIdeal.LiesOver v.asIdeal] [hvv' : v'.asIdeal.LiesOver v.asIdeal]
    [hww' : w'.asIdeal.LiesOver w.asIdeal] [hv'w' : w'.asIdeal.LiesOver v'.asIdeal]
    (hf : Ideal.inertiaDeg v'.asIdeal w'.asIdeal = 1) :
    Ideal.inertiaDeg v.asIdeal w.asIdeal = 1 := by
  exact Nat.eq_one_of_dvd_coprimes hcop (inertiaDeg_dvd_finrank K E v w)
    ((inertiaDeg_dvd_of_upper_eq_one K E B F v w v' w' hf).trans
      (inertiaDeg_dvd_finrank K B v v'))

include hNF_K hNF_E hNF_B hNF_F in
/-- Complete splitting descends through a Galois base change of coprime degree. -/
theorem splittingIdeals_of_coprime_baseChange [IsGalois K E] [IsGalois K B]
    (hcop : Nat.Coprime (Module.finrank K E) (Module.finrank K B))
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit : ∀ P ∈ v.asIdeal.primesOver (𝓞 B), P ∈ splittingIdeals B F) :
    v.asIdeal ∈ splittingIdeals K E := by
  refine ⟨v.isPrime, v.ne_bot, fun P hP => ?_⟩
  obtain ⟨hPp, hPo⟩ := hP
  haveI := hPp
  haveI := hPo
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  obtain ⟨Q, hQp, hQc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) P (by simp)
  haveI := hQp
  haveI hQo : Q.LiesOver P := ⟨hQc.symm⟩
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hP0 Q
  haveI : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
  haveI hP'p : (Q.under (𝓞 B)).IsPrime := Ideal.IsPrime.under (𝓞 B) Q
  haveI hP'o : (Q.under (𝓞 B)).LiesOver v.asIdeal := Ideal.LiesOver.tower_bot Q (Q.under (𝓞 B))
    v.asIdeal
  have hP'0 : Q.under (𝓞 B) ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _
  haveI : Q.LiesOver (Q.under (𝓞 B)) := ⟨rfl⟩
  obtain ⟨-, -, hsp⟩ := hsplit (Q.under (𝓞 B)) ⟨hP'p, hP'o⟩
  obtain ⟨he, hf⟩ := hsp Q ⟨hQp, inferInstance⟩
  let w : HeightOneSpectrum (𝓞 E) := ⟨P, hPp, hP0⟩
  let v' : HeightOneSpectrum (𝓞 B) := ⟨Q.under (𝓞 B), hP'p, hP'0⟩
  let w' : HeightOneSpectrum (𝓞 F) := ⟨Q, hQp, hQ0⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := hPo
  haveI : v'.asIdeal.LiesOver v.asIdeal := hP'o
  haveI : w'.asIdeal.LiesOver w.asIdeal := hQo
  haveI : w'.asIdeal.LiesOver v'.asIdeal := ⟨rfl⟩
  exact ⟨ramificationIdx_eq_one_of_coprime_baseChange K E B F hcop v w v' w' he,
    inertiaDeg_eq_one_of_coprime_baseChange K E B F hcop v w v' w' hf⟩

include hNF_K hNF_E hNF_F in
-- The unused section instances are kept: the planned signature includes them.
set_option linter.unusedSectionVars false in
/-- Contraction is onto on primes in a finite integral tower, so uniqueness descends. -/
theorem primesOver_subsingleton_of_tower
    (v : HeightOneSpectrum (𝓞 K))
    (hunique : Subsingleton (v.asIdeal.primesOver (𝓞 F))) :
    Subsingleton (v.asIdeal.primesOver (𝓞 E)) := by
  refine ⟨fun P₁ P₂ => Subtype.ext ?_⟩
  obtain ⟨P₁, hP₁p, hP₁o⟩ := P₁
  obtain ⟨P₂, hP₂p, hP₂o⟩ := P₂
  haveI := hP₁p
  haveI := hP₁o
  haveI := hP₂p
  haveI := hP₂o
  obtain ⟨Q₁, hQ₁p, hQ₁c⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) P₁ (by simp)
  obtain ⟨Q₂, hQ₂p, hQ₂c⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) P₂ (by simp)
  haveI : Q₁.LiesOver P₁ := ⟨hQ₁c.symm⟩
  haveI : Q₂.LiesOver P₂ := ⟨hQ₂c.symm⟩
  haveI : Q₁.LiesOver v.asIdeal := Ideal.LiesOver.trans Q₁ P₁ v.asIdeal
  haveI : Q₂.LiesOver v.asIdeal := Ideal.LiesOver.trans Q₂ P₂ v.asIdeal
  have hQ : Q₁ = Q₂ := congrArg Subtype.val
    (hunique.elim ⟨Q₁, hQ₁p, inferInstance⟩ ⟨Q₂, hQ₂p, inferInstance⟩)
  change P₁ = P₂
  rw [← hQ₁c, ← hQ₂c, hQ]

include hNF_K hNF_E in
/-- The fundamental identity has one summand, equal to one, at a unique completely split prime. -/
theorem finrank_eq_one_of_split_unique
    (v : HeightOneSpectrum (𝓞 K)) (hsplit : v.asIdeal ∈ splittingIdeals K E)
    (hunique : Subsingleton (v.asIdeal.primesOver (𝓞 E))) :
    Module.finrank K E = 1 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨-, -, hsp⟩ := hsplit
  rw [← Ideal.sum_ramification_inertia (𝓞 E) K E v.ne_bot]
  obtain ⟨P, hPp, hPc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 E) v.asIdeal (by simp)
  have hPmem : P ∈ v.asIdeal.primesOver (𝓞 E) := ⟨hPp, ⟨hPc.symm⟩⟩
  have hfin : IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) = {P} := by
    ext Q
    rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot, Finset.mem_singleton]
    constructor
    · intro hQ
      exact congrArg Subtype.val (hunique.elim ⟨Q, hQ⟩ ⟨P, hPmem⟩)
    · rintro rfl
      exact hPmem
  rw [hfin, Finset.sum_singleton, (hsp P hPmem).1, (hsp P hPmem).2]

end Cox.ClassFieldTheory
