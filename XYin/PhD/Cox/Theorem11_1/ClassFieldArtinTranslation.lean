/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealQuotients
import XYin.PhD.Cox.Theorem11_1.ClassFieldNormIdeals
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinPrimes
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinTranslationAdapters
import XYin.PhD.Cox.Theorem11_1.ClassFieldArtinIntegral
import Mathlib.FieldTheory.Normal.Basic

/-! # Artin compatibility with relative ideal norms

The five existing interfaces from LocalTranslation implement Janusz III.3.1,
printed103–104. They are placed below class-field existence. Restriction has explicit
generic field binders.
-/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory

/-- Janusz III.3.1, printed 104: iteration raises the residue exponent to the same power. -/
theorem iterate_residue_pow_congruence {R : Type*} [Ring R]
    (σ : R → R) (P : Ideal R) [P.IsTwoSided] (N : ℕ)
    (hσ : ∀ x : R, σ x - x ^ N ∈ P) (n : ℕ) (x : R) :
    (σ^[n]) x - x ^ (N ^ n) ∈ P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h1 := hσ ((σ^[n]) x)
    have h2 : ((σ^[n]) x) ^ N - (x ^ (N ^ n)) ^ N ∈ P := by
      rw [← Ideal.Quotient.eq] at ih ⊢
      rw [map_pow, map_pow, ih]
    rw [← pow_mul, ← pow_succ] at h2
    have h3 := P.add_mem h1 h2
    rwa [sub_add_sub_cancel] at h3

/-- An automorphism of a compositum fixing both generating fields is the identity. -/
theorem compositum_restriction_injective
    (K L E F : Type*) [Field K] [Field L] [Field E] [Field F]
    [Algebra K L] [Algebra K E] [Algebra K F] [Algebra L F] [Algebra E F]
    [IsScalarTower K L F] [IsScalarTower K E F] [Normal K L]
    (hgen : Algebra.adjoin E (Set.range (algebraMap L F)) = ⊤) :
    Function.Injective (fun σ : F ≃ₐ[E] F ↦
      AlgEquiv.restrictNormalHom L (σ.restrictScalars K)) := by
  intro σ τ h
  have h3 : (σ.restrictScalars K).restrictNormal L = (τ.restrictScalars K).restrictNormal L := h
  have hL : ∀ x : L, σ (algebraMap L F x) = τ (algebraMap L F x) := by
    intro x
    have h1 := AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) L x
    have h2 := AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) L x
    rw [h3] at h1
    rw [AlgEquiv.restrictScalars_apply] at h1 h2
    exact h1.symm.trans h2
  have hext : (σ : F →ₐ[E] F) = (τ : F →ₐ[E] F) := by
    refine AlgHom.ext_of_adjoin_eq_top hgen fun y hy => ?_
    obtain ⟨x, rfl⟩ := hy
    exact hL x
  exact AlgEquiv.ext fun y => DFunLike.congr_fun hext y

variable (K L E F : Type*) [Field K] [hNF_K : NumberField K] [Field L] [hNF_L : NumberField L]
  [Field E] [hNF_E : NumberField E] [Field F] [hNF_F : NumberField F]
  [Algebra K L] [Algebra K E] [Algebra K F] [Algebra L F] [Algebra E F]
  [IsScalarTower K L F] [IsScalarTower K E F]

include hNF_K hNF_E in
/-- The good fractional ideal and its norm both admit compatible integral quotients. -/
theorem exists_coprime_norm_quotient [Module.Finite (𝓞 K) (𝓞 E)]
    (m : Ideal (𝓞 K))
    (u : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E)))) :
    ∃ (A B : Ideal (𝓞 E)) (uN : coprimeIdeals K m),
      A ≠ ⊥ ∧ B ≠ ⊥ ∧ A ⊔ m.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤ ∧
      B ⊔ m.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤ ∧
      ((u : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) * B = A ∧
      ((uN : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
        (Ideal.relNorm (𝓞 K) B : FractionalIdeal (𝓞 K)⁰ K) = Ideal.relNorm (𝓞 K) A := by
  obtain ⟨A, B, hA, hB, hAm, hBm, huAB⟩ :=
    exists_coprime_ideal_quotient E (m.map (algebraMap (𝓞 K) (𝓞 E))) u
  obtain ⟨uA, huA⟩ := exists_coprime_relNorm_unit K E m A hA hAm
  obtain ⟨uB, huB⟩ := exists_coprime_relNorm_unit K E m B hB hBm
  refine ⟨A, B, uA / uB, hA, hB, hAm, hBm, huAB, ?_⟩
  rw [← huA, ← huB, ← Units.val_mul, ← Subgroup.coe_mul, div_mul_cancel]

/-- Janusz III.3.1, printed 104: restriction equals the lower Frobenius to the residue degree. -/
theorem artin_baseChange_prime
    (K L E F : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field E] [NumberField E] [Field F]
    [Algebra K L] [Algebra K E] [Algebra K F] [Algebra L F] [Algebra E F]
    [IsScalarTower K L F] [IsScalarTower K E F] [IsGalois K L]
    (m : Ideal (𝓞 K))
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ)
    (hU : IsUnramifiedAway K m L)
    (ψ : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))) →* (F ≃ₐ[E] F))
    (hψ : IsArtinMap E (m.map (algebraMap (𝓞 K) (𝓞 E))) F ψ)
    (q : Ideal (𝓞 E)) (hq : q.IsPrime) (hq0 : q ≠ ⊥)
    (hqm : q ⊔ m.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤)
    (u : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))))
    (hu : ((u : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) = q)
    (uP : coprimeIdeals K m)
    (huP : ((uP : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      q.under (𝓞 K)) :
    AlgEquiv.restrictNormalHom L ((ψ u).restrictScalars K) =
      φ uP ^ Ideal.inertiaDeg (q.under (𝓞 K)) q := by
  haveI := hq
  obtain ⟨P, hPp, hPc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) q (by simp)
  haveI := hPp
  have hPq : P.under (𝓞 E) = q := hPc
  haveI hPL : (P.under (𝓞 L)).IsPrime := Ideal.IsPrime.under (𝓞 L) P
  have hqKp : (q.under (𝓞 K)).IsPrime := Ideal.IsPrime.under (𝓞 K) q
  have hqK0 : q.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot (A := 𝓞 K) hq0
  have hqKm : q.under (𝓞 K) ⊔ m = ⊤ := under_coprime K E m q hqm
  have hPLK : (P.under (𝓞 L)).under (𝓞 K) = q.under (𝓞 K) := by
    rw [Ideal.under_under, ← hPq, Ideal.under_under]
  haveI hPLo : (P.under (𝓞 L)).LiesOver (q.under (𝓞 K)) := ⟨hPLK.symm⟩
  have hPLmem : P.under (𝓞 L) ∈ (q.under (𝓞 K)).primesOver (𝓞 L) := ⟨hPL, hPLo⟩
  have hunr := hU _ hqKp hqK0 hqKm _ hPLmem
  have hinert : Ideal.inertia (L ≃ₐ[K] L) (P.under (𝓞 L)) = ⊥ := by
    apply Chebotarev.inertiaGroup_trivial_of_unramified K L (P.under (𝓞 L))
    rw [hPLK]
    exact hunr
  haveI : q.IsMaximal := hq.isMaximal hq0
  haveI : (q.under (𝓞 K)).IsMaximal := hqKp.isMaximal hqK0
  haveI : CharZero (FractionRing (𝓞 K)) := charZero_of_injective_algebraMap
    (IsFractionRing.injective (𝓞 K) (FractionRing (𝓞 K)))
  have hN : Ideal.absNorm q =
      Ideal.absNorm (q.under (𝓞 K)) ^ Ideal.inertiaDeg (q.under (𝓞 K)) q := by
    rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 E) q,
      Ideal.relNorm_eq_pow_of_isMaximal q (q.under (𝓞 K)), map_pow]
  have hbridge : ∀ (g : L ≃ₐ[K] L) (y : 𝓞 L),
      g • y = RingOfIntegers.mapRingHom g.toRingHom y := by
    intro g y
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingHom_apply]
    simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := L ≃ₐ[K] L) (R := 𝓞 L) (S := L) g y 1).symm
  have hσ : ∀ x : 𝓞 F, RingOfIntegers.mapRingHom ((ψ u).restrictScalars K).toRingHom x -
      x ^ Ideal.absNorm q ∈ P := fun x => hψ q hq hq0 hqm u hu P ⟨hPp, ⟨hPq.symm⟩⟩ x
  have hτ := residue_pow_congruence_restrict K L F ((ψ u).restrictScalars K) P
    (Ideal.absNorm q) hσ
  have hφP : ∀ y : 𝓞 L, (φ uP) • y - y ^ Ideal.absNorm (q.under (𝓞 K)) ∈ P.under (𝓞 L) := by
    intro y
    rw [hbridge]
    exact hφ _ hqKp hqK0 hqKm uP huP _ hPLmem y
  refine eq_of_sub_mem_of_inertia_eq_bot (P.under (𝓞 L)).toAddSubgroup hinert _ _
    fun y => ?_
  have h1 := hτ y
  have h2 := iterate_residue_pow_congruence ((φ uP) • ·) (P.under (𝓞 L)) _ hφP
    (Ideal.inertiaDeg (q.under (𝓞 K)) q) y
  rw [smul_iterate_apply, ← hN] at h2
  rw [← hbridge] at h1
  have h3 := (P.under (𝓞 L)).sub_mem h1 h2
  rw [sub_sub_sub_cancel_right] at h3
  exact h3

/-- Janusz III.3.1, printed 104: multiplicativity extends the prime norm calculation
to the same supplied fractional ideal representatives. -/
theorem artin_baseChange_quotient_norm
    (K L E F : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field E] [NumberField E] [Field F]
    [Algebra K L] [Algebra K E] [Algebra K F] [Algebra L F] [Algebra E F]
    [IsScalarTower K L F] [IsScalarTower K E F] [IsGalois K L]
    [Module.Finite (𝓞 K) (𝓞 E)]
    (m : Ideal (𝓞 K))
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ)
    (hU : IsUnramifiedAway K m L)
    (ψ : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))) →* (F ≃ₐ[E] F))
    (hψ : IsArtinMap E (m.map (algebraMap (𝓞 K) (𝓞 E))) F ψ)
    (u : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))))
    (A B : Ideal (𝓞 E)) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hAm : A ⊔ m.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤)
    (hBm : B ⊔ m.map (algebraMap (𝓞 K) (𝓞 E)) = ⊤)
    (hu : ((u : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) * B = A)
    (uN : coprimeIdeals K m)
    (hN : ((uN : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
      (Ideal.relNorm (𝓞 K) B : FractionalIdeal (𝓞 K)⁰ K) = Ideal.relNorm (𝓞 K) A) :
    AlgEquiv.restrictNormalHom L ((ψ u).restrictScalars K) = φ uN := by
  let ρ : (F ≃ₐ[E] F) →* (L ≃ₐ[K] L) :=
    { toFun := fun σ => AlgEquiv.restrictNormalHom L (σ.restrictScalars K)
      map_one' := by
        have h : (1 : F ≃ₐ[E] F).restrictScalars K = 1 := AlgEquiv.ext fun _ => rfl
        simp only [h, map_one]
      map_mul' := fun σ τ => by
        have h : (σ * τ).restrictScalars K = σ.restrictScalars K * τ.restrictScalars K :=
          AlgEquiv.ext fun _ => rfl
        simp only [h, map_mul] }
  let θ := ρ.comp ψ
  haveI : CharZero (FractionRing (𝓞 K)) := charZero_of_injective_algebraMap
    (IsFractionRing.injective (𝓞 K) (FractionRing (𝓞 K)))
  have key : ∀ C : Ideal (𝓞 E), C ≠ ⊥ → C ⊔ (m.map (algebraMap (𝓞 K) (𝓞 E))) = ⊤ →
      ∀ v : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))), ((v : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
        FractionalIdeal (𝓞 E)⁰ E) = C →
      ∀ w : coprimeIdeals K m, ((w : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = (Ideal.relNorm (𝓞 K) C : FractionalIdeal (𝓞 K)⁰ K) →
      θ v = φ w := by
    intro C hC hCm
    refine ideal_coprime_induction (m.map (algebraMap (𝓞 K) (𝓞 E))) (fun C =>
      ∀ v : coprimeIdeals E (m.map (algebraMap (𝓞 K) (𝓞 E))),
        ((v : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) = C →
      ∀ w : coprimeIdeals K m, ((w : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = (Ideal.relNorm (𝓞 K) C : FractionalIdeal (𝓞 K)⁰ K) →
      θ v = φ w) ?_ ?_ ?_ C hC hCm
    · intro v hv w hw
      have hv1 : v = 1 := Subtype.ext (Units.ext (by
        rw [hv, FractionalIdeal.coeIdeal_top]
        rfl))
      have hw1 : w = 1 := Subtype.ext (Units.ext (by
        rw [hw, Ideal.relNorm_top, FractionalIdeal.coeIdeal_top]
        rfl))
      rw [hv1, hw1, map_one, map_one]
    · intro q hq hq0 hqm v hv w hw
      haveI := hq
      have hqKp : (q.under (𝓞 K)).IsPrime := Ideal.IsPrime.under (𝓞 K) q
      have hqK0 : q.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot (A := 𝓞 K) hq0
      have hqKm : q.under (𝓞 K) ⊔ m = ⊤ := under_coprime K E m q hqm
      obtain ⟨vP, hvP⟩ := exists_coprimeIdealUnit K m _ hqK0 hqKm
      have h1 := artin_baseChange_prime K L E F m φ hφ hU ψ hψ q hq hq0 hqm v hv vP hvP
      haveI : q.IsMaximal := hq.isMaximal hq0
      haveI : (q.under (𝓞 K)).IsMaximal := hqKp.isMaximal hqK0
      have hw' : w = vP ^ Ideal.inertiaDeg (q.under (𝓞 K)) q := Subtype.ext (Units.ext (by
        rw [hw, Ideal.relNorm_eq_pow_of_isMaximal q (q.under (𝓞 K)),
          FractionalIdeal.coeIdeal_pow, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hvP]))
      rw [hw', map_pow]
      exact h1
    · intro C D hC hD hCm hDm ihC ihD v hv w hw
      obtain ⟨vC, hvC⟩ := exists_coprimeIdealUnit E (m.map (algebraMap (𝓞 K) (𝓞 E))) C hC hCm
      obtain ⟨vD, hvD⟩ := exists_coprimeIdealUnit E (m.map (algebraMap (𝓞 K) (𝓞 E))) D hD hDm
      obtain ⟨wC, hwC⟩ := exists_coprime_relNorm_unit K E m C hC hCm
      obtain ⟨wD, hwD⟩ := exists_coprime_relNorm_unit K E m D hD hDm
      have hv' : v = vC * vD := Subtype.ext (Units.ext (by
        rw [hv, Subgroup.coe_mul, Units.val_mul, hvC, hvD, FractionalIdeal.coeIdeal_mul]))
      have hw' : w = wC * wD := Subtype.ext (Units.ext (by
        rw [hw, Subgroup.coe_mul, Units.val_mul, hwC, hwD, map_mul,
          FractionalIdeal.coeIdeal_mul]))
      rw [hv', hw', map_mul, map_mul, ihC vC hvC wC hwC, ihD vD hvD wD hwD]
  obtain ⟨vA, hvA⟩ := exists_coprimeIdealUnit E (m.map (algebraMap (𝓞 K) (𝓞 E))) A hA hAm
  obtain ⟨vB, hvB⟩ := exists_coprimeIdealUnit E (m.map (algebraMap (𝓞 K) (𝓞 E))) B hB hBm
  obtain ⟨wA, hwA⟩ := exists_coprime_relNorm_unit K E m A hA hAm
  obtain ⟨wB, hwB⟩ := exists_coprime_relNorm_unit K E m B hB hBm
  have huv : u * vB = vA := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, hvB, hvA, hu]))
  have hNw : uN * wB = wA := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, hwB, hwA, hN]))
  have hA' := key A hA hAm vA hvA wA hwA
  have hB' := key B hB hBm vB hvB wB hwB
  have h1 : θ u * θ vB = φ uN * φ wB := by
    rw [← map_mul, ← map_mul, huv, hNw, hA']
  rw [hB'] at h1
  exact mul_right_cancel h1

end Cox.ClassFieldTheory
