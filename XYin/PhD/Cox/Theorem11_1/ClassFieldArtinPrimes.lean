/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldIdealGroups
import XYin.PhD.Cox.Theorem11_1.ChebotarevFrobenius

/-! # Primewise arithmetic Artin conditions

Janusz III.2 identifies arithmetic Frobenius through its action on residues; III.3 extends equality
from good primes multiplicatively. The representative prime ideal and quotient cardinality are kept
explicit.
-/

open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]
variable (m : Ideal (𝓞 K))

/-- Homomorphisms from the good-ideal group agree if they agree on good primes. -/
theorem coprimeIdeals_hom_ext {G : Type*} [Monoid G] (φ ψ : coprimeIdeals K m →* G)
    (h : ∀ (q : Ideal (𝓞 K)), q.IsPrime → q ≠ ⊥ → q ⊔ m = ⊤ →
      ∀ u : coprimeIdeals K m,
        ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q →
        φ u = ψ u) : φ = ψ := by
  set H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    (MonoidHom.eqLocus φ ψ).map (coprimeIdeals K m).subtype
  have hle : coprimeIdeals K m ≤ H := by
    refine (coprimeIdeals_eq_closure_primes K m).trans_le ((Subgroup.closure_le H).mpr ?_)
    rintro u ⟨q, hq, hq0, hqm, hu⟩
    have hmem : u ∈ coprimeIdeals K m := Subgroup.subset_closure ⟨q, hq0, hqm, hu⟩
    exact ⟨⟨u, hmem⟩, h q hq hq0 hqm ⟨u, hmem⟩ hu, rfl⟩
  ext x
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle x.2)
  obtain rfl : y = x := Subtype.ext hyx
  exact hy

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]

omit [NumberField L] in
/-- The defining prime congruence gives the actual restricted arithmetic Frobenius. -/
theorem isArtinMap_isArithFrobAt
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ)
    {q : Ideal (𝓞 K)} (hq : q.IsPrime) (hq0 : q ≠ ⊥) (hmq : q ⊔ m = ⊤)
    (u : coprimeIdeals K m)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q)
    (P : Ideal (𝓞 L)) (hP : P ∈ q.primesOver (𝓞 L)) :
    (RingOfIntegers.mapAlgHom (φ u)).IsArithFrobAt P := by
  have hLO : P.LiesOver q := hP.2
  intro x
  have hcard : Nat.card (𝓞 K ⧸ P.under (𝓞 K)) = q.absNorm := by
    rw [← Ideal.over_def P q, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard]
  exact hφ q hq hq0 hmq u hu P hP x

/-- At a good prime, the order of its Artin element is the relative residue degree. -/
theorem orderOf_artin_eq_inertiaDeg [IsGalois K L]
    (hU : IsUnramifiedAway K m L)
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ)
    {q : Ideal (𝓞 K)} (hq : q.IsPrime) (hq0 : q ≠ ⊥) (hmq : q ⊔ m = ⊤)
    (u : coprimeIdeals K m)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q)
    (P : Ideal (𝓞 L)) (hP : P ∈ q.primesOver (𝓞 L)) :
    orderOf (φ u) = Ideal.inertiaDeg q P := by
  have hPp : P.IsPrime := hP.1
  have hLO : P.LiesOver q := hP.2
  have hram : Ideal.ramificationIdx (P.under (𝓞 K)) P = 1 := by
    rw [← Ideal.over_def P q]
    exact hU q hq hq0 hmq P hP
  have hfrob : IsArithFrobAt (𝓞 K) (φ u) P :=
    isArtinMap_isArithFrobAt K m L φ hφ hq hq0 hmq u hu P hP
  have hmax : (P.under (𝓞 K)).IsMaximal := by
    rw [← Ideal.over_def P q]
    exact hq.isMaximal hq0
  rw [Chebotarev.orderOf_eq_finrank_of_isArithFrobAt K L (φ u) P hram hfrob,
    ← Ideal.inertiaDeg_algebraMap (P.under (𝓞 K)) P, ← Ideal.over_def P q]

/-- The unramified Frobenius uniqueness theorem identifies two prime Artin values. -/
theorem isArtinMap_prime_eq [IsGalois K L]
    (hU : IsUnramifiedAway K m L)
    (φ ψ : coprimeIdeals K m →* (L ≃ₐ[K] L))
    (hφ : IsArtinMap K m L φ) (hψ : IsArtinMap K m L ψ)
    {q : Ideal (𝓞 K)} (hq : q.IsPrime) (hq0 : q ≠ ⊥) (hmq : q ⊔ m = ⊤)
    (u : coprimeIdeals K m)
    (hu : ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = q) :
    φ u = ψ u := by
  have hqmax : q.IsMaximal := hq.isMaximal hq0
  obtain ⟨P, hP⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) q
  have hPp : P.IsPrime := hP.1
  have hLO : P.LiesOver q := hP.2
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq0 P
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  have : Algebra.IsUnramifiedAt (𝓞 K) P := by
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP0, ← Ideal.over_def P q]
    exact hU q hq hq0 hmq P hP
  rw [Chebotarev.eq_arithFrobAt_of_isArithFrobAt K L P (φ u)
      (isArtinMap_isArithFrobAt K m L φ hφ hq hq0 hmq u hu P hP),
    Chebotarev.eq_arithFrobAt_of_isArithFrobAt K L P (ψ u)
      (isArtinMap_isArithFrobAt K m L ψ hψ hq hq0 hmq u hu P hP)]

end Cox.ClassFieldTheory
