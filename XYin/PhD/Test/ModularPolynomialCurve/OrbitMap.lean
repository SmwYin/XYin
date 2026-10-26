/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Test.ModularPolynomialCurve.PlaneModel

/-!
# The orbit quotient maps onto the modular-polynomial plane curve

The pair `(j(τ), j(Nτ))` is invariant under `Γ₀(N)` and descends to mathlib's actual
group-orbit quotient. Every complex zero of `Φ_N` is represented by this pair.
These statements concern the analytic orbit quotient and the plane equation's points;
they do not identify that plane curve with a coarse moduli scheme or its normalization.
-/

open UpperHalfPlane MatrixGroups

noncomputable section

namespace ModularPolynomialCurveTest

open Cox

/-- The analytic quotient underlying `Y₀(N)`, using the existing subgroup action. -/
abbrev gamma0Orbits (N : ℕ+) :=
  MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 (N : ℕ)) ℍ

@[simp]
theorem jPair_fst (N : ℕ+) (τ : ℍ) : (jPair N τ).val.1 = j τ := rfl

@[simp]
theorem jPair_snd (N : ℕ+) (τ : ℍ) : (jPair N τ).val.2 = levelJ N τ := rfl

/-- Both coordinates are invariant under the same `Γ₀(N)` action. -/
theorem jPair_smul (N : ℕ+) (γ : CongruenceSubgroup.Gamma0 (N : ℕ)) (τ : ℍ) :
    jPair N (γ • τ) = jPair N τ := by
  apply Subtype.ext
  exact Prod.ext (j_modularGroup_smul (γ : SL(2, ℤ)) τ)
    ((levelJ_cuspData N).apply_smul γ τ)

/-- Every point of the plane equation is a j-pair of a point of the upper half-plane. -/
theorem jPair_surjective (N : ℕ+) : Function.Surjective (jPair N) := by
  intro p
  obtain ⟨τ, hτ⟩ := j_surjective p.val.1
  have hroot : (modularPolynomialC N).evalEval (j τ) p.val.2 = 0 := by
    rw [hτ]
    exact p.property
  obtain ⟨σ, hσ⟩ := (modularPolynomialC_evalEval_eq_zero_iff N τ p.val.2).mp hroot
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep (coxMatrixEquivRightCosets N σ)
  change Quotient.mk'' γ = coxMatrixEquivRightCosets N σ at hγ
  refine ⟨γ • τ, Subtype.ext <| Prod.ext ?_ ?_⟩
  · exact (j_modularGroup_smul γ τ).trans hτ
  · change levelJ N (γ • τ) = p.val.2
    rw [← rightCosetEval_mk, hγ, rightCosetEval_equiv]
    exact hσ.symm

/-- The j-pair is constant on the existing orbit equivalence relation. -/
theorem jPair_eq_of_orbitRel (N : ℕ+) {τ η : ℍ}
    (h : MulAction.orbitRel (CongruenceSubgroup.Gamma0 (N : ℕ)) ℍ τ η) :
    jPair N τ = jPair N η := by
  obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  exact jPair_smul N γ η

/-- The descended j-pair map from the analytic orbit quotient to the plane curve's points. -/
def orbitMap (N : ℕ+) : gamma0Orbits N → planePoints N :=
  Quotient.lift (jPair N) fun _ _ h ↦ jPair_eq_of_orbitRel N h

@[simp]
theorem orbitMap_mk (N : ℕ+) (τ : ℍ) :
    orbitMap N (Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 (N : ℕ)) ℍ) τ) =
      jPair N τ := rfl

/-- The descended j-pair map is surjective. -/
theorem orbitMap_surjective (N : ℕ+) : Function.Surjective (orbitMap N) := by
  intro p
  obtain ⟨τ, rfl⟩ := jPair_surjective N p
  exact ⟨Quotient.mk _ τ, rfl⟩

/-- The quotient coordinates still satisfy the original defining equation. -/
theorem orbitMap_equation (N : ℕ+) (q : gamma0Orbits N) :
    (modularPolynomialC N).evalEval (orbitMap N q).val.1 (orbitMap N q).val.2 = 0 :=
  (orbitMap N q).property

example (N : ℕ+) (τ : ℍ) :
    (orbitMap N (Quotient.mk _ τ)).val = (j τ, levelJ N τ) := rfl

example (N : ℕ+) (v u : ℂ) (h : (modularPolynomialC N).evalEval v u = 0) :
    ∃ q : gamma0Orbits N, (orbitMap N q).val = (v, u) := by
  obtain ⟨q, hq⟩ := orbitMap_surjective N ⟨(v, u), h⟩
  exact ⟨q, congrArg Subtype.val hq⟩

#print axioms jPair_smul
#print axioms jPair_surjective
#print axioms orbitMap_surjective

end ModularPolynomialCurveTest
