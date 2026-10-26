/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselIdempotent
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselResidueCRT
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselLiftComparison
import XYin.PhD.Cox.Theorem11_1.ClassFieldHenselResidueComparison

/-! # Hensel factor lifting and the local degree comparison

Source: Janusz II.3.5 and V.9.3.
-/

noncomputable section
open Polynomial IsLocalRing
namespace Cox.ClassFieldTheory

attribute [local instance] Ideal.Quotient.field

/-- Lift an actual coprime pair of monic residue factors through the source idempotent
decomposition. -/
theorem exists_monic_factors_of_coprime_map
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (hf : f.Monic) (g h : (R ⧸ I)[X]) (hg : g.Monic) (hh : h.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = g * h) (hcop : IsCoprime g h) :
    ∃ G H : R[X], G.Monic ∧ H.Monic ∧ f = G * H ∧
      G.map (Ideal.Quotient.mk I) = g ∧ H.map (Ideal.Quotient.mk I) = h := by
  let A := AdjoinRoot f
  letI := hf.free_adjoinRoot
  letI := hf.finite_adjoinRoot
  obtain ⟨Ebar, hroot⟩ := exists_adjoinRoot_residue_mul_algEquiv f I g h hfactor hcop
  obtain ⟨e, he, hres⟩ := exists_idempotent_lift_product R A (AdjoinRoot g) (AdjoinRoot h) I Ebar
  let B := A ⧸ Ideal.span {e}
  let C := A ⧸ Ideal.span {1 - e}
  obtain ⟨E, hE⟩ := exists_idempotent_quotient_algEquiv R A e he
  letI : Module.Free R B := moduleFree_factor_of_linearEquiv_prod R A B C E.toLinearEquiv
  letI : Module.Free R C := moduleFree_factor_of_linearEquiv_prod R A C B
    (E.toLinearEquiv.trans (LinearEquiv.prodComm R B C))
  letI : Module.Finite R B := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ R (Ideal.span {e})).toLinearMap Ideal.Quotient.mk_surjective
  letI : Module.Finite R C := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})).toLinearMap Ideal.Quotient.mk_surjective
  let x := AdjoinRoot.root f
  let xB : B := Ideal.Quotient.mk _ x
  let xC : C := Ideal.Quotient.mk _ x
  let G := (Algebra.lmul R B xB).charpoly
  let H := (Algebra.lmul R C xC).charpoly
  have hprod : f = G * H := by
    have hp := charpoly_lmul_eq_prod_of_algEquiv E x
    rw [charpoly_adjoinRoot_mul_root f hf, hE] at hp
    exact hp
  have hG : G.map (Ideal.Quotient.mk I) = g := by
    obtain ⟨F, hF⟩ := exists_residue_factor_algEquiv R A (AdjoinRoot g) (AdjoinRoot h)
      I Ebar e hres
    apply charpoly_lmul_map_eq_of_residue_root I g hg F xB
    change F (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) = AdjoinRoot.root g
    rw [hF, hroot]
  have hH : H.map (Ideal.Quotient.mk I) = h := by
    let swap : (AdjoinRoot g × AdjoinRoot h) ≃ₐ[R ⧸ I] (AdjoinRoot h × AdjoinRoot g) :=
      AlgEquiv.ofRingEquiv (f := RingEquiv.prodComm) (fun _ => rfl)
    have hs : (Ebar.trans swap) (Ideal.Quotient.mk _ (1 - e)) = (0, 1) := by
      have hr : swap (Ebar (Ideal.Quotient.mk _ e)) = (1, 0) :=
        congrArg swap hres
      calc
        (Ebar.trans swap) (Ideal.Quotient.mk _ (1 - e)) =
            1 - swap (Ebar (Ideal.Quotient.mk _ e)) := by
              simp only [map_sub, map_one, AlgEquiv.trans_apply]
        _ = 1 - (1, 0) := congrArg (fun z => 1 - z) hr
        _ = (0, 1) := by ext <;> simp
    obtain ⟨F, hF⟩ := exists_residue_factor_algEquiv R A (AdjoinRoot h) (AdjoinRoot g)
      I (Ebar.trans swap) (1-e) hs
    apply charpoly_lmul_map_eq_of_residue_root I h hh F xC
    change F (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) = AdjoinRoot.root h
    rw [hF, AlgEquiv.trans_apply, hroot]
    rfl
  exact ⟨G, H, LinearMap.charpoly_monic _, LinearMap.charpoly_monic _, hprod, hG, hH⟩

end Cox.ClassFieldTheory
