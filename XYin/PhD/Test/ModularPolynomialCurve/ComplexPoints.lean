/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import XYin.PhD.Test.ModularPolynomialCurve.PlaneModel

/-!
# Actual complex points of the modular-polynomial plane scheme

The plane equation's zeros identify both the coordinate ring's complex algebra points
and the scheme morphisms `Spec ℂ ⟶ planeScheme N` over `Spec ℂ`. The underlying prime
spectrum is not identified with the set of complex points.
-/

open CategoryTheory AlgebraicGeometry Polynomial
open scoped Polynomial.Bivariate

noncomputable section

namespace ModularPolynomialCurveTest.ComplexPoints

open Cox

/-- Complex algebra points of the independent coordinate ring. -/
abbrev AlgebraPoint (N : ℕ+) := planeRing N →ₐ[ℂ] ℂ

/-- Evaluation of both formal variables, using the existing bivariate universal property. -/
def evalPair (v u : ℂ) : ℂ[X][Y] →ₐ[ℂ] ℂ :=
  aevalAeval v u

@[simp]
theorem evalPair_apply (v u : ℂ) (P : ℂ[X][Y]) :
    evalPair v u P = P.evalEval v u :=
  congrFun (coe_aevalAeval_eq_evalEval v u) P

/-- The equation's vanishing makes evaluation factor through the coordinate ring. -/
def algebraPointOfPlanePoint (N : ℕ+) (p : planePoints N) : AlgebraPoint N :=
  Ideal.Quotient.liftₐ (definingIdeal N) (evalPair p.val.1 p.val.2) fun P hP ↦ by
    obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton.mp hP
    simp only [map_mul, evalPair_apply, p.property, zero_mul]

@[simp]
theorem algebraPointOfPlanePoint_mk (N : ℕ+) (p : planePoints N) (P : ℂ[X][Y]) :
    algebraPointOfPlanePoint N p (Ideal.Quotient.mk (definingIdeal N) P) =
      P.evalEval p.val.1 p.val.2 := by
  rw [algebraPointOfPlanePoint, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
    AlgHom.coe_toRingHom, evalPair_apply]

/-- The two geometric coordinates of a complex algebra point. -/
def coordinates (N : ℕ+) (p : AlgebraPoint N) : ℂ × ℂ :=
  (aevalAevalEquiv ℂ ℂ).symm (p.comp (Ideal.Quotient.mkₐ ℂ (definingIdeal N)))

@[simp]
theorem coordinates_fst (N : ℕ+) (p : AlgebraPoint N) :
    (coordinates N p).1 = p (Ideal.Quotient.mk (definingIdeal N) (C X)) := rfl

@[simp]
theorem coordinates_snd (N : ℕ+) (p : AlgebraPoint N) :
    (coordinates N p).2 = p (Ideal.Quotient.mk (definingIdeal N) X) := rfl

/-- An algebra point evaluates every polynomial at its two coordinates. -/
theorem algebraPoint_apply_mk (N : ℕ+) (p : AlgebraPoint N) (P : ℂ[X][Y]) :
    p (Ideal.Quotient.mk (definingIdeal N) P) =
      P.evalEval (coordinates N p).1 (coordinates N p).2 := by
  have h : evalPair (coordinates N p).1 (coordinates N p).2 =
      p.comp (Ideal.Quotient.mkₐ ℂ (definingIdeal N)) :=
    (aevalAevalEquiv ℂ ℂ).apply_symm_apply
      (p.comp (Ideal.Quotient.mkₐ ℂ (definingIdeal N)))
  simpa only [evalPair_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using
    (AlgHom.congr_fun h P).symm

/-- The defining equation holds at the coordinates of every algebra point. -/
theorem coordinates_equation (N : ℕ+) (p : AlgebraPoint N) :
    (modularPolynomialC N).evalEval (coordinates N p).1 (coordinates N p).2 = 0 := by
  rw [← algebraPoint_apply_mk]
  have h : Ideal.Quotient.mk (definingIdeal N) (modularPolynomialC N) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [h, map_zero]

/-- An algebra point determines a point of the independently defined plane equation. -/
def planePointOfAlgebra (N : ℕ+) (p : AlgebraPoint N) : planePoints N :=
  ⟨coordinates N p, coordinates_equation N p⟩

/-- Complex algebra points are exactly the plane equation's zeros. -/
def algebraPointEquiv (N : ℕ+) : AlgebraPoint N ≃ planePoints N where
  toFun := planePointOfAlgebra N
  invFun := algebraPointOfPlanePoint N
  left_inv p := by
    apply Ideal.Quotient.algHom_ext
    rw [algebraPointOfPlanePoint, Ideal.Quotient.liftₐ_comp]
    exact (aevalAevalEquiv ℂ ℂ).apply_symm_apply
      (p.comp (Ideal.Quotient.mkₐ ℂ (definingIdeal N)))
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> simp [planePointOfAlgebra, coordinates,
      aevalAevalEquiv_symm_apply, algebraPointOfPlanePoint_mk, evalEval_C]

/-- The base scheme for complex-valued scheme points. -/
abbrev complexBase : Scheme := Spec (.of ℂ)

/-- The actual structure morphism of the plane scheme. -/
def structureMap (N : ℕ+) : planeScheme N ⟶ complexBase :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (planeRing N)))

/-- Complex-valued scheme points with the required commuting triangle over the base. -/
abbrev SchemePoint (N : ℕ+) :=
  {p : complexBase ⟶ planeScheme N // p ≫ structureMap N = 𝟙 complexBase}

/-- The contravariant `Spec` morphism induced by a complex algebra point. -/
def schemePointOfAlgebra (N : ℕ+) (p : AlgebraPoint N) : SchemePoint N :=
  ⟨Spec.map (CommRingCat.ofHom p.toRingHom), by
    change Spec.map (CommRingCat.ofHom p.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (planeRing N))) = 𝟙 (Spec (.of ℂ))
    rw [← Spec.map_comp, Spec.map_eq_id]
    ext z
    exact p.commutes z⟩

/-- The commuting triangle makes the corresponding ring homomorphism complex-linear. -/
def algebraPointOfScheme (N : ℕ+) (p : SchemePoint N) : AlgebraPoint N where
  toRingHom := (Spec.preimage p.val).hom
  commutes' z := by
    have h := congrArg Spec.preimage p.property
    simp only [structureMap, planeScheme, Spec.preimage_comp, Spec.preimage_map,
      Spec.preimage_id] at h
    exact congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ f z) h

/-- Actual scheme points over the base agree with complex algebra points. -/
def algebraSchemePointEquiv (N : ℕ+) : AlgebraPoint N ≃ SchemePoint N where
  toFun := schemePointOfAlgebra N
  invFun := algebraPointOfScheme N
  left_inv p := by
    apply AlgHom.ext
    intro q
    change (Spec.preimage (Spec.map (CommRingCat.ofHom p.toRingHom))).hom q = p q
    rw [Spec.preimage_map]
    rfl
  right_inv p := by
    apply Subtype.ext
    change Spec.map (Spec.preimage p.val) = p.val
    exact Spec.map_preimage p.val

/-- Actual scheme morphisms over `Spec ℂ` are exactly the plane equation's zeros. -/
def schemePointEquiv (N : ℕ+) : SchemePoint N ≃ planePoints N :=
  (algebraSchemePointEquiv N).symm.trans (algebraPointEquiv N)

/-- A zero of the plane equation gives an actual scheme point over `Spec ℂ`. -/
def schemePointOfPlanePoint (N : ℕ+) (p : planePoints N) : SchemePoint N :=
  (schemePointEquiv N).symm p

@[simp]
theorem schemePointEquiv_fst (N : ℕ+) (p : SchemePoint N) :
    ((schemePointEquiv N) p).val.1 =
      (Spec.preimage p.val).hom (Ideal.Quotient.mk (definingIdeal N) (C X)) := rfl

@[simp]
theorem schemePointEquiv_snd (N : ℕ+) (p : SchemePoint N) :
    ((schemePointEquiv N) p).val.2 =
      (Spec.preimage p.val).hom (Ideal.Quotient.mk (definingIdeal N) X) := rfl

example (N : ℕ+) (p : planePoints N) :
    schemePointEquiv N (schemePointOfPlanePoint N p) = p :=
  (schemePointEquiv N).apply_symm_apply p

example (N : ℕ+) (p : SchemePoint N) :
    schemePointOfPlanePoint N (schemePointEquiv N p) = p :=
  (schemePointEquiv N).symm_apply_apply p

example (N : ℕ+) (p : planePoints N) :
    (schemePointOfPlanePoint N p).val ≫ structureMap N = 𝟙 complexBase :=
  (schemePointOfPlanePoint N p).property

#print axioms algebraPointEquiv
#print axioms algebraSchemePointEquiv
#print axioms schemePointEquiv

end ModularPolynomialCurveTest.ComplexPoints
