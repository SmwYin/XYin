import XYin.PhD.Test.MMeromorphic.P1Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.FiniteType

/-!
# Properness of the standard polynomial projective line

The chosen scheme `Proj ℂ[X₀, X₁]` has an actual structure morphism to `Spec ℂ`, and that
morphism is proper. This is an algebraic property of the chosen model; identifying it with
the classical analytic compactification still requires the quotient and cusp bridges.

The structure-map formula follows AINTLIB's Apache-2.0
`ForMathlib/MvPolynomialProjectiveClosure.lean` by the AINTLIB ModularCurves contributors.
The finite-generation proof below uses the pinned mathlib degree-zero calculation directly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace MMeromorphicTest.P1

/-- Degree-zero homogeneous polynomials form the module spanned by the constant `1`. -/
instance gradeZero_finite : Module.Finite ℂ (grading 0) := by
  apply Module.Finite.of_fg
  rw [grading, MvPolynomial.homogeneousSubmodule_zero, Submodule.one_eq_span]
  exact Submodule.fg_span_singleton 1

/-- The coefficient algebra and the degree-zero algebra have their natural common action. -/
instance gradeZero_scalarTower : IsScalarTower ℂ (grading 0) coordinateRing :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := grading 0) (A := coordinateRing)
    (by ext r; rfl)

/-- The finite polynomial generators also generate over the degree-zero ring. -/
instance coordinateRing_finiteType_gradeZero : Algebra.FiniteType (grading 0) coordinateRing :=
  Algebra.FiniteType.of_restrictScalars_finiteType ℂ (grading 0) coordinateRing

/-- The morphism from the degree-zero coefficient spectrum to `Spec ℂ`. -/
def coefficientMap : Spec (CommRingCat.of (grading 0)) ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (grading 0)))

instance coefficientMap_isFinite : IsFinite coefficientMap := by
  rw [coefficientMap, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The projective line's structure morphism over the complex coefficient field. -/
def structureMap : scheme ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero grading ≫ coefficientMap

instance structureMap_isProper : IsProper structureMap := by
  have hproj : IsProper (Proj.toSpecZero grading) := inferInstance
  have hbase : IsProper coefficientMap := inferInstance
  exact MorphismProperty.IsStableUnderComposition.comp_mem
    (P := @IsProper) (Proj.toSpecZero grading) coefficientMap hproj hbase

example : IsProper (Proj.toSpecZero grading) := inferInstance

example : IsProper coefficientMap := inferInstance

example : IsProper structureMap := inferInstance

#print axioms gradeZero_finite
#print axioms coordinateRing_finiteType_gradeZero
#print axioms coefficientMap_isFinite
#print axioms structureMap_isProper

end MMeromorphicTest.P1
