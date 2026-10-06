import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Basic

/-!
# The standard polynomial projective line

This file independently constructs `Proj ℂ[X₀, X₁]`, proves it is integral, and exhibits
the nonempty affine coordinate open `D₊(X₀)`. It makes no identification with a modular
curve. The general integral-`Proj` argument is adapted from AINTLIB's Apache-2.0
`ForMathlib/ProjIntegral.lean` by the AINTLIB ModularCurves contributors.
-/

open AlgebraicGeometry HomogeneousLocalization ProjectiveSpectrum TopologicalSpace

namespace MMeromorphicTest.P1

section IntegralProj

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsDomain A]

/-- The degree-zero homogeneous localization of a domain is reduced. -/
theorem isReduced_away (f : A) : _root_.IsReduced (Away 𝒜 f) :=
  isReduced_of_injective
    (algebraMap (Away 𝒜 f) (Localization (Submonoid.powers f)))
    (HomogeneousLocalization.val_injective _)

/-- A graded domain with a nonzero positive-degree element has integral `Proj`. -/
theorem isIntegral_proj (h : ∃ i, 0 < i ∧ ∃ x ∈ 𝒜 i, x ≠ 0) :
    IsIntegral (Proj 𝒜) := by
  have hrel : ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ (⊥ : HomogeneousIdeal 𝒜) := by
    obtain ⟨i, hi, x, hx, hx0⟩ := h
    rw [SetLike.not_le_iff_exists]
    exact ⟨x, HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi hx,
      fun hc ↦ hx0 (Ideal.mem_bot.mp hc)⟩
  let p : ProjectiveSpectrum 𝒜 := ⟨⊥, Ideal.isPrime_bot, hrel⟩
  haveI : IsReduced (Proj 𝒜) := by
    haveI : ∀ i, IsReduced ((Proj.affineOpenCover 𝒜).openCover.X i) := by
      intro i
      change IsReduced (Spec ((Proj.affineOpenCover 𝒜).X i))
      haveI : _root_.IsReduced (↥((Proj.affineOpenCover 𝒜).X i)) := isReduced_away 𝒜 _
      infer_instance
    exact IsReduced.of_openCover _ (Proj.affineOpenCover 𝒜).openCover
  have hclosure : closure ({p} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    exact ProjectiveSpectrum.zeroLocus_bot 𝒜
  haveI hirr : IrreducibleSpace (ProjectiveSpectrum 𝒜) := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hclosure]
    exact isIrreducible_singleton.closure
  haveI : IrreducibleSpace (Proj 𝒜) := hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end IntegralProj

/-- The homogeneous polynomial ring in the two projective coordinates. -/
abbrev coordinateRing := MvPolynomial (Fin 2) ℂ

/-- The total-degree grading of the two-variable polynomial ring. -/
abbrev grading := MvPolynomial.homogeneousSubmodule (Fin 2) ℂ

noncomputable instance grading_gradedAlgebra : GradedAlgebra grading :=
  MvPolynomial.gradedAlgebra

theorem coordinate_mem_grading_one (i : Fin 2) : MvPolynomial.X i ∈ grading 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _)

/-- The standard projective line over the complex numbers. -/
noncomputable def scheme : Scheme := Proj grading

instance scheme_isIntegral : IsIntegral scheme :=
  isIntegral_proj grading ⟨1, one_pos, MvPolynomial.X (0 : Fin 2),
    coordinate_mem_grading_one 0, MvPolynomial.X_ne_zero 0⟩

/-- The affine chart where the first homogeneous coordinate is nonzero. -/
noncomputable def standardOpen : scheme.Opens :=
  Proj.basicOpen grading (MvPolynomial.X (0 : Fin 2))

theorem standardOpen_isAffineOpen : IsAffineOpen standardOpen :=
  Proj.isAffineOpen_basicOpen grading (MvPolynomial.X (0 : Fin 2))
    (coordinate_mem_grading_one 0) one_pos

private theorem irrelevant_not_le_bot :
    ¬ HomogeneousIdeal.irrelevant grading ≤ (⊥ : HomogeneousIdeal grading) := by
  intro h
  have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem grading one_pos
    (coordinate_mem_grading_one 0))
  exact MvPolynomial.X_ne_zero (0 : Fin 2) (Ideal.mem_bot.mp hx)

/-- The zero homogeneous prime is a point of this projective line. -/
def zeroPrime : scheme := ⟨⊥, Ideal.isPrime_bot, irrelevant_not_le_bot⟩

theorem zeroPrime_mem_standardOpen : zeroPrime ∈ standardOpen := by
  change MvPolynomial.X (0 : Fin 2) ∉ (⊥ : HomogeneousIdeal grading)
  exact fun h ↦ MvPolynomial.X_ne_zero (0 : Fin 2) (Ideal.mem_bot.mp h)

theorem standardOpen_nonempty : (standardOpen : Set scheme).Nonempty :=
  ⟨zeroPrime, zeroPrime_mem_standardOpen⟩

instance standardOpen_instNonempty : Nonempty standardOpen :=
  ⟨⟨zeroPrime, zeroPrime_mem_standardOpen⟩⟩

example : IsIntegral scheme := inferInstance

example : Nonempty standardOpen := inferInstance

#print axioms isIntegral_proj
#print axioms scheme_isIntegral
#print axioms standardOpen_isAffineOpen
#print axioms standardOpen_nonempty

end MMeromorphicTest.P1
