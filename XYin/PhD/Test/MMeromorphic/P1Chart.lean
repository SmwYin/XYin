import XYin.PhD.Test.MMeromorphic.P1Basic
import XYin.PhD.Test.MMeromorphic.P1ChartRing
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The affine polynomial chart of the standard projective-line model

The independently defined scheme `Proj ℂ[X₀, X₁]` has a nonempty affine chart `D₊(X₀)`.
This file identifies its section ring with `ℂ[X]`, with chart coordinate `X₁ / X₀`.
It concerns the standard projective-line model; it does not assert an identification with
an existing AINTLIB object called `X₁` or construct an analytic compactification.
-/

open AlgebraicGeometry HomogeneousLocalization

namespace MMeromorphicTest.P1

noncomputable section

private instance otherCoordinateUnique : Unique {j : Fin 2 // j ≠ 0} where
  default := ⟨1, by decide⟩
  uniq j := by
    apply Subtype.ext
    apply Fin.ext
    have hj : j.val.val ≠ 0 := fun h ↦ j.property (Fin.ext h)
    have hjlt := j.val.isLt
    change j.val.val = 1
    omega

/-- The degree-zero localization on the chart where `X₀` is nonzero. -/
abbrev chartRing := Away grading (MvPolynomial.X (0 : Fin 2))

/-- The standard coordinate on the affine chart is `X₁ / X₀`. -/
def affineCoordinate : chartRing := Chart.awayVar ℂ (0 : Fin 2) ⟨1, by decide⟩

/-- The homogeneous-localization chart ring is a polynomial ring in one variable. -/
def chartRingEquiv : chartRing ≃+* Polynomial ℂ :=
  (Chart.chartRingEquiv ℂ (0 : Fin 2)).trans
    (MvPolynomial.uniqueAlgEquiv ℂ {j : Fin 2 // j ≠ 0}).toRingEquiv

/-- The chart equivalence sends the geometric ratio to the polynomial variable. -/
@[simp]
theorem chartRingEquiv_affineCoordinate : chartRingEquiv affineCoordinate = Polynomial.X := by
  simp [chartRingEquiv, affineCoordinate, MvPolynomial.uniqueAlgEquiv]

/-- The degree-zero localization is the ring of sections on the standard affine chart. -/
def standardOpenAwayRingEquiv : chartRing ≃+* Γ(scheme, standardOpen) :=
  (Proj.basicOpenIsoAway grading (MvPolynomial.X (0 : Fin 2))
    (coordinate_mem_grading_one 0) one_pos).commRingCatIsoToRingEquiv

/-- The sections on the standard affine chart form the polynomial ring `ℂ[X]`. -/
def standardOpenSectionRingEquiv : Γ(scheme, standardOpen) ≃+* Polynomial ℂ :=
  standardOpenAwayRingEquiv.symm.trans chartRingEquiv

/-- Complex coefficients embed into the chart ring as constant fractions. -/
instance chartComplexAlgebra : Algebra ℂ chartRing := Chart.chartAlgebra ℂ (0 : Fin 2)

/-- The standard chart ring is a complex polynomial algebra. -/
def chartAlgEquiv : chartRing ≃ₐ[ℂ] Polynomial ℂ :=
  (Chart.chartAlgEquiv ℂ (0 : Fin 2)).trans
    (MvPolynomial.uniqueAlgEquiv ℂ {j : Fin 2 // j ≠ 0})

/-- Complex constants on the standard open are the sections given by constant fractions. -/
instance standardOpenComplexAlgebra : Algebra ℂ Γ(scheme, standardOpen) :=
  (standardOpenAwayRingEquiv.toRingHom.comp (Chart.awayConstHom ℂ (0 : Fin 2))).toAlgebra

/-- The polynomial chart identification respects the complex constants. -/
def standardOpenSectionAlgEquiv : Γ(scheme, standardOpen) ≃ₐ[ℂ] Polynomial ℂ where
  __ := standardOpenSectionRingEquiv
  commutes' c := by
    change chartRingEquiv
      (standardOpenAwayRingEquiv.symm
        (standardOpenAwayRingEquiv (Chart.awayConst ℂ (0 : Fin 2) c))) = Polynomial.C c
    rw [standardOpenAwayRingEquiv.symm_apply_apply]
    exact chartAlgEquiv.commutes c

example (c : ℂ) :
    standardOpenSectionAlgEquiv (algebraMap ℂ Γ(scheme, standardOpen) c) = Polynomial.C c :=
  standardOpenSectionAlgEquiv.commutes c

example : IsAffineOpen standardOpen := standardOpen_isAffineOpen

example : Nonempty standardOpen := inferInstance

#print axioms chartRingEquiv
#print axioms chartRingEquiv_affineCoordinate
#print axioms standardOpenSectionRingEquiv
#print axioms chartAlgEquiv
#print axioms standardOpenSectionAlgEquiv

end

end MMeromorphicTest.P1
