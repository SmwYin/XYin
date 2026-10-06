/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarseFiniteType
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Reducedness of the actual AINTLIB `YZeroCoarse`

A smooth algebra over a domain is reduced: locally it is standard étale over a polynomial
ring, and an étale algebra over a domain embeds into its reduced generic fibre by flatness.
Only the original base ring is assumed to be a domain. The full-level section ring itself
may have zero divisors and may be disconnected.

We apply this to the actual smooth full-level representing scheme. The actual Borel
invariant-ring inclusion is injective, so its invariant ring and the actual coarse scheme
are reduced as well. Over `ℂ` the base-domain and level-invertibility requirements are automatic.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

namespace ReducednessDescent

/-- Étale algebras over a domain are reduced; the algebra need not be a domain. -/
theorem isReduced_of_etale_over_domain
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] : _root_.IsReduced A := by
  let K := FractionRing R
  let f := Algebra.TensorProduct.includeRight (R := R) (A := K) (B := A)
  have : _root_.IsReduced (K ⊗[R] A) := Algebra.FormallyUnramified.isReduced_of_field K _
  have hf : Function.Injective f := by
    have hmap : ⇑f = (LinearMap.rTensor A (Algebra.ofId R K).toLinearMap).comp
        (Algebra.TensorProduct.lid R A).symm.toLinearMap := by
      ext x
      simp [f]
    rw [hmap]
    suffices h : Function.Injective
        (LinearMap.rTensor A (Algebra.ofId R K).toLinearMap) from
      h.comp (Algebra.TensorProduct.lid R A).symm.injective
    apply Module.Flat.rTensor_preserves_injective_linearMap
    exact IsFractionRing.injective R K
  exact isReduced_of_injective f hf

/-- Smooth algebras over a domain are reduced, even when the algebra is disconnected. -/
theorem isReduced_of_smooth_over_domain (R A : Type*) [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Algebra.Smooth R A] : _root_.IsReduced A := by
  classical
  -- Local standard-étale polynomial charts give a reduced principal-open cover.
  have hloc (p : PrimeSpectrum A) :
      ∃ f ∉ p.asIdeal, _root_.IsReduced (Localization.Away f) := by
    obtain ⟨f, hf, n, alg, _tower, he⟩ :=
      Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p.asIdeal)
    let : Algebra (MvPolynomial (Fin n) R) (Localization.Away f) := alg
    have : Algebra.IsStandardEtale (MvPolynomial (Fin n) R) (Localization.Away f) := he
    exact ⟨f, hf, isReduced_of_etale_over_domain
      (MvPolynomial (Fin n) R) (Localization.Away f)⟩
  choose f hfm hf using hloc
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, e⟩ := Ideal.exists_le_maximal _ h
    let p : PrimeSpectrum A := ⟨m, inferInstance⟩
    exact hfm p (e (Ideal.subset_span (Set.mem_range_self p)))
  have : ∀ c : Set.range f, _root_.IsReduced (Localization.Away c.1) :=
    Set.forall_subtype_range_iff.mpr hf
  exact isReduced_of_injective (algebraMap A (Π c : Set.range f, Localization.Away c.1))
    (Localization.algebraMap_injective_of_span_eq_top (Set.range f) hspan)

end ReducednessDescent

variable {R : CommRingCat.{u}} (N : ℕ) [NeZero N]
variable (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R))

/-- The actual fine-level coefficient map is smooth. -/
theorem fullCoefficientHom_smooth : (fullCoefficientHom N hN hinv).Smooth := by
  have : Smooth (fullObject N hN hinv).structMap := fullObject_structMap_smooth N hN hinv
  have hs : (fullObject N hN hinv).structMap.appTop.hom.Smooth :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp inferInstance
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)) hs

/-- Scalars on the actual full-level section ring are induced by its structure morphism. -/
abbrev fullAlgebra : Algebra R ↑Γ((fullObject N hN hinv).base, ⊤) :=
  (fullCoefficientHom N hN hinv).toAlgebra

/-- Actual full-level sections are reduced over a domain base; no fine-ring domain is assumed. -/
theorem fullSections_isReduced [IsDomain R] :
    _root_.IsReduced Γ((fullObject N hN hinv).base, ⊤) := by
  let : Algebra R ↑Γ((fullObject N hN hinv).base, ⊤) := fullAlgebra (R := R) N hN hinv
  have : Algebra.Smooth R ↑Γ((fullObject N hN hinv).base, ⊤) :=
    fullCoefficientHom_smooth (R := R) N hN hinv
  exact ReducednessDescent.isReduced_of_smooth_over_domain
    R ↑Γ((fullObject N hN hinv).base, ⊤)

theorem fullBase_isReduced [IsDomain R] :
    AlgebraicGeometry.IsReduced (fullObject N hN hinv).base := by
  have : _root_.IsReduced Γ((fullObject N hN hinv).base, ⊤) :=
    fullSections_isReduced (R := R) N hN hinv
  exact isReduced_of_isAffine_isReduced _

/-- The actual invariant ring is a subring of the actual reduced fine-level section ring. -/
theorem yZeroInvariantRing_isReduced [IsDomain R] :
    _root_.IsReduced (yZeroInvariantRing N hN hinv) := by
  have : _root_.IsReduced Γ((fullObject N hN hinv).base, ⊤) :=
    fullSections_isReduced (R := R) N hN hinv
  exact isReduced_of_injective (yZeroInvariantRingι N hN hinv).hom
    (yZeroInvariantRingι_injective N hN hinv)

/-- Reducedness of the actual AINTLIB coarse scheme over a domain base. -/
theorem yZeroCoarse_isReduced [IsDomain R] :
    AlgebraicGeometry.IsReduced (ModularCurves.YZeroCoarse (R := R) N hN hinv) := by
  have : _root_.IsReduced (yZeroInvariantRing N hN hinv) :=
    yZeroInvariantRing_isReduced (R := R) N hN hinv
  exact isReduced_of_isOpenImmersion (yZeroInvariantSpecIso N hN hinv).hom

theorem fullComplexSections_isReduced (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) :
    _root_.IsReduced Γ((fullObject (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) :=
  fullSections_isReduced (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)

theorem yZeroComplexInvariantRing_isReduced (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) :
    _root_.IsReduced
      (yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroInvariantRing_isReduced (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)

theorem yZeroComplexCoarse_isReduced (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) :
    AlgebraicGeometry.IsReduced
      (ModularCurves.YZeroCoarse (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroCoarse_isReduced (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)

#print axioms ReducednessDescent.isReduced_of_etale_over_domain
#print axioms ReducednessDescent.isReduced_of_smooth_over_domain
#print axioms fullCoefficientHom_smooth
#print axioms fullSections_isReduced
#print axioms fullBase_isReduced
#print axioms yZeroInvariantRing_isReduced
#print axioms yZeroCoarse_isReduced
#print axioms fullComplexSections_isReduced
#print axioms yZeroComplexInvariantRing_isReduced
#print axioms yZeroComplexCoarse_isReduced

end ModularPolynomialCurveTest.AINTLIB
