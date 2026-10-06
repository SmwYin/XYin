/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.ComplexPointSeparation
public import AINTLIBDrafts.YZeroCoarseFiniteType
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Lifting actual coarse complex points to full-level coefficient algebra points

An injective integral map of algebras lifts points over an algebraically closed field when
its target is of finite type over that field. We instantiate this with the actual Borel
inclusion used by AINTLIB's `YZeroCoarse`. The full-level scalar algebra is exactly the one
induced by its actual structure morphism. The fine ring need not be a domain or reduced.

The output is an algebra point together with its literal restriction equality. Scheme-point
conversion and pullback of the universal elliptic curve are separate interfaces.
-/

@[expose] public section

universe u v w

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

/-- Points over an algebraically closed field lift through an injective integral algebra map. -/
theorem exists_algHom_comp_eq_of_injective_integral
    {k : Type u} [Field k] [IsAlgClosed k]
    {B : Type v} [CommRing B] [Algebra k B]
    {A : Type w} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (ι : B →ₐ[k] A) (hinj : Function.Injective ι) (hint : ι.toRingHom.IsIntegral)
    (φ : B →ₐ[k] k) : ∃ ψ : A →ₐ[k] k, ψ.comp ι = φ := by
  let : Algebra B A := ι.toRingHom.toAlgebra
  have : Algebra.IsIntegral B A := ⟨hint⟩
  let m : Ideal B := RingHom.ker φ.toRingHom
  have : m.IsMaximal := RingHom.ker_isMaximal_of_surjective
    (f := φ.toRingHom) (fun z ↦ ⟨algebraMap k B z, φ.commutes z⟩)
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := B) (S := A) m (by
      change RingHom.ker ι.toRingHom ≤ m
      rw [(RingHom.injective_iff_ker_eq_bot ι.toRingHom).mp hinj]
      exact bot_le)
  have : q.IsMaximal := hq
  obtain ⟨ψ, hψ⟩ := ModularPolynomialCurveTest.AINTLIB.exists_algHom_ker_eq_of_isMaximal
    (k := k) q
  refine ⟨ψ, ?_⟩
  ext b
  have hb : b - algebraMap k B (φ b) ∈ m := by
    change φ (b - algebraMap k B (φ b)) = 0
    rw [map_sub, φ.commutes, Algebra.algebraMap_self_apply, sub_self]
  have hi : ι (b - algebraMap k B (φ b)) ∈ q := by
    change b - algebraMap k B (φ b) ∈ q.under B
    rwa [hqm]
  have hz : ψ (ι (b - algebraMap k B (φ b))) = 0 := by
    rw [← hψ] at hi
    exact hi
  change ψ (ι b) = φ b
  simpa only [map_sub, ι.commutes, ψ.commutes, Algebra.algebraMap_self_apply, sub_eq_zero] using hz

/-- A product sanity check: the lifting API applies to a ring with zero divisors. -/
example : ∃ ψ : (ℂ × ℂ) →ₐ[ℂ] ℂ,
    ψ.comp (Algebra.ofId ℂ (ℂ × ℂ)) = AlgHom.id ℂ ℂ := by
  apply exists_algHom_comp_eq_of_injective_integral
  · exact FaithfulSMul.algebraMap_injective ℂ (ℂ × ℂ)
  · exact Algebra.isIntegral_def.mp (inferInstance : Algebra.IsIntegral ℂ (ℂ × ℂ))

#print axioms exists_algHom_comp_eq_of_injective_integral

open CategoryTheory AlgebraicGeometry

section Actual

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

local instance pointLiftingFullAlgebra : Algebra ℂ
    Γ((fullObject (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) :=
  (fullCoefficientHom (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)).toAlgebra

local instance pointLiftingInvariantAlgebra : Algebra ℂ
    (yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroInvariantAlgebra (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)

/-- Actual full-level complex points use precisely the original coefficient algebra. -/
abbrev fullComplexAlgebraPoint :=
  Γ((fullObject (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) →ₐ[ℂ] ℂ

/-- The literal actual invariant inclusion respects the coefficient algebra. -/
def yZeroComplexInvariantInclusion :
    yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N) →ₐ[ℂ]
      Γ((fullObject (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) where
  toRingHom := (yZeroInvariantRingι (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)).hom
  commutes' z := DFunLike.congr_fun
    (yZeroInvariantCoefficientHom_comp_inclusion (R := CommRingCat.of ℂ)
      N hN (complexLevelIsUnit N)) z

/-- Every actual coarse complex algebra point lifts to an actual fine coefficient algebra point. -/
theorem yZeroComplexAlgebraPoint_lifts
    (φ : yZeroInvariantRing (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N) →ₐ[ℂ] ℂ) :
    ∃ ψ : fullComplexAlgebraPoint N hN,
      ψ.toRingHom.comp
        (yZeroInvariantRingι (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)).hom =
      φ.toRingHom := by
  have : Algebra.FiniteType ℂ
      Γ((fullObject (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) :=
    fullCoefficientHom_finiteType (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)
  obtain ⟨ψ, hψ⟩ := exists_algHom_comp_eq_of_injective_integral
    (yZeroComplexInvariantInclusion N hN)
    (yZeroInvariantRingι_injective (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N))
    (yZeroInvariantRingι_isIntegral (R := CommRingCat.of ℂ) N hN (complexLevelIsUnit N)) φ
  exact ⟨ψ, congrArg AlgHom.toRingHom hψ⟩

#print axioms yZeroComplexInvariantInclusion
#print axioms yZeroComplexAlgebraPoint_lifts

end Actual

end ModularPolynomialCurveTest.AINTLIB
