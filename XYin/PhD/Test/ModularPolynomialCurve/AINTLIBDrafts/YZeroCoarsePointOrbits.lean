/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.YZeroCoarsePointLifting
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Fibers of actual Borel invariants are Borel orbits

For coefficient-valued algebra points over a domain, prime-ideal transitivity for a finite
invariant extension becomes transitivity of the points themselves: a coefficient-algebra
map to the coefficient ring is determined by its kernel. The acting ring can have zero
divisors, and algebraic closedness, finite type, and reducedness are unnecessary here.

We apply this to the literal Borel action on global sections of AINTLIB's full-level
representing object. Equality of restrictions to the actual `YZeroCoarse` invariant ring
is equivalent to pullback along an actual Borel-action morphism.
-/

@[expose] public section

open scoped Pointwise

namespace ModularPolynomialCurveTest.AINTLIB.PointOrbit

variable {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]

/-- A coefficient-algebra map to its coefficient ring is determined by its kernel. -/
theorem algHom_eq_of_ker_eq (φ ψ : B →ₐ[k] k)
    (h : (RingHom.ker φ.toRingHom) = (RingHom.ker ψ.toRingHom)) : φ = ψ := by
  apply AlgHom.ext
  intro x
  have hx : x - algebraMap k B (φ x) ∈ (RingHom.ker φ.toRingHom) := by simp
  rw [h] at hx
  have hx' : ψ (x - algebraMap k B (φ x)) = 0 := hx
  have hx'' : ψ x - φ x = 0 := by simpa using hx'
  exact (sub_eq_zero.mp hx'').symm

variable {A G : Type*} [IsDomain k] [CommRing A]
  [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B]
  [SMulCommClass G k B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]

/-- Fibers of an invariant extension on coefficient-valued algebra points are group orbits. -/
theorem invariant_restriction_eq_iff_orbit (φ ψ : B →ₐ[k] k) :
    (∀ x : A, φ (algebraMap A B x) = ψ (algebraMap A B x)) ↔
      ∃ g : G, ∀ x : B, ψ x = φ (g • x) := by
  constructor
  · intro h
    have hPQ : (RingHom.ker φ.toRingHom).under A = (RingHom.ker ψ.toRingHom).under A := by
      ext x
      change φ (algebraMap A B x) = 0 ↔ ψ (algebraMap A B x) = 0
      rw [h x]
    have : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime φ.toRingHom
    have : (RingHom.ker ψ.toRingHom).IsPrime := RingHom.ker_isPrime ψ.toRingHom
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G
      (RingHom.ker φ.toRingHom) (RingHom.ker ψ.toRingHom) hPQ
    let θ := φ.comp (MulSemiringAction.toAlgHom k B g⁻¹)
    have hker : (RingHom.ker ψ.toRingHom) = (RingHom.ker θ.toRingHom) := by
      rw [hg]
      ext x
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    have hθ : ψ = θ := algHom_eq_of_ker_eq ψ θ hker
    exact ⟨g⁻¹, fun x ↦ congrArg (fun f : B →ₐ[k] k ↦ f x) hθ⟩
  · rintro ⟨g, h⟩ x
    rw [h, smul_algebraMap]

/-- The kernel API also applies over a coefficient ring with zero divisors. -/
example (φ ψ : Polynomial (ℂ × ℂ) →ₐ[ℂ × ℂ] (ℂ × ℂ))
    (h : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom) : φ = ψ :=
  algHom_eq_of_ker_eq φ ψ h

#print axioms algHom_eq_of_ker_eq
#print axioms invariant_restriction_eq_iff_orbit

end ModularPolynomialCurveTest.AINTLIB.PointOrbit

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace ModularPolynomialCurveTest.AINTLIB

variable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))

local instance pointOrbitsFullAlgebra : Algebra ℂ
    Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) :=
  (fullCoefficientHom (R := .of ℂ) N hN (complexLevelIsUnit N)).toAlgebra

local instance pointOrbitsInvariantAlgebra : Algebra ℂ
    (yZeroInvariantRing (R := .of ℂ) N hN (complexLevelIsUnit N)) :=
  yZeroInvariantAlgebra (R := .of ℂ) N hN (complexLevelIsUnit N)

local instance pointOrbitsFullAction : MulSemiringAction (ModularCurves.borel N)
    ↑Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) :=
  (borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).gammaMulSemiringAction
    (show (borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).IsStableOpen
        (⊤ : (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base.Opens) from
      (borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).isStableOpen_preimage
        (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).structMap
        (borelAction_over (R := .of ℂ) N hN (complexLevelIsUnit N)) (⊤ : (Spec (.of ℂ)).Opens))

private theorem fullComplexSection_smul_eq_appTop (g : ModularCurves.borel N)
    (x : Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤)) :
    g • x = ((borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).hom g).appTop.hom x := by
  let a := (borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).hom g
  have htop : a.appLE ⊤ ⊤ le_rfl = a.appTop := by
    change a.appLE ⊤ (a ⁻¹ᵁ ⊤) le_rfl = a.app ⊤
    exact Scheme.Hom.appLE_eq_app _
  exact congrArg (fun f : Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) ⟶
    Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) ↦ f.hom x) htop

private theorem fullComplexSection_scalar_fixed (g : ModularCurves.borel N) (z : ℂ) :
    g • algebraMap ℂ ↑Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) z =
      algebraMap ℂ ↑Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) z := by
  rw [fullComplexSection_smul_eq_appTop]
  have h := congrArg Scheme.Hom.appTop
    (borelAction_over (R := .of ℂ) N hN (complexLevelIsUnit N) g)
  rw [Scheme.Hom.comp_appTop] at h
  exact congrArg (fun f : Γ(Spec (.of ℂ), ⊤) ⟶
    Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) ↦
      f.hom ((Scheme.ΓSpecIso (.of ℂ)).inv.hom z)) h

local instance pointOrbitsScalarComm : SMulCommClass (ModularCurves.borel N) ℂ
    ↑Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) where
  smul_comm g z x := by
    simp only [Algebra.smul_def, smul_mul', fullComplexSection_scalar_fixed]

local instance pointOrbitsInvariantExtension :
    Algebra (yZeroInvariantRing (R := .of ℂ) N hN (complexLevelIsUnit N))
    ↑Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) :=
  (yZeroInvariantRingι (R := .of ℂ) N hN (complexLevelIsUnit N)).hom.toAlgebra

local instance pointOrbitsInvariantIsInvariant :
    Algebra.IsInvariant (yZeroInvariantRing (R := .of ℂ) N hN (complexLevelIsUnit N))
    ↑Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) (ModularCurves.borel N) := by
  change Algebra.IsInvariant (FixedPoints.subalgebra ℤ
    ↑Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) (ModularCurves.borel N))
    ↑Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) (ModularCurves.borel N)
  infer_instance

local instance pointOrbitsInvariantScalarComm : SMulCommClass (ModularCurves.borel N)
    (yZeroInvariantRing (R := .of ℂ) N hN (complexLevelIsUnit N))
    ↑Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) := by
  change SMulCommClass (ModularCurves.borel N) (FixedPoints.subalgebra ℤ
    ↑Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤) (ModularCurves.borel N))
    ↑Γ((fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤)
  infer_instance

/-- Two actual full-level complex algebra points agree on coarse invariants exactly when
one is the pullback of the other along an actual Borel-action morphism. -/
theorem yZeroComplexInvariantRestriction_eq_iff_borel (φ ψ : fullComplexAlgebraPoint N hN) :
    φ.comp (yZeroComplexInvariantInclusion N hN) = ψ.comp (yZeroComplexInvariantInclusion N hN) ↔
      ∃ g : ModularCurves.borel N, ∀ x : Γ(
        (fullObject (R := .of ℂ) N hN (complexLevelIsUnit N)).base, ⊤),
        ψ x = φ (((borelAction (R := .of ℂ) N hN (complexLevelIsUnit N)).hom g).appTop.hom x) := by
  rw [AlgHom.ext_iff]
  change (∀ x : yZeroInvariantRing (R := .of ℂ) N hN (complexLevelIsUnit N),
    φ ((yZeroInvariantRingι (R := .of ℂ) N hN (complexLevelIsUnit N)).hom x) =
      ψ ((yZeroInvariantRingι (R := .of ℂ) N hN (complexLevelIsUnit N)).hom x)) ↔ _
  have h := PointOrbit.invariant_restriction_eq_iff_orbit
    (A := yZeroInvariantRing (R := .of ℂ) N hN (complexLevelIsUnit N))
    (G := ModularCurves.borel N) φ ψ
  change (∀ x : yZeroInvariantRing (R := .of ℂ) N hN (complexLevelIsUnit N),
    φ ((yZeroInvariantRingι (R := .of ℂ) N hN (complexLevelIsUnit N)).hom x) =
      ψ ((yZeroInvariantRingι (R := .of ℂ) N hN (complexLevelIsUnit N)).hom x)) ↔ _ at h
  simpa only [fullComplexSection_smul_eq_appTop] using h

#print axioms yZeroComplexInvariantRestriction_eq_iff_borel

end ModularPolynomialCurveTest.AINTLIB
