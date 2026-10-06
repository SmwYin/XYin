/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import AINTLIBDrafts.PrincipalDivisorValuation
public import AINTLIBDrafts.FinsuppFiniteFiberPullback

/-!
# Principal-divisor pullback from normalized valuation restriction

A finite-fiber map of intrinsic places pulls back principal divisors when its
normalized valuations agree with restriction along the supplied field algebra
homomorphism. The proof compares coefficients using the valuation formula and
injectivity of `WithZero.exp`.

Each field retains its independent base algebra and its own current finite,
separating polynomial/rational-function chart inputs. No relation between the
two chart parameters, full constant field, genus or scheme model is assumed.
The examples check the identity map and the pointwise coefficient equation.
-/

@[expose] public section

open scoped Polynomial RatFunc WithZero

namespace FunctionField

variable (k K L : Type*) [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k L] [Algebra k[X] L] [Algebra k⟮X⟯ L]
  [IsScalarTower k k[X] L] [IsScalarTower k[X] k⟮X⟯ L] [FunctionField k L]
  [Algebra.IsSeparable k⟮X⟯ L]

theorem principalDivisor_comapDomainOfFiniteFibers
    (φ : L →ₐ[k] K) (r : Place k K → Place k L)
    (hfib : ∀ w, (r ⁻¹' {w}).Finite)
    (hval : ∀ v z, (r v).valuation z = v.valuation (φ z)) (u : Lˣ) :
    Finsupp.comapDomainOfFiniteFibers r hfib
      (principalDivisor k L (Additive.ofMul u)) =
        principalDivisor k K (Additive.ofMul (Units.map φ.toRingHom u)) := by
  let u' : Kˣ := Units.map φ.toRingHom u
  have hu' : (u' : K) = φ (u : L) := rfl
  ext v
  rw [Finsupp.comapDomainOfFiniteFibers_apply]
  apply neg_injective
  apply WithZero.exp_injective
  calc
    WithZero.exp (-(principalDivisor k L (Additive.ofMul u) (r v))) =
        (r v).valuation (u : L) :=
      (valuation_eq_exp_neg_principalDivisor k L u (r v)).symm
    _ = v.valuation (φ (u : L)) := hval v (u : L)
    _ = WithZero.exp
        (-(principalDivisor k K (Additive.ofMul (Units.map φ.toRingHom u)) v)) :=
      by simpa only [hu'] using valuation_eq_exp_neg_principalDivisor k K u' v

example (u : Kˣ) :
    Finsupp.comapDomainOfFiniteFibers (id : Place k K → Place k K)
      (fun _ => by simp)
      (principalDivisor k K (Additive.ofMul u)) =
        principalDivisor k K (Additive.ofMul u) := by
  simpa using principalDivisor_comapDomainOfFiniteFibers k K K (AlgHom.id k K)
    id (fun _ => by simp) (fun _ _ => rfl) u

example (φ : L →ₐ[k] K) (r : Place k K → Place k L)
    (hfib : ∀ w, (r ⁻¹' {w}).Finite)
    (hval : ∀ v z, (r v).valuation z = v.valuation (φ z)) (u : Lˣ) (v : Place k K) :
    principalDivisor k L (Additive.ofMul u) (r v) =
      principalDivisor k K (Additive.ofMul (Units.map φ.toRingHom u)) v := by
  simpa only [Finsupp.comapDomainOfFiniteFibers_apply] using
    congrArg (fun D : Divisor k K => D v)
      (principalDivisor_comapDomainOfFiniteFibers k K L φ r hfib hval u)

#print axioms principalDivisor_comapDomainOfFiniteFibers
#print axioms valuation_eq_exp_neg_principalDivisor
#print axioms Finsupp.comapDomainOfFiniteFibers
#print axioms Finsupp.comapDomainOfFiniteFibers_apply
#print axioms WithZero.exp_injective
#print axioms neg_injective
#print axioms Units.map
#print axioms Units.coe_map
#print axioms Finsupp.ext

end FunctionField
