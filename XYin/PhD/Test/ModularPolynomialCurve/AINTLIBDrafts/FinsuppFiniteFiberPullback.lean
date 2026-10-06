/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XYin contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Int.Basic

/-!
# Additive pullback of finitely supported functions along finite-fiber maps

A map `r : A → B` with finite fibers pulls back a finitely supported function by
coefficient precomposition: the coefficient at `a` is the old coefficient at
`r a`. Finite support follows from the existing finite-preimage theorem. The
additive map is built using `Finsupp.ofSupportFinite`.

The support lemma needs only zero coefficients, and the bundled pullback needs
only `AddZeroClass`. Injectivity is not required. The two examples check an
explicit two-to-one map with integer coefficients and the additive coefficient
formula. No scheme, principal-divisor, genus or model input is used.
-/

@[expose] public section

namespace Finsupp

variable {A B M : Type*} (r : A → B) (hfib : ∀ b, (r ⁻¹' {b}).Finite)

include hfib in
theorem hasFiniteSupport_comp_of_finiteFibers [Zero M] (D : B →₀ M) :
    Function.HasFiniteSupport (fun a => D (r a)) := by
  change (r ⁻¹' Function.support D).Finite
  exact D.hasFiniteSupport.preimage' (fun b _ => hfib b)

noncomputable def comapDomainOfFiniteFibers [AddZeroClass M] :
    (B →₀ M) →+ (A →₀ M) where
  toFun D := ofSupportFinite (fun a => D (r a))
    (hasFiniteSupport_comp_of_finiteFibers r hfib D)
  map_zero' := by ext a; rfl
  map_add' D E := by ext a; rfl

@[simp]
theorem comapDomainOfFiniteFibers_apply [AddZeroClass M] (D : B →₀ M) (a : A) :
    comapDomainOfFiniteFibers r hfib D a = D (r a) := rfl

@[simp]
theorem comapDomainOfFiniteFibers_zero [AddZeroClass M] :
    comapDomainOfFiniteFibers r hfib (0 : B →₀ M) = 0 := by
  ext a
  rfl

@[simp]
theorem comapDomainOfFiniteFibers_add [AddZeroClass M] (D E : B →₀ M) :
    comapDomainOfFiniteFibers r hfib (D + E) =
      comapDomainOfFiniteFibers r hfib D + comapDomainOfFiniteFibers r hfib E := by
  ext a
  rfl

example :
    comapDomainOfFiniteFibers (fun _ : Bool => ()) (fun _ => Set.toFinite _)
      (single () (3 : ℤ)) = single false 3 + single true 3 := by
  ext a
  cases a <;> simp

example [AddZeroClass M] (D E : B →₀ M) (a : A) :
    comapDomainOfFiniteFibers r hfib (D + E) a = D (r a) + E (r a) := rfl

#print axioms hasFiniteSupport_comp_of_finiteFibers
#print axioms comapDomainOfFiniteFibers
#print axioms comapDomainOfFiniteFibers_apply
#print axioms comapDomainOfFiniteFibers_zero
#print axioms comapDomainOfFiniteFibers_add
#print axioms ofSupportFinite
#print axioms hasFiniteSupport
#print axioms Set.Finite.preimage'
#print axioms Finsupp.ext

end Finsupp
