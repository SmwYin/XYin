/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldExtensionEquiv
import XYin.PhD.Cox.Theorem11_1.ClassFieldLocal
import XYin.PhD.Cox.Theorem11_1.Splitting

/-! # Transport to the fixed complex embedding

Exact Artin kernels are invariant under base-preserving isomorphisms, so a class field built
inside an algebraic closure can be moved to its image under an embedding into `ℂ` that fixes
the given copy of `K`; this gives Cox's fixed-modulus existence for an order's conductor.
-/

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace Cox.ClassFieldTheory

variable (K : Type*) [Field K] [NumberField K]
variable (m : Ideal (𝓞 K))
variable (L M : Type*) [Field L] [Field M] [Algebra K L] [Algebra K M]

/-- A finite extension supplied by the Artin-kernel contract is itself a number field. -/
theorem numberField_of_hasArtinKernel {H : Subgroup (coprimeIdeals K m)}
    (hL : HasArtinKernel K m L H) : NumberField L := by
  haveI := hL.finiteDimensional
  exact NumberField.of_module_finite K L

/-- Finite abelian Galoisness and the exact Artin kernel are invariant under a
base-preserving field equivalence. -/
theorem hasArtinKernel_algEquiv [NumberField L] [NumberField M]
    (e : L ≃ₐ[K] M) {H : Subgroup (coprimeIdeals K m)}
    (hL : HasArtinKernel K m L H) : HasArtinKernel K m M H := by
  exact hasArtinKernel_of_algEquiv K m L M e hL

end Cox.ClassFieldTheory

namespace Cox.Order

variable {K : IntermediateField ℚ ℂ} [hNF : NumberField K]

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Extend the given embedding of `K` into the algebraically closed field `ℂ`. -/
theorem exists_complex_embedding (L : Type*) [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] : Nonempty (L →ₐ[K] ℂ) := by
  haveI : Module.IsTorsionFree K ℂ := Module.IsTorsionFree.of_smul_eq_zero fun r z h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact Or.inl ((map_eq_zero (algebraMap K ℂ)).mp h1)
    · exact Or.inr h1
  haveI : Module.IsTorsionFree K L := Module.IsTorsionFree.of_smul_eq_zero fun r z h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact Or.inl ((map_eq_zero (algebraMap K L)).mp h1)
    · exact Or.inr h1
  exact ⟨IsAlgClosed.lift⟩

/-- The rational intermediate field which is the image of a chosen `K`-embedding. -/
def complexModel (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (ι : L →ₐ[K] ℂ) : IntermediateField ℚ ℂ :=
  (ι.restrictScalars ℚ).fieldRange

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- The image contains the existing embedded copy of `K`, since the chosen map fixes it. -/
theorem le_complexModel (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (ι : L →ₐ[K] ℂ) : K ≤ complexModel L ι := by
  intro x hx
  exact ⟨algebraMap K L ⟨x, hx⟩, ι.commutes ⟨x, hx⟩⟩

/-- Range restriction is an equivalence for precisely the inclusion-induced algebra
used by the Cox ring-class-field definition. -/
theorem exists_complexModel_equiv (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (ι : L →ₐ[K] ℂ) :
    letI : Algebra K (complexModel L ι) :=
      (IntermediateField.inclusion (le_complexModel L ι)).toRingHom.toAlgebra
    Nonempty (L ≃ₐ[K] complexModel L ι) := by
  letI : Algebra K (complexModel L ι) :=
    (IntermediateField.inclusion (le_complexModel L ι)).toRingHom.toAlgebra
  let f : L →ₐ[K] complexModel L ι :=
    { toFun := fun x => ⟨ι x, x, rfl⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' := fun x y => Subtype.ext (map_mul ι x y)
      map_zero' := Subtype.ext (map_zero ι)
      map_add' := fun x y => Subtype.ext (map_add ι x y)
      commutes' := fun k => Subtype.ext (ι.commutes k) }
  refine ⟨AlgEquiv.ofBijective f ⟨fun x y hxy => ι.injective (congrArg Subtype.val hxy), ?_⟩⟩
  rintro ⟨y, x, rfl⟩
  exact ⟨x, rfl⟩

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- The chosen image in `ℂ` is a number field, by the rational range equivalence. -/
theorem complexModel_numberField (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (ι : L →ₐ[K] ℂ) : NumberField (complexModel L ι) := by
  let e : L ≃ₐ[ℚ] complexModel L ι := AlgEquiv.ofInjectiveField (ι.restrictScalars ℚ)
  exact NumberField.of_ringEquiv L _ e.toRingEquiv

variable (O : Subalgebra ℤ K) [hO : IsOrder O] [hK : IsImaginaryQuadraticField K]
include hNF hO hK

/-- Cox 8.6, with Janusz V.9.16 and V.12.7: fixed-modulus class-field existence.
This internal node requires the separate reciprocity, Kummer, and conductor developments. -/
theorem exists_artinKernel (H : Subgroup (conductorCoprimeIdeals O))
    (hH : rayPrincipalIdeals O ≤ H) :
    ∃ (L : IntermediateField ℚ ℂ) (_ : NumberField L) (hKL : K ≤ L),
      letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
      HasArtinKernel O L H := by
  haveI : IsTotallyComplex K := isTotallyComplex
  have hne : conductorIdeal O ≠ ⊥ := by
    rw [conductorIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (conductor_pos O).ne'
  obtain ⟨L₀, hL₀⟩ := ClassFieldTheory.exists_artinKernel_at_modulus K
    (⟨conductorIdeal O, hne, H, hH⟩ : ClassFieldTheory.CongruenceSubgroup K)
  haveI := ClassFieldTheory.numberField_of_hasArtinKernel K _ L₀ hL₀
  haveI := hL₀.finiteDimensional
  obtain ⟨ι⟩ := exists_complex_embedding (K := K) L₀
  haveI := complexModel_numberField L₀ ι
  letI : Algebra K (complexModel L₀ ι) :=
    (IntermediateField.inclusion (le_complexModel L₀ ι)).toRingHom.toAlgebra
  obtain ⟨e⟩ := exists_complexModel_equiv L₀ ι
  exact ⟨complexModel L₀ ι, inferInstance, le_complexModel L₀ ι,
    ClassFieldTheory.hasArtinKernel_algEquiv K _ L₀ (complexModel L₀ ι) e hL₀⟩

end Cox.Order
