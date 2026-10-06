/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.OrderClasses
import XYin.PhD.Cox.Theorem11_1.ClassFieldDescent
import XYin.PhD.Cox.Theorem11_1.Splitting
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # The conjugation argument in Cox Lemma 9.3

Complex conjugation carries an embedded field `L` to `conjugateField L`. On an embedded
imaginary quadratic field `K` it restricts to `quadraticConjugation K`, and a rational
embedding of a normal extension `L/K` has image `L` or `conjugateField L`
(`embedding_range_eq_or_conjugate`). Hence a conjugation-stable normal extension of `K` is
Galois over `ℚ` (`isGalois_of_conjugateField_eq`).

For an order `O` of `K`, conjugation fixes the conductor and the rational-principal subgroup
(Cox Exercise 9.2), so the conjugate of a ring class field of `O` is again one
(`Order.isRingClassField_conjugate`).
-/

open NumberField
open scoped nonZeroDivisors

noncomputable section
namespace Cox

/-- The literal image under complex conjugation, as used in Cox 9.3. -/
def conjugateField (L : IntermediateField ℚ ℂ) : IntermediateField ℚ ℂ :=
  L.map (Complex.conjAe.restrictScalars ℚ).toAlgHom

/-- The canonical equivalence with the conjugate field. -/
def conjugateFieldEquiv (L : IntermediateField ℚ ℂ) : L ≃ₐ[ℚ] conjugateField L :=
  L.equivMap (Complex.conjAe.restrictScalars ℚ).toAlgHom

/-- The equivalence acts by complex conjugation on the ambient value. -/
theorem conjugateFieldEquiv_coe (L : IntermediateField ℚ ℂ) (x : L) :
    ((conjugateFieldEquiv L x : conjugateField L) : ℂ) = star (x : ℂ) := by
  rfl

/-- Complex conjugation is an involution of rational algebra maps. -/
theorem conj_comp_conj :
    (Complex.conjAe.restrictScalars ℚ).toAlgHom.comp (Complex.conjAe.restrictScalars ℚ).toAlgHom =
      AlgHom.id ℚ ℂ :=
  AlgHom.ext fun z => Complex.conj_conj z

/-- Conjugating twice recovers the original embedded field. -/
theorem conjugateField_conjugateField (L : IntermediateField ℚ ℂ) :
    conjugateField (conjugateField L) = L := by
  rw [conjugateField, conjugateField, IntermediateField.map_map, conj_comp_conj,
    IntermediateField.map_id]

/-- The conjugate of a number field is a number field. -/
theorem numberField_conjugateField (L : IntermediateField ℚ ℂ) [NumberField L] :
    NumberField (conjugateField L) := by
  exact NumberField.of_ringEquiv _ _ (conjugateFieldEquiv L).toRingEquiv

/-- Exact Artin kernels transfer along an equality of moduli with the same ambient kernel. -/
theorem ClassFieldTheory.hasArtinKernel_of_modulus_eq {F E : Type*} [Field F] [NumberField F]
    [Field E] [Algebra F E] {m₁ m₂ : Ideal (𝓞 F)} (hm : m₁ = m₂)
    {H₁ : Subgroup (ClassFieldTheory.coprimeIdeals F m₁)}
    {H₂ : Subgroup (ClassFieldTheory.coprimeIdeals F m₂)}
    (hH : H₁.map (ClassFieldTheory.coprimeIdeals F m₁).subtype =
      H₂.map (ClassFieldTheory.coprimeIdeals F m₂).subtype)
    (h : ClassFieldTheory.HasArtinKernel F m₁ E H₁) :
    ClassFieldTheory.HasArtinKernel F m₂ E H₂ := by
  subst hm
  obtain rfl := Subgroup.map_injective (Subgroup.subtype_injective _) hH
  exact h

variable (K : IntermediateField ℚ ℂ) [hIQ : IsImaginaryQuadraticField K]

/-- Restriction of complex conjugation to its normal quadratic subfield. -/
def quadraticConjugation : K ≃ₐ[ℚ] K :=
  (Complex.conjAe.restrictScalars ℚ).restrictNormal K

include hIQ

/-- The restricted automorphism is still literal complex conjugation. -/
theorem quadraticConjugation_coe (x : K) :
    ((quadraticConjugation K x : K) : ℂ) = star (x : ℂ) := by
  exact (Complex.conjAe.restrictScalars ℚ).restrictNormal_commutes K x

/-- The restricted conjugation is an involution. -/
theorem quadraticConjugation_quadraticConjugation (x : K) :
    quadraticConjugation K (quadraticConjugation K x) = x :=
  Subtype.ext <| by rw [quadraticConjugation_coe, quadraticConjugation_coe, star_star]

/-- Cox 9.3: complex conjugation fixes the quadratic base as a set. -/
theorem conjugateField_quadratic : conjugateField K = K := by
  have h : ∀ z ∈ K, star z ∈ K := fun z hz => by
    simpa only [quadraticConjugation_coe] using (quadraticConjugation K ⟨z, hz⟩).2
  ext z
  rw [conjugateField, IntermediateField.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact h x hx
  · exact fun hz => ⟨star z, h z hz, star_star z⟩

/-- The two rational embeddings of an imaginary quadratic field. -/
theorem quadratic_embedding_eq_or_conjugate (φ : K →ₐ[ℚ] ℂ) :
    φ = K.val ∨ φ = (Complex.conjAe.restrictScalars ℚ).toAlgHom.comp K.val := by
  obtain ⟨D, r, hD, hr, hlin⟩ := Order.exists_negative_square_generator (K := K)
  -- Rational embeddings are determined by their value on the generator `r`.
  have hext : ∀ ψ₁ ψ₂ : K →ₐ[ℚ] ℂ, ψ₁ r = ψ₂ r → ψ₁ = ψ₂ := by
    intro ψ₁ ψ₂ h
    have hcard : Fintype.card (Fin 2) = Module.finrank ℚ K := by
      rw [Fintype.card_fin, IsImaginaryQuadraticField.finrank_eq_two]
    apply AlgHom.toLinearMap_injective
    refine (basisOfLinearIndependentOfCardEqFinrank hlin hcard).ext fun i => ?_
    fin_cases i <;> simp [h]
  -- Every embedding sends `r` to a square root of `D`.
  have hsq : ∀ ψ : K →ₐ[ℚ] ℂ, ψ r ^ 2 = (D : ℂ) := fun ψ => by
    rw [← map_pow, hr, map_intCast]
  have hval : ((r : K) : ℂ) ^ 2 = (D : ℂ) := hsq K.val
  -- The generator is purely imaginary, so conjugation negates it.
  have hre : ((r : K) : ℂ).re = 0 := by
    have h1 := congrArg Complex.re hval
    have h2 := congrArg Complex.im hval
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im] at h1 h2
    have hD' : (D : ℝ) < 0 := by exact_mod_cast hD
    rcases mul_eq_zero.mp (show ((r : K) : ℂ).re * ((r : K) : ℂ).im = 0 by linarith) with h | h
    · exact h
    · rw [h] at h1
      nlinarith [sq_nonneg ((r : K) : ℂ).re]
  have hconj : star ((r : K) : ℂ) = -((r : K) : ℂ) := by
    apply Complex.ext <;> simp [hre]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((hsq φ).trans hval.symm) with h | h
  · exact Or.inl (hext _ _ h)
  · exact Or.inr (hext _ _ (h.trans hconj.symm))

/-- A conjugate extension contains the same imaginary quadratic base. -/
theorem le_conjugateField {L : IntermediateField ℚ ℂ} (hKL : K ≤ L) :
    K ≤ conjugateField L := by
  exact (conjugateField_quadratic K).ge.trans (IntermediateField.map_mono _ hKL)

/-- The two conjugation maps form a semilinear square over the base. -/
theorem conjugateFieldEquiv_inclusion {L : IntermediateField ℚ ℂ} (hKL : K ≤ L)
    (x : K) :
    conjugateFieldEquiv L (IntermediateField.inclusion hKL x) =
      IntermediateField.inclusion (le_conjugateField K hKL) (quadraticConjugation K x) := by
  exact Subtype.ext ((conjugateFieldEquiv_coe L _).trans (quadraticConjugation_coe K x).symm)

omit hIQ in
/-- A rational embedding fixing the base is a K-embedding, whose image is fixed by normality. -/
theorem embedding_range_eq_of_fixes_base {L : IntermediateField ℚ ℂ} [NumberField L]
    (hKL : K ≤ L)
    (hN : letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
      Normal K L)
    (φ : L →ₐ[ℚ] ℂ) (hφ : ∀ x : K, φ (IntermediateField.inclusion hKL x) = (x : ℂ)) :
    φ.fieldRange = L := by
  letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  -- Both `φ` and the inclusion of `L` are `K`-embeddings.
  let ψ : L →ₐ[K] ℂ := { φ.toRingHom with commutes' := fun r => hφ r }
  let ι : L →ₐ[K] ℂ := { L.val.toRingHom with commutes' := fun _ => rfl }
  have hle : φ.fieldRange ≤ L := by
    rintro _ ⟨x, rfl⟩
    have hx : ψ x ∈ (minpoly K x).rootSet ℂ := by
      rw [Polynomial.mem_rootSet']
      exact ⟨Polynomial.map_ne_zero (minpoly.ne_zero (hN.isIntegral x)), by
        rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]⟩
    rw [← (hN.splits x).image_rootSet ι] at hx
    obtain ⟨y, -, hy⟩ := hx
    have hy' : (y : ℂ) = φ x := hy
    change φ x ∈ L
    rw [← hy']
    exact y.2
  refine IntermediateField.eq_of_le_of_finrank_eq hle ?_
  let e : L ≃ₐ[ℚ] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  exact e.toLinearEquiv.finrank_eq.symm

/-- A rational embedding of a normal quadratic-base extension has one of two images;
this is the field-image step recalled in Cox's proof of Lemma 9.3. -/
theorem embedding_range_eq_or_conjugate {L : IntermediateField ℚ ℂ} [NumberField L]
    (hKL : K ≤ L)
    (hN : letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
      Normal K L)
    (φ : L →ₐ[ℚ] ℂ) : φ.fieldRange = L ∨ φ.fieldRange = conjugateField L := by
  rcases quadratic_embedding_eq_or_conjugate K (φ.comp (IntermediateField.inclusion hKL)) with
    h | h
  · exact Or.inl (embedding_range_eq_of_fixes_base K hKL hN φ fun x => DFunLike.congr_fun h x)
  · right
    -- Compose with conjugation to obtain an embedding fixing the base.
    have hfix : ∀ x : K, ((Complex.conjAe.restrictScalars ℚ).toAlgHom.comp φ)
        (IntermediateField.inclusion hKL x) = (x : ℂ) := fun x => by
      have hx : φ (IntermediateField.inclusion hKL x) = star (x : ℂ) := DFunLike.congr_fun h x
      change star (φ (IntermediateField.inclusion hKL x)) = (x : ℂ)
      rw [hx, star_star]
    have hr := embedding_range_eq_of_fixes_base K hKL hN _ hfix
    have hφ : φ = (Complex.conjAe.restrictScalars ℚ).toAlgHom.comp
        ((Complex.conjAe.restrictScalars ℚ).toAlgHom.comp φ) := by
      rw [← AlgHom.comp_assoc, conj_comp_conj, AlgHom.id_comp]
    rw [hφ, ← AlgHom.map_fieldRange, hr]
    rfl

omit hIQ in
/-- All images of embeddings lying in the original number field imply normality.
Use the normal closure and complex splitting, without assuming that `ℂ/ℚ` is algebraic. -/
theorem normal_of_embedding_ranges_le (L : IntermediateField ℚ ℂ) [NumberField L]
    (h : ∀ φ : L →ₐ[ℚ] ℂ, φ.fieldRange ≤ L) : Normal ℚ L := by
  have hsplit : ∀ x : L, ((minpoly ℚ x).map (algebraMap ℚ ℂ)).Splits :=
    fun x => IsAlgClosed.splits _
  have hN : Normal ℚ (IntermediateField.normalClosure ℚ L ℂ) :=
    IsNormalClosure.normal (h := Algebra.IsAlgebraic.isNormalClosure_normalClosure hsplit)
  have heq : IntermediateField.normalClosure ℚ L ℂ = L :=
    le_antisymm (normalClosure_le_iff.mpr h) (IntermediateField.le_normalClosure L)
  exact Normal.of_algEquiv (h := hN) (IntermediateField.equivOfEq heq)

/-- Cox 9.3: the two possible images coincide when conjugation preserves the field. -/
theorem isGalois_of_conjugateField_eq {L : IntermediateField ℚ ℂ} [NumberField L]
    (hKL : K ≤ L)
    (hN : letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
      Normal K L)
    (hconj : conjugateField L = L) : IsGalois ℚ L := by
  haveI : Normal ℚ L := normal_of_embedding_ranges_le L fun φ =>
    (embedding_range_eq_or_conjugate K hKL hN φ).elim le_of_eq fun h => (h.trans hconj).le
  exact IsGalois.mk

namespace Order
variable [hNF : NumberField K] (O : Subalgebra ℤ K) [hO : IsOrder O]
include hNF hO

-- `hNF` is part of the fixed signature: the conductor ideal does not need it.
set_option linter.unusedSectionVars false in
/-- Cox Exercise 9.2(a): the conductor modulus is fixed under conjugation. -/
theorem conductorIdeal_map_quadraticConjugation :
    (conductorIdeal O).map
      (RingOfIntegers.mapRingEquiv (quadraticConjugation K).toRingEquiv).toRingHom =
      conductorIdeal O := by
  rw [conductorIdeal, Ideal.map_span, Set.image_singleton, map_natCast]

omit hIQ in
/-- The ring-class subgroup of `I_K(f)` has the rational-principal subgroup as ambient image. -/
theorem map_subtype_rationalPrincipalIdeals :
    (rationalPrincipalIdeals O).map (conductorCoprimeIdeals O).subtype =
      rationalPrincipalAmbient O := by
  rw [rationalPrincipalIdeals, Subgroup.map_comap_eq, Subgroup.range_subtype]
  exact inf_eq_right.mpr (rationalPrincipalAmbient_le O)

/-- Cox Exercise 9.2(a): a rational residue remains the same after conjugation. -/
theorem rational_residue_conjugate (α : 𝓞 K) (a : ℤ)
    (hα : α - (a : 𝓞 K) ∈ conductorIdeal O) :
    RingOfIntegers.mapRingEquiv (quadraticConjugation K).toRingEquiv α - (a : 𝓞 K) ∈
      conductorIdeal O := by
  have h := Ideal.mem_map_of_mem
    (RingOfIntegers.mapRingEquiv (quadraticConjugation K).toRingEquiv).toRingHom hα
  rw [conductorIdeal_map_quadraticConjugation, map_sub, map_intCast] at h
  exact h

/-- Cox Exercise 9.2(a): the rational-principal generating set is invariant. -/
theorem rationalPrincipalGenerators_transport_conjugation :
    ClassFieldTheory.transportFractional K (quadraticConjugation K).toRingEquiv ''
      rationalPrincipalGenerators O = rationalPrincipalGenerators O := by
  -- The transport of a principal ideal is generated by the conjugate generator.
  have hcoe : ∀ (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : 𝓞 K),
      (u : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) →
      (ClassFieldTheory.transportFractional K (quadraticConjugation K).toRingEquiv u :
        FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰
          ((RingOfIntegers.mapRingEquiv (quadraticConjugation K).toRingEquiv α : 𝓞 K) : K) := by
    intro u α hu
    change FractionalIdeal.ringEquivOfRingEquiv K K
        (RingOfIntegers.mapRingEquiv (quadraticConjugation K).toRingEquiv)
        (u : FractionalIdeal (𝓞 K)⁰ K) = _
    rw [hu, FractionalIdeal.ringEquivOfRingEquiv_spanSingleton]
    exact congrArg _ (IsFractionRing.ringEquivOfRingEquiv_algebraMap _ α)
  have hmem : ∀ u ∈ rationalPrincipalGenerators O,
      ClassFieldTheory.transportFractional K (quadraticConjugation K).toRingEquiv u ∈
        rationalPrincipalGenerators O := by
    rintro u ⟨α, hα, ⟨a, ha, hαa⟩, hu⟩
    exact ⟨RingOfIntegers.mapRingEquiv (quadraticConjugation K).toRingEquiv α,
      (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv _).injective).mpr hα,
      ⟨a, ha, rational_residue_conjugate K O α a hαa⟩, hcoe u α hu⟩
  have hinv : ∀ u ∈ rationalPrincipalGenerators O,
      ClassFieldTheory.transportFractional K (quadraticConjugation K).toRingEquiv
        (ClassFieldTheory.transportFractional K (quadraticConjugation K).toRingEquiv u) = u := by
    rintro u ⟨α, -, -, hu⟩
    apply Units.ext
    rw [hcoe _ _ (hcoe u α hu), hu]
    exact congrArg _ (quadraticConjugation_quadraticConjugation K (α : K))
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hmem u hu
  · exact fun hv => ⟨_, hmem v hv, hinv v hv⟩

/-- Cox Exercise 9.2(a): invariance passes from generators to the principal subgroup. -/
theorem rationalPrincipalAmbient_map_conjugation :
    (rationalPrincipalAmbient O).map
      (ClassFieldTheory.transportFractional K (quadraticConjugation K).toRingEquiv).toMonoidHom =
      rationalPrincipalAmbient O := by
  rw [rationalPrincipalAmbient, MonoidHom.map_closure, MulEquiv.coe_toMonoidHom,
    rationalPrincipalGenerators_transport_conjugation]

/-- Cox Exercise 9.2(b,c): transport the Artin map and its exact kernel to the conjugate field. -/
theorem hasArtinKernel_conjugate {L : IntermediateField ℚ ℂ}
    (hKL : K ≤ L)
    (hL : letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
      HasArtinKernel O L (rationalPrincipalIdeals O)) :
    letI : Algebra K (conjugateField L) :=
      (IntermediateField.inclusion (le_conjugateField K hKL)).toRingHom.toAlgebra
    HasArtinKernel O (conjugateField L) (rationalPrincipalIdeals O) := by
  letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  letI : Algebra K (conjugateField L) :=
    (IntermediateField.inclusion (le_conjugateField K hKL)).toRingHom.toAlgebra
  have h := ClassFieldTheory.hasArtinKernel_semilinear K (quadraticConjugation K).toRingEquiv
    (conjugateFieldEquiv L).toRingEquiv (fun x => conjugateFieldEquiv_inclusion K hKL x)
    (conductorIdeal O) (rationalPrincipalIdeals O) hL
  refine ClassFieldTheory.hasArtinKernel_of_modulus_eq
    (conductorIdeal_map_quadraticConjugation K O) ?_ h
  rw [Subgroup.map_map]
  calc _ = ((rationalPrincipalIdeals O).map (conductorCoprimeIdeals O).subtype).map
          (ClassFieldTheory.transportFractional K
            (quadraticConjugation K).toRingEquiv).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        exact MonoidHom.ext (ClassFieldTheory.transportCoprime_coe K _ _)
    _ = _ := by
        rw [map_subtype_rationalPrincipalIdeals, rationalPrincipalAmbient_map_conjugation]
        exact (map_subtype_rationalPrincipalIdeals K O).symm

/-- Cox Lemma 9.3: the conjugate field has the same defining ring-class kernel. -/
theorem isRingClassField_conjugate {L : IntermediateField ℚ ℂ}
    (hL : IsRingClassField O L) : IsRingClassField O (conjugateField L) := by
  haveI := hL.numberField
  exact ⟨numberField_conjugateField L, le_conjugateField K hL.le,
    hasArtinKernel_conjugate K O hL.le hL.artinKernel⟩

end Order
end Cox
