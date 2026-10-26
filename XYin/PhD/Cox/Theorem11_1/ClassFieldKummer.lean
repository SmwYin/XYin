/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import XYin.PhD.Cox.Theorem11_1.ClassFieldArithmetic

/-!
# Source decomposition of Janusz V.8.1

The radical character is the actual ratio σ(a)/a. Hilbert 90 supplies its surjectivity;
finite character duality and the independent-generator degree bound finish Kummer
correspondence.
-/

open NumberField IntermediateField

noncomputable section

namespace Cox.ClassFieldTheory

namespace Kummer

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The actual embedded base-field units. -/
def baseUnits : Subgroup Lˣ := (Units.map (algebraMap K L).toMonoidHom).range

/-- Janusz's M: units whose nth powers lie in the embedded base field. -/
def radicalUnits (n : ℕ) : Subgroup Lˣ :=
  (baseUnits K L).comap (powMonoidHom n)

/-- Embedded base units are radical units for every exponent. -/
theorem baseUnits_le_radicalUnits (n : ℕ) : baseUnits K L ≤ radicalUnits K L n := by
  intro u hu
  change u ^ n ∈ baseUnits K L
  exact (baseUnits K L).pow_mem hu n

/-- The radical automorphism ratio is an nth root of unity. -/
theorem radical_ratio_pow (n : ℕ) (a : radicalUnits K L n) (σ : L ≃ₐ[K] L) :
    (σ ((a : Lˣ) : L) / ((a : Lˣ) : L)) ^ n = 1 := by
  have ha : (a : Lˣ) ^ n ∈ baseUnits K L := a.property
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp ha
  have hb' : algebraMap K L (b : K) = ((a : Lˣ) : L) ^ n :=
    congrArg (fun u : Lˣ ↦ (u : L)) hb
  have hfixed : (σ ((a : Lˣ) : L)) ^ n = ((a : Lˣ) : L) ^ n := by
    calc
      (σ ((a : Lˣ) : L)) ^ n = σ (((a : Lˣ) : L) ^ n) := (map_pow σ _ n).symm
      _ = σ (algebraMap K L (b : K)) := congrArg σ hb'.symm
      _ = algebraMap K L (b : K) := σ.commutes (b : K)
      _ = ((a : Lˣ) : L) ^ n := hb'
  rw [div_pow, hfixed, div_self (pow_ne_zero n (Units.ne_zero (a : Lˣ)))]

/-- All nth roots of unity in the extension already lie in the base field. -/
theorem rootOfUnity_mem_base (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (x : L) (hx : x ^ n = 1) :
    ∃ u : Kˣ, algebraMap K L (u : K) = x := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let y : rootsOfUnity n L := rootsOfUnity.mkOfPowEq x hx
  have hmap : (rootsOfUnity n K).map (Units.map (algebraMap K L).toMonoidHom) =
      rootsOfUnity n L :=
    hζ.map_rootsOfUnity (f := (algebraMap K L).toMonoidHom) (algebraMap K L).injective
  have hy : (y : Lˣ) ∈ (rootsOfUnity n K).map
      (Units.map (algebraMap K L).toMonoidHom) := by
    rw [hmap]
    exact y.property
  obtain ⟨u, _, hu⟩ := Subgroup.mem_map.mp hy
  refine ⟨u, ?_⟩
  have hu' : algebraMap K L (u : K) = ((y : Lˣ) : L) :=
    congrArg (fun v : Lˣ ↦ (v : L)) hu
  exact hu'.trans (rootsOfUnity.coe_mkOfPowEq hx)

/-- The quotient σ(a)/a has a unique nonzero base-field representative. -/
theorem radical_ratio_base (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (a : radicalUnits K L n) (σ : L ≃ₐ[K] L) :
    ∃! u : Kˣ, algebraMap K L (u : K) =
      σ ((a : Lˣ) : L) / ((a : Lˣ) : L) := by
  have hex : ∃ u : Kˣ, algebraMap K L (u : K) =
      σ ((a : Lˣ) : L) / ((a : Lˣ) : L) :=
    Cox.ClassFieldTheory.Kummer.rootOfUnity_mem_base K L n hn ζ hζ _
      (Cox.ClassFieldTheory.Kummer.radical_ratio_pow K L n a σ)
  refine existsUnique_of_exists_of_unique hex ?_
  intro u v hu hv
  apply Units.ext
  exact (algebraMap K L).injective (hu.trans hv.symm)

/-- Multiplication of radicals multiplies their automorphism ratios. -/
theorem radical_ratio_mul (n : ℕ) (a b : radicalUnits K L n) (σ : L ≃ₐ[K] L) :
    σ (((a * b : radicalUnits K L n) : Lˣ) : L) /
        (((a * b : radicalUnits K L n) : Lˣ) : L) =
      (σ ((a : Lˣ) : L) / ((a : Lˣ) : L)) *
        (σ ((b : Lˣ) : L) / ((b : Lˣ) : L)) := by
  change σ (((a : Lˣ) : L) * ((b : Lˣ) : L)) /
      (((a : Lˣ) : L) * ((b : Lˣ) : L)) = _
  calc
    σ (((a : Lˣ) : L) * ((b : Lˣ) : L)) /
        (((a : Lˣ) : L) * ((b : Lˣ) : L)) =
        (σ ((a : Lˣ) : L) * σ ((b : Lˣ) : L)) /
          (((a : Lˣ) : L) * ((b : Lˣ) : L)) :=
      congrArg (fun x : L ↦ x / (((a : Lˣ) : L) * ((b : Lˣ) : L)))
        (map_mul σ ((a : Lˣ) : L) ((b : Lˣ) : L))
    _ = (σ ((a : Lˣ) : L) / ((a : Lˣ) : L)) *
        (σ ((b : Lˣ) : L) / ((b : Lˣ) : L)) :=
      mul_div_mul_comm (σ ((a : Lˣ) : L)) (σ ((b : Lˣ) : L))
        ((a : Lˣ) : L) ((b : Lˣ) : L)

/-- Base-valued ratios turn the cocycle identity into the character identity. -/
theorem radical_ratio_comp (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (a : radicalUnits K L n) (σ τ : L ≃ₐ[K] L) :
    (σ * τ) ((a : Lˣ) : L) / ((a : Lˣ) : L) =
      (σ ((a : Lˣ) : L) / ((a : Lˣ) : L)) *
        (τ ((a : Lˣ) : L) / ((a : Lˣ) : L)) := by
  -- C1: Eliminate the one tau-ratio witness; its uniqueness is not used.
  refine Exists.elim
    (Cox.ClassFieldTheory.Kummer.radical_ratio_base K L n hn ζ hζ a τ).exists ?_
  intro u hu
  let A : L := ((a : Lˣ) : L)
  let b : L := algebraMap K L (u : K)
  change b = τ A / A at hu
  change (σ * τ) A / A = (σ A / A) * (τ A / A)
  -- C2: The original radical is a unit, so the denominator is nonzero.
  have hA : A ≠ 0 := Units.ne_zero (a : Lˣ)
  -- C3: Recover Janusz's eigen-scalar formula from that same ratio.
  have hτ : τ A = b * A := (div_eq_iff hA).mp hu.symm
  calc
    -- C4: Native multiplication applies sigma after tau.
    (σ * τ) A / A = σ (τ A) / A :=
      congrArg (fun x : L ↦ x / A) (AlgEquiv.mul_apply σ τ A)
    -- C5: Transport the same eigen-scalar equality under sigma and division.
    _ = σ (b * A) / A := congrArg (fun x : L ↦ σ x / A) hτ
    -- C6: Sigma preserves multiplication; the denominator is unchanged.
    _ = (σ b * σ A) / A := congrArg (fun x : L ↦ x / A) (map_mul σ b A)
    -- C7: Sigma fixes this exact base-field scalar b.
    _ = (b * σ A) / A :=
      congrArg (fun x : L ↦ (x * σ A) / A) (σ.commutes (u : K))
    -- C8: Reassociate division, then commute scalar factors only.
    _ = (σ A / A) * b :=
      (mul_div_assoc b (σ A) A).trans (mul_comm b (σ A / A))
    -- C9: Substitute the original tau-ratio equality using the same u.
    _ = (σ A / A) * (τ A / A) := congrArg (fun x : L ↦ (σ A / A) * x) hu

/-- The actual radical-to-character homomorphism, specified by its field values. -/
theorem exists_radicalCharacterHom (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) :
    ∃ Φ : radicalUnits K L n →* ((L ≃ₐ[K] L) →* Kˣ),
      ∀ a σ, algebraMap K L ((Φ a σ : Kˣ) : K) =
        σ ((a : Lˣ) : L) / ((a : Lˣ) : L) := by
  -- W1: Fix the unique-existence proof and one selected unit for every pair.
  let h (a : radicalUnits K L n) (σ : L ≃ₐ[K] L) :=
    Cox.ClassFieldTheory.Kummer.radical_ratio_base K L n hn ζ hζ a σ
  let c (a : radicalUnits K L n) (σ : L ≃ₐ[K] L) : Kˣ := Classical.choose (h a σ)
  have hc (a : radicalUnits K L n) (σ : L ≃ₐ[K] L) :
      algebraMap K L ((c a σ : Kˣ) : K) =
        σ ((a : Lˣ) : L) / ((a : Lˣ) : L) :=
    (Classical.choose_spec (h a σ)).1
  -- W2a: Keep the product of the same units when passing to scalar images.
  have h_image_mul (u v : Kˣ) :
      algebraMap K L ((u * v : Kˣ) : K) =
        algebraMap K L (u : K) * algebraMap K L (v : K) :=
    (congrArg (algebraMap K L) (Units.val_mul u v)).trans
      (RingHom.map_mul (algebraMap K L) (u : K) (v : K))
  -- W2b: Substitute two known scalar images without a new representative.
  have h_product_eq {x y r s : L} (hx : x = r) (hy : y = s) : x * y = r * s :=
    (congrArg (fun z : L ↦ z * y) hx).trans (congrArg (fun z : L ↦ r * z) hy)
  -- W3: Uniqueness at the same pair (a, sigma*tau) lifts the inner ratio law.
  have h_inner_mul (a : radicalUnits K L n) (σ τ : L ≃ₐ[K] L) :
      c a (σ * τ) = c a σ * c a τ := by
    apply ExistsUnique.unique (h a (σ * τ)) (hc a (σ * τ))
    calc
      algebraMap K L ((c a σ * c a τ : Kˣ) : K) =
          algebraMap K L ((c a σ : Kˣ) : K) *
            algebraMap K L ((c a τ : Kˣ) : K) := h_image_mul (c a σ) (c a τ)
      _ = (σ ((a : Lˣ) : L) / ((a : Lˣ) : L)) *
          (τ ((a : Lˣ) : L) / ((a : Lˣ) : L)) := h_product_eq (hc a σ) (hc a τ)
      _ = (σ * τ) ((a : Lˣ) : L) / ((a : Lˣ) : L) :=
        (Cox.ClassFieldTheory.Kummer.radical_ratio_comp K L n hn ζ hζ a σ τ).symm
  -- W4: Native mk' supplies the identity law in the group-valued codomain K units.
  let ψ (a : radicalUnits K L n) : (L ≃ₐ[K] L) →* Kˣ :=
    MonoidHom.mk' (c a) (h_inner_mul a)
  -- W5a: The outer ratio law compares units for the actual radical product a*b.
  have h_outer_unit_mul (a b : radicalUnits K L n) (σ : L ≃ₐ[K] L) :
      c (a * b) σ = c a σ * c b σ := by
    apply ExistsUnique.unique (h (a * b) σ) (hc (a * b) σ)
    calc
      algebraMap K L ((c a σ * c b σ : Kˣ) : K) =
          algebraMap K L ((c a σ : Kˣ) : K) *
            algebraMap K L ((c b σ : Kˣ) : K) := h_image_mul (c a σ) (c b σ)
      _ = (σ ((a : Lˣ) : L) / ((a : Lˣ) : L)) *
          (σ ((b : Lˣ) : L) / ((b : Lˣ) : L)) := h_product_eq (hc a σ) (hc b σ)
      _ = σ (((a * b : radicalUnits K L n) : Lˣ) : L) /
          (((a * b : radicalUnits K L n) : Lˣ) : L) :=
        (Cox.ClassFieldTheory.Kummer.radical_ratio_mul K L n a b σ).symm
  -- W5b: Outer multiplicativity is equality of the two bundled characters.
  have h_outer_mul (a b : radicalUnits K L n) : ψ (a * b) = ψ a * ψ b := by
    apply MonoidHom.ext
    intro σ
    change c (a * b) σ = (ψ a * ψ b) σ
    exact (h_outer_unit_mul a b σ).trans (MonoidHom.mul_apply (ψ a) (ψ b) σ).symm
  -- W6: The native pointwise character group makes mk' available a second time.
  let Φ : radicalUnits K L n →* ((L ≃ₐ[K] L) →* Kˣ) := MonoidHom.mk' ψ h_outer_mul
  -- W7: The final specification concerns this exact Phi, reducing to the same c.
  refine ⟨Φ, ?_⟩
  intro a σ
  exact hc a σ

/-- A chosen copy of the uniquely specified ratio homomorphism. -/
def radicalCharacterHom (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) : radicalUnits K L n →* ((L ≃ₐ[K] L) →* Kˣ) :=
  Classical.choose (exists_radicalCharacterHom K L n hn ζ hζ)

/-- The defining ratio formula retained after choosing the homomorphism. -/
theorem radicalCharacterHom_apply (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (a : radicalUnits K L n) (σ : L ≃ₐ[K] L) :
    algebraMap K L ((radicalCharacterHom K L n hn ζ hζ a σ : Kˣ) : K) =
      σ ((a : Lˣ) : L) / ((a : Lˣ) : L) := by
  exact (Classical.choose_spec
    (Cox.ClassFieldTheory.Kummer.exists_radicalCharacterHom K L n hn ζ hζ)) a σ

/-- A base-valued character is a multiplicative cocycle under the Galois action. -/
theorem character_isMulCocycle (χ : (L ≃ₐ[K] L) →* Kˣ) :
    groupCohomology.IsMulCocycle₁ (fun σ => Units.map (algebraMap K L).toMonoidHom (χ σ)) := by
  -- F abbreviates exactly the unit map already present in the public target.
  let F : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  -- C1: The genuine action fixes the image of each base unit.
  have hfixed (σ : L ≃ₐ[K] L) (u : Kˣ) : σ • F u = F u := by
    apply Units.ext
    change σ (algebraMap K L (u : K)) = algebraMap K L (u : K)
    exact σ.commutes (u : K)
  -- Unfold the cocycle predicate, retaining the same character and automorphisms.
  intro σ τ
  change F (χ (σ * τ)) = (σ • F (χ τ)) * F (χ σ)
  -- C2: The native composition is the same embedded character.
  have hmul : F (χ (σ * τ)) = F (χ σ) * F (χ τ) :=
    (F.comp χ).map_mul σ τ
  -- C3: Commute only the target units, not the two automorphisms.
  have hcomm : F (χ σ) * F (χ τ) = F (χ τ) * F (χ σ) :=
    mul_comm (F (χ σ)) (F (χ τ))
  -- C4: Restore the genuine action on that same first target factor.
  have haction : F (χ τ) * F (χ σ) = (σ • F (χ τ)) * F (χ σ) :=
    congrArg (fun u : Lˣ ↦ u * F (χ σ)) (hfixed σ (χ τ)).symm
  -- Assemble the three equalities in the library's reversed-factor convention.
  exact hmul.trans (hcomm.trans haction)

/-- Hilbert 90 realizes each base-valued character by a radical candidate. -/
theorem character_has_eigenvector [FiniteDimensional K L] (χ : (L ≃ₐ[K] L) →* Kˣ) :
    ∃ a : Lˣ, ∀ σ : L ≃ₐ[K] L,
      σ (a : L) / (a : L) = algebraMap K L ((χ σ : Kˣ) : K) := by
  -- The function is exactly the supplied character followed by the existing unit map.
  let f : (L ≃ₐ[K] L) → Lˣ :=
    fun σ ↦ Units.map (algebraMap K L).toMonoidHom (χ σ)
  -- E1: Retain the same supplied character and genuine native action.
  have hc : groupCohomology.IsMulCocycle₁ f :=
    Cox.ClassFieldTheory.Kummer.character_isMulCocycle K L χ
  -- E2: Native Hilbert90 produces one unit with its uniform automorphism specification.
  have hb : groupCohomology.IsMulCoboundary₁ f :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hc
  -- Ordinary proposition-valued elimination retains the same witness for every σ.
  refine Exists.elim hb ?_
  intro a ha
  refine Exists.intro a ?_
  intro σ
  -- E3: Project the same unit equality and explicitly convert unit division to field division.
  have hval := congrArg (fun u : Lˣ ↦ (u : L)) (ha σ)
  beta_reduce at hval
  rw [Units.val_div_eq_div_val] at hval
  change σ (a : L) / (a : L) = algebraMap K L ((χ σ : Kˣ) : K) at hval
  exact hval

/-- Taking nth powers of radical units lands uniquely in the base-field units. -/
theorem exists_radicalPowerHom (n : ℕ) :
    ∃ P : radicalUnits K L n →* Kˣ, ∀ a,
      algebraMap K L ((P a : Kˣ) : K) = ((a : Lˣ) : L) ^ n := by
  -- Data context: the exact existing unit embedding, with no new field map.
  let F : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  -- C1: The same unit embedding is injective.
  have hF : Function.Injective F := Units.map_injective (algebraMap K L).injective
  -- C2: One native equivalence onto its actual range, with its fixed inverse.
  let e : Kˣ ≃* F.range := MonoidHom.ofInjective hF
  -- C3: Radical membership is exactly the range condition for the nth power.
  let q : radicalUnits K L n →* F.range :=
    ((powMonoidHom n).restrict (radicalUnits K L n)).codRestrict F.range
      (fun a ↦ a.property)
  -- C4: One base-valued bundled homomorphism, using the same e and q.
  let P : radicalUnits K L n →* Kˣ := e.symm.toMonoidHom.comp q
  refine Exists.intro P ?_
  intro a
  -- C5: The same inverse and same input supply the identity in L units.
  have hunit : F (P a) = (a : Lˣ) ^ n :=
    MonoidHom.apply_ofInjective_symm hF (q a)
  -- C6: Project that identity and explicitly expose both unit-value bridges.
  have hval := congrArg (fun u : Lˣ ↦ (u : L)) hunit
  change ((Units.map (algebraMap K L).toMonoidHom (P a) : Lˣ) : L) =
    (((a : Lˣ) ^ n : Lˣ) : L) at hval
  rw [Units.coe_map, Units.val_pow_eq_pow_val] at hval
  exact hval

/-- The actual base-valued nth-power homomorphism. -/
def radicalPowerHom (n : ℕ) : radicalUnits K L n →* Kˣ :=
  Classical.choose (exists_radicalPowerHom K L n)

/-- Its defining nth-power formula. -/
theorem radicalPowerHom_apply (n : ℕ) (a : radicalUnits K L n) :
    algebraMap K L ((radicalPowerHom K L n a : Kˣ) : K) = ((a : Lˣ) : L) ^ n := by
  exact (Classical.choose_spec
    (Cox.ClassFieldTheory.Kummer.exists_radicalPowerHom K L n)) a

/-- The subgroup of radicands produced by all radical elements of L. -/
def radicalPowerRange (n : ℕ) : Subgroup Kˣ := (radicalPowerHom K L n).range

/-- Taking powers of base units includes all base nth powers in the radicand subgroup. -/
theorem nthPowers_le_radicalPowerRange (n : ℕ) :
    nthPowers K n ≤ radicalPowerRange K L n := by
  intro x hx
  -- Setup: the fixed unit embedding, with no new algebra structure.
  let F : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  -- C1: Keep the original base unit u and its original power equation.
  have hx' : ∃ u : Kˣ, u ^ n = x := MonoidHom.mem_range.mp hx
  refine Exists.elim hx' ?_
  intro u hu
  -- C2: The same u witnesses membership in the actual base-unit range.
  have hbase : F u ∈ baseUnits K L := Exists.intro u (Eq.refl (F u))
  -- C3: Make a radical with exactly the value F u, using the existing child.
  let a : radicalUnits K L n :=
    ⟨F u, Cox.ClassFieldTheory.Kummer.baseUnits_le_radicalUnits K L n hbase⟩
  -- C4: Apply the chosen-map formula to this same a, exposing the value bridge.
  have h := Cox.ClassFieldTheory.Kummer.radicalPowerHom_apply K L n a
  change (algebraMap K L) ((radicalPowerHom K L n a : Kˣ) : K) =
    ((Units.map (algebraMap K L).toMonoidHom u : Lˣ) : L) ^ n at h
  rw [Units.coe_map] at h
  change (algebraMap K L) ((radicalPowerHom K L n a : Kˣ) : K) =
    (algebraMap K L) (u : K) ^ n at h
  -- C5: Match the image of the same base-unit nth power, for arbitrary n.
  rw [← map_pow (algebraMap K L) (u : K) n,
    ← Units.val_pow_eq_pow_val (a := u) n] at h
  -- C6: Reflect scalar equality and then equality of K units.
  have hunit : radicalPowerHom K L n a = u ^ n :=
    Units.ext ((algebraMap K L).injective h)
  -- Assembly: the same radical a witnesses the original element x in the range.
  change ∃ b : radicalUnits K L n, radicalPowerHom K L n b = x
  exact Exists.intro a (hunit.trans hu)

/-- A radical nth power is already a base nth power exactly when the radical itself
is an embedded base unit. -/
theorem radicalPowerHom_preimage_nthPowers (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) :
    (nthPowers K n).comap (radicalPowerHom K L n) =
      (baseUnits K L).subgroupOf (radicalUnits K L n) := by
  -- Setup: the original unit embedding, with the original algebra structure.
  let F : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  -- Parent assembly: both memberships concern this same existing radical a.
  apply Subgroup.ext
  intro a
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  refine Iff.intro ?_ ?_
  · intro ha
    -- F1: retain the original base-power witness u and its equation.
    have hpow : ∃ u : Kˣ, u ^ n = radicalPowerHom K L n a :=
      MonoidHom.mem_range.mp ha
    refine Exists.elim hpow ?_
    intro u hu
    -- F2: compare the powers of this same a and the image of this same u.
    have h := Cox.ClassFieldTheory.Kummer.radicalPowerHom_apply K L n a
    rw [← hu, Units.val_pow_eq_pow_val (a := u) n,
      map_pow (algebraMap K L) (u : K) n] at h
    have hp : ((a : Lˣ) : L) ^ n = (algebraMap K L (u : K)) ^ n := h.symm
    -- F3: the denominator is the value of the actual mapped unit F u.
    have hu0 : algebraMap K L (u : K) ≠ 0 := by
      have h0 := Units.ne_zero (F u)
      change ((Units.map (algebraMap K L).toMonoidHom u : Lˣ) : L) ≠ 0 at h0
      rw [Units.coe_map] at h0
      exact h0
    -- F4: the ratio of those same values has nth power one.
    have hx : (((a : Lˣ) : L) / algebraMap K L (u : K)) ^ n = 1 := by
      rw [div_pow, hp]
      exact div_self (pow_ne_zero n hu0)
    -- F5: descend this exact ratio, keeping a single representative v.
    refine Exists.elim (Cox.ClassFieldTheory.Kummer.rootOfUnity_mem_base
      K L n hn ζ hζ (((a : Lˣ) : L) / algebraMap K L (u : K)) hx) ?_
    intro v hv
    -- F6: recover the original radical value using exactly the product v*u.
    have hprod : algebraMap K L ((v * u : Kˣ) : K) = ((a : Lˣ) : L) := by
      rw [Units.val_mul, map_mul, hv]
      exact div_mul_cancel₀ _ hu0
    -- F7: return this same product as the base-unit range witness.
    have hunit : F (v * u) = (a : Lˣ) := by
      apply Units.ext
      change ((Units.map (algebraMap K L).toMonoidHom (v * u) : Lˣ) : L) =
        ((a : Lˣ) : L)
      rw [Units.coe_map]
      exact hprod
    change ∃ w : Kˣ, F w = (a : Lˣ)
    exact Exists.intro (v * u) hunit
  · intro ha
    -- R1: retain one base representative of the same existing radical a.
    have hbase : ∃ u : Kˣ, F u = (a : Lˣ) := MonoidHom.mem_range.mp ha
    refine Exists.elim hbase ?_
    intro u hu
    -- R2: evaluate that original units equality in L.
    have huval := congrArg (fun z : Lˣ ↦ (z : L)) hu
    change ((Units.map (algebraMap K L).toMonoidHom u : Lˣ) : L) =
      ((a : Lˣ) : L) at huval
    change algebraMap K L (u : K) = ((a : Lˣ) : L) at huval
    -- R3: use the formula at the same a and identify the same base-unit power.
    have h := Cox.ClassFieldTheory.Kummer.radicalPowerHom_apply K L n a
    rw [← huval, ← map_pow (algebraMap K L) (u : K) n,
      ← Units.val_pow_eq_pow_val (a := u) n] at h
    -- R4: reflect the equality first to K values, then to K units.
    have hunit : radicalPowerHom K L n a = u ^ n :=
      Units.ext ((algebraMap K L).injective h)
    -- R5: return the same u, orienting its power equation for range membership.
    change ∃ w : Kˣ, w ^ n = radicalPowerHom K L n a
    exact Exists.intro u hunit.symm

/-- The actual power map followed by the quotient of its image by base nth powers. -/
def radicalPowerQuotientHom (n : ℕ) : radicalUnits K L n →*
    (radicalPowerRange K L n ⧸ (nthPowers K n).subgroupOf (radicalPowerRange K L n)) :=
  (QuotientGroup.mk' ((nthPowers K n).subgroupOf (radicalPowerRange K L n))).comp
    (radicalPowerHom K L n).rangeRestrict

/-- The power quotient map is onto its actual image quotient. -/
theorem radicalPowerQuotientHom_surjective (n : ℕ) :
    Function.Surjective (radicalPowerQuotientHom K L n) := by
  exact (QuotientGroup.mk'_surjective _).comp (radicalPowerHom K L n).rangeRestrict_surjective

/-- The kernel required by the first isomorphism theorem for the power quotient. -/
theorem radicalPowerQuotientHom_ker (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) :
    (radicalPowerQuotientHom K L n).ker =
      (baseUnits K L).subgroupOf (radicalUnits K L n) := by
  rw [← radicalPowerHom_preimage_nthPowers K L n hn ζ hζ]
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  change QuotientGroup.mk ((radicalPowerHom K L n).rangeRestrict a) = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

/-- Roots differing by an nth root of unity have the same class modulo base units. -/
theorem radical_power_quotient_equiv (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) :
    Nonempty ((radicalUnits K L n ⧸ (baseUnits K L).subgroupOf (radicalUnits K L n)) ≃*
      (radicalPowerRange K L n ⧸ (nthPowers K n).subgroupOf (radicalPowerRange K L n))) := by
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (radicalPowerQuotientHom_ker K L n hn ζ hζ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (radicalPowerQuotientHom_surjective K L n))⟩

variable [hGalois : IsGalois K L]
include hGalois

/-- An element fixed by every automorphism of a finite Galois extension is a base unit. -/
theorem mem_baseUnits_of_fixed [FiniteDimensional K L] (a : Lˣ)
    (h : ∀ σ : L ≃ₐ[K] L, σ (a : L) = a) : a ∈ baseUnits K L := by
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (a : L)).mpr h
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact Units.ne_zero a (by rw [← hb, map_zero])
  exact ⟨Units.mk0 b hb0, Units.ext (by simpa using hb)⟩

/-- If the Galois exponent divides n, a character eigenvector has nth power in K. -/
theorem eigenvector_mem_radicalUnits [FiniteDimensional K L] (n : ℕ) (χ : (L ≃ₐ[K] L) →* Kˣ)
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1)
    (a : Lˣ) (ha : ∀ σ : L ≃ₐ[K] L,
      σ (a : L) / (a : L) = algebraMap K L ((χ σ : Kˣ) : K)) :
    a ∈ radicalUnits K L n := by
  change a ^ n ∈ baseUnits K L
  apply mem_baseUnits_of_fixed K L
  intro σ
  have hσa : σ (a : L) = algebraMap K L ((χ σ : Kˣ) : K) * a := by
    rw [← ha σ, div_mul_cancel₀ _ (Units.ne_zero a)]
  have hc : (algebraMap K L ((χ σ : Kˣ) : K)) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow χ, hexp σ, map_one, Units.val_one,
      map_one]
  rw [Units.val_pow_eq_pow_val, map_pow, hσa, mul_pow, hc, one_mul]

/-- A radical has trivial character exactly when it is an embedded base unit. -/
theorem radicalCharacterHom_ker [FiniteDimensional K L] (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) :
    (radicalCharacterHom K L n hn ζ hζ).ker =
      (baseUnits K L).subgroupOf (radicalUnits K L n) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    apply mem_baseUnits_of_fixed K L
    intro σ
    have h1 := radicalCharacterHom_apply K L n hn ζ hζ a σ
    rw [h, MonoidHom.one_apply, Units.val_one, map_one, eq_comm,
      div_eq_one_iff_eq (Units.ne_zero _)] at h1
    exact h1
  · rintro ⟨u, hu⟩
    refine MonoidHom.ext fun σ => Units.ext ((algebraMap K L).injective ?_)
    rw [radicalCharacterHom_apply, MonoidHom.one_apply, Units.val_one, map_one, ← hu,
      Units.coe_map]
    change σ (algebraMap K L (u : K)) / algebraMap K L (u : K) = 1
    rw [σ.commutes]
    exact div_self ((algebraMap K L).injective.ne_iff' (map_zero _) |>.mpr (Units.ne_zero u))

/-- Hilbert 90 makes the character map surjective when the Galois exponent divides n. -/
theorem radicalCharacterHom_surjective [FiniteDimensional K L] (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1) :
    Function.Surjective (radicalCharacterHom K L n hn ζ hζ) := by
  intro χ
  obtain ⟨a, ha⟩ := character_has_eigenvector K L χ
  refine ⟨⟨a, eigenvector_mem_radicalUnits K L n χ hexp a ha⟩, ?_⟩
  refine MonoidHom.ext fun σ => Units.ext ((algebraMap K L).injective ?_)
  rw [radicalCharacterHom_apply]
  exact ha σ

/-- The first isomorphism theorem identifies M/K* with the full character group. -/
theorem radical_quotient_equiv_characters [FiniteDimensional K L] (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1) :
    Nonempty ((radicalUnits K L n ⧸ (baseUnits K L).subgroupOf (radicalUnits K L n)) ≃*
      ((L ≃ₐ[K] L) →* Kˣ)) := by
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (radicalCharacterHom_ker K L n hn ζ hζ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (radicalCharacterHom_surjective K L n hn ζ hζ hexp))⟩

omit hGalois in
/-- Primitive roots supply the exponent-specific hypothesis used by finite duality. -/
theorem enough_roots_of_exponent (G : Type*) [CommGroup G] [Finite G]
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (hexp : ∀ g : G, g ^ n = 1) : HasEnoughRootsOfUnity K (Monoid.exponent G) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : HasEnoughRootsOfUnity K n := ⟨⟨ζ, hζ⟩, inferInstance⟩
  exact HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hexp)

omit hGalois in
/-- The radical quotient is finite through its character-group equivalence. -/
theorem radical_quotient_finite [FiniteDimensional K L] [IsAbelianGalois K L]
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1) :
    Finite (radicalUnits K L n ⧸ (baseUnits K L).subgroupOf (radicalUnits K L n)) := by
  obtain ⟨e⟩ := radical_quotient_equiv_characters K L n hn ζ hζ hexp
  have hchar : Finite ((L ≃ₐ[K] L) →* Kˣ) := by
    open scoped IsMulCommutative in
    exact (by
      haveI := enough_roots_of_exponent K (L ≃ₐ[K] L) n hn ζ hζ hexp
      obtain ⟨d⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) K
      exact Finite.of_equiv _ d.toEquiv.symm)
  exact Finite.of_equiv _ e.toEquiv.symm

omit hGalois in
/-- Finite duality applied after the ratio isomorphism gives the radical quotient order. -/
theorem radical_quotient_card [FiniteDimensional K L] [IsAbelianGalois K L]
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1) :
    Nat.card (radicalUnits K L n ⧸ (baseUnits K L).subgroupOf (radicalUnits K L n)) =
      Module.finrank K L := by
  obtain ⟨e⟩ := radical_quotient_equiv_characters K L n hn ζ hζ hexp
  rw [Nat.card_congr e.toEquiv, ← IsGalois.card_aut_eq_finrank]
  open scoped IsMulCommutative in
  exact (by
    haveI := enough_roots_of_exponent K (L ≃ₐ[K] L) n hn ζ hζ hexp
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) K)

end Kummer

variable (K : Type*) [Field K] [hNK : NumberField K]
include hNK

/-- Janusz V.8.1: Hilbert 90 and finite character separation show that radical elements
separate automorphisms of a Kummer extension. -/
theorem kummer_radicals_separate (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    ∃ a : Lˣ, (∃ b : K, (a : L) ^ n = algebraMap K L b) ∧ σ (a : L) ≠ a := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  obtain ⟨χ, hχ⟩ : ∃ χ : (L ≃ₐ[K] L) →* Kˣ, χ σ ≠ 1 := by
    open scoped IsMulCommutative in
    exact (by
      haveI := Kummer.enough_roots_of_exponent K (L ≃ₐ[K] L) n hn ζ hζ hexp
      exact CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) K hσ)
  obtain ⟨a, ha⟩ := Kummer.character_has_eigenvector K L χ
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (Kummer.eigenvector_mem_radicalUnits K L n χ hexp a ha)
  refine ⟨a, ⟨(u : K), ?_⟩, ?_⟩
  · have h := congrArg (fun v : Lˣ => (v : L)) hu
    simp only [Units.coe_map, powMonoidHom_apply, Units.val_pow_eq_pow_val] at h
    exact h.symm
  · intro h
    apply hχ
    have h1 := ha σ
    rw [h, div_self (Units.ne_zero a)] at h1
    exact Units.ext ((algebraMap K L).injective (h1.symm.trans (map_one _).symm))

/-- Janusz V.8.1: radical elements generate a finite abelian extension of exponent n. -/
theorem kummer_adjoin_radicals_eq_top (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1) :
    IntermediateField.adjoin K {a : L | ∃ b : K, a ^ n = algebraMap K L b} = ⊤ := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  set E := IntermediateField.adjoin K {a : L | ∃ b : K, a ^ n = algebraMap K L b} with hE
  have hfix : E.fixingSubgroup = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    by_contra hne
    obtain ⟨a, ⟨b, hb⟩, ha⟩ := kummer_radicals_separate K L n hn ζ hζ hexp σ hne
    exact ha ((IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ (a : L)
      (IntermediateField.subset_adjoin K _ ⟨b, hb⟩))
  rw [← IsGalois.fixedField_fixingSubgroup E, hfix, IntermediateField.fixedField_bot]

namespace Kummer

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
/-- Finite quotient representatives reduce the radical field to finitely many radicands. -/
theorem exists_finite_radicands (n : ℕ) (hn : 0 < n) (W : Subgroup Kˣ)
    [Finite (W ⧸ (nthPowers K n).subgroupOf W)] :
    ∃ T : Finset W, radicalField K n W =
      IntermediateField.adjoin K {a : AlgebraicClosure K |
        ∃ w ∈ T, a ^ n = algebraMap K (AlgebraicClosure K) ((w : Kˣ) : K)} := by
  classical
  letI := Fintype.ofFinite (W ⧸ (nthPowers K n).subgroupOf W)
  let rep : (W ⧸ (nthPowers K n).subgroupOf W) → W := fun q => q.out
  refine ⟨Finset.univ.image rep, le_antisymm ?_ ?_⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨w, hwW, hx⟩
    set q : W ⧸ (nthPowers K n).subgroupOf W := QuotientGroup.mk ⟨w, hwW⟩
    have ht : (QuotientGroup.mk (rep q) : W ⧸ (nthPowers K n).subgroupOf W) = q :=
      QuotientGroup.out_eq' q
    have hmem := QuotientGroup.eq.mp ht
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hmem
    rw [powMonoidHom_apply] at hv
    have hvK : ((rep q : W) : Kˣ) = w * (v⁻¹) ^ n := by
      have h1 : ((rep q : W) : Kˣ)⁻¹ * w = v ^ n := by
        rw [hv]
        rfl
      rw [inv_pow, ← h1]
      group
    have hroot : (x * algebraMap K (AlgebraicClosure K) ((v⁻¹ : Kˣ) : K)) ^ n =
        algebraMap K (AlgebraicClosure K) (((rep q : W) : Kˣ) : K) := by
      rw [mul_pow, hx, ← map_pow, ← map_mul, hvK, Units.val_mul, Units.val_pow_eq_pow_val]
    have hmemT : x * algebraMap K (AlgebraicClosure K) ((v⁻¹ : Kˣ) : K) ∈
        IntermediateField.adjoin K {a : AlgebraicClosure K | ∃ w ∈ Finset.univ.image rep,
          a ^ n = algebraMap K (AlgebraicClosure K) ((w : Kˣ) : K)} :=
      IntermediateField.subset_adjoin K _ ⟨rep q, Finset.mem_image_of_mem _ (Finset.mem_univ _),
        hroot⟩
    have hx' : x = x * algebraMap K (AlgebraicClosure K) ((v⁻¹ : Kˣ) : K) *
        algebraMap K (AlgebraicClosure K) ((v : Kˣ) : K) := by
      rw [mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
        mul_one]
    rw [SetLike.mem_coe, hx']
    exact IntermediateField.mul_mem _ hmemT (IntermediateField.algebraMap_mem _ _)
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨t, -, hx⟩
    exact IntermediateField.subset_adjoin K _ ⟨(t : Kˣ), t.2, hx⟩

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Each finite family of nonzero radicands has a finite set of nth roots. -/
theorem finite_roots_of_radicands (n : ℕ) (hn : 0 < n) (W : Subgroup Kˣ) (T : Finset W) :
    Set.Finite {a : AlgebraicClosure K |
      ∃ w ∈ T, a ^ n = algebraMap K (AlgebraicClosure K) ((w : Kˣ) : K)} := by
  have h : {a : AlgebraicClosure K |
      ∃ w ∈ T, a ^ n = algebraMap K (AlgebraicClosure K) ((w : Kˣ) : K)} =
      ⋃ w ∈ T, {a | (Polynomial.X ^ n - Polynomial.C (algebraMap K (AlgebraicClosure K)
        ((w : Kˣ) : K))).IsRoot a} := by
    ext a
    simp [sub_eq_zero]
  rw [h]
  exact Set.Finite.biUnion T.finite_toSet fun w _ =>
    Polynomial.finite_setOf_isRoot (Polynomial.X_pow_sub_C_ne_zero hn _)

end Kummer

/-- Janusz V.8.1: finite radical quotient implies a finite radical field. -/
theorem radicalField_finiteDimensional (n : ℕ) (hn : 0 < n) (W : Subgroup Kˣ)
    [Finite (W ⧸ (nthPowers K n).subgroupOf W)] :
    FiniteDimensional K (radicalField K n W) := by
  obtain ⟨T, hT⟩ := Kummer.exists_finite_radicands K n hn W
  haveI := (Kummer.finite_roots_of_radicands K n hn W T).to_subtype
  haveI : FiniteDimensional K (IntermediateField.adjoin K {a : AlgebraicClosure K |
      ∃ w ∈ T, a ^ n = algebraMap K (AlgebraicClosure K) ((w : Kˣ) : K)}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact (IntermediateField.equivOfEq hT.symm).toLinearEquiv.finiteDimensional

namespace Kummer

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
/-- The radical field is normal because it contains all roots of every defining polynomial. -/
theorem radicalField_normal (n : ℕ) (hn : 0 < n) (W : Subgroup Kˣ) :
    Normal K (radicalField K n W) := by
  rw [IntermediateField.normal_iff_forall_map_le]
  intro σ
  rw [radicalField, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, ⟨w, hwW, hx⟩, rfl⟩
  refine IntermediateField.subset_adjoin K _ ⟨w, hwW, ?_⟩
  rw [← map_pow, hx, AlgHom.commutes]

omit hNK in
/-- An automorphism of the radical field scales each defining root by a base root of unity. -/
theorem radicalField_aut_generator (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (W : Subgroup Kˣ)
    (σ : radicalField K n W ≃ₐ[K] radicalField K n W) (x : radicalField K n W) (w : Kˣ)
    (hx : (x : AlgebraicClosure K) ^ n = algebraMap K (AlgebraicClosure K) (w : K)) :
    ∃ c : Kˣ, c ^ n = 1 ∧ σ x = algebraMap K (radicalField K n W) (c : K) * x := by
  have hxw : x ^ n = algebraMap K (radicalField K n W) (w : K) := Subtype.ext hx
  have hw0 : algebraMap K (radicalField K n W) (w : K) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero w)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hxw
    exact hw0 hxw.symm
  have h1 : (σ x / x) ^ n = 1 := by
    rw [div_pow, ← map_pow, hxw, AlgEquiv.commutes, div_self hw0]
  obtain ⟨u, hu⟩ := rootOfUnity_mem_base K (radicalField K n W) n hn ζ hζ (σ x / x) h1
  refine ⟨u, ?_, ?_⟩
  · apply Units.ext
    apply (algebraMap K (radicalField K n W)).injective
    rw [Units.val_pow_eq_pow_val, map_pow, hu, h1, Units.val_one, map_one]
  · rw [hu, div_mul_cancel₀ _ hx0]

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Scaling radical generators by base roots of unity gives exponent dividing n. -/
theorem radicalField_aut_pow (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (W : Subgroup Kˣ)
    (σ : radicalField K n W ≃ₐ[K] radicalField K n W) : σ ^ n = 1 := by
  apply AlgEquiv.coe_algHom_injective
  apply IntermediateField.algHom_ext_of_eq_adjoin K (S := radicalField K n W) rfl
  rintro x ⟨w, hwW, hx⟩
  obtain ⟨c, hc, hσ⟩ := radicalField_aut_generator K n hn ζ hζ W σ
    ⟨x, IntermediateField.subset_adjoin K _ ⟨w, hwW, hx⟩⟩ w hx
  have hpow : ∀ k : ℕ, (σ ^ k) ⟨x, IntermediateField.subset_adjoin K _ ⟨w, hwW, hx⟩⟩ =
      algebraMap K (radicalField K n W) ((c : K) ^ k) *
        ⟨x, IntermediateField.subset_adjoin K _ ⟨w, hwW, hx⟩⟩ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, AlgEquiv.commutes, hσ, pow_succ,
        map_mul]
      ring
  change (σ ^ n) _ = (1 : radicalField K n W ≃ₐ[K] radicalField K n W) _
  rw [hpow n, AlgEquiv.one_apply, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one,
    one_mul]

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Base-valued radical ratios make all automorphisms commute. -/
theorem radicalField_aut_commute (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (W : Subgroup Kˣ)
    (σ τ : radicalField K n W ≃ₐ[K] radicalField K n W) : Commute σ τ := by
  apply AlgEquiv.coe_algHom_injective
  apply IntermediateField.algHom_ext_of_eq_adjoin K (S := radicalField K n W) rfl
  rintro x ⟨w, hwW, hx⟩
  obtain ⟨c, -, hσ⟩ := radicalField_aut_generator K n hn ζ hζ W σ
    ⟨x, IntermediateField.subset_adjoin K _ ⟨w, hwW, hx⟩⟩ w hx
  obtain ⟨d, -, hτ⟩ := radicalField_aut_generator K n hn ζ hζ W τ
    ⟨x, IntermediateField.subset_adjoin K _ ⟨w, hwW, hx⟩⟩ w hx
  change (σ * τ) _ = (τ * σ) _
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτ, map_mul, AlgEquiv.commutes, hσ, map_mul,
    AlgEquiv.commutes, hτ]
  ring

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Independent cyclic coordinates in the finite radicand quotient. -/
theorem exists_independent_quotient_generators (n : ℕ) (W : Subgroup Kˣ)
    [Finite (W ⧸ (nthPowers K n).subgroupOf W)] :
    ∃ r : ℕ, ∃ d : Fin r → ℕ, ∃ a : Fin r → W,
      (∀ i, 0 < d i) ∧
      ∃ e : (W ⧸ (nthPowers K n).subgroupOf W) ≃* (∀ i, Multiplicative (ZMod (d i))),
        ∀ i, e (QuotientGroup.mk (a i)) = Pi.mulSingle i (Multiplicative.ofAdd 1) := by
  obtain ⟨ι, hι, dι, hdι, ⟨e₀⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite (W ⧸ (nthPowers K n).subgroupOf W)
  let f := Fintype.equivFin ι
  let d : Fin (Fintype.card ι) → ℕ := fun j => dι (f.symm j)
  let e₁ : (∀ i : ι, Multiplicative (ZMod (dι i))) ≃*
      (∀ j : Fin (Fintype.card ι), Multiplicative (ZMod (d j))) :=
    { Equiv.piCongrLeft' (fun i => Multiplicative (ZMod (dι i))) f with
      map_mul' := fun x y => rfl }
  let e := e₀.trans e₁
  refine ⟨Fintype.card ι, d,
    fun j => (e.symm (Pi.mulSingle j (Multiplicative.ofAdd 1))).out, ?_, e, fun j => ?_⟩
  · exact fun j => lt_trans zero_lt_one (hdι (f.symm j))
  · rw [QuotientGroup.out_eq', MulEquiv.apply_symm_apply]

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- If the radicand class has order d, an nth root has degree at most d. -/
theorem radical_simple_finrank_le (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (w : Kˣ) (d : ℕ) (hd : 0 < d)
    (hpow : w ^ d ∈ nthPowers K n) (a : AlgebraicClosure K)
    (ha : a ^ n = algebraMap K (AlgebraicClosure K) (w : K)) :
    Module.finrank K (IntermediateField.adjoin K {a}) ≤ d := by
  obtain ⟨c₀, hc₀⟩ := MonoidHom.mem_range.mp hpow
  rw [powMonoidHom_apply] at hc₀
  have hb0 : algebraMap K (AlgebraicClosure K) (c₀ : K) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero c₀)
  have h1 : (a ^ d / algebraMap K (AlgebraicClosure K) (c₀ : K)) ^ n = 1 := by
    have hbn : algebraMap K (AlgebraicClosure K) (c₀ : K) ^ n = (a ^ n) ^ d := by
      rw [ha, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hc₀]
    rw [div_pow, ← pow_mul, mul_comm d n, pow_mul, ← hbn, div_self (pow_ne_zero _ hb0)]
  obtain ⟨c, hc⟩ := rootOfUnity_mem_base K (AlgebraicClosure K) n hn ζ hζ _ h1
  have had : a ^ d = algebraMap K (AlgebraicClosure K) ((c : K) * c₀) := by
    rw [map_mul, hc, div_mul_cancel₀ _ hb0]
  have hint : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  rw [IntermediateField.adjoin.finrank hint]
  have hmonic : (Polynomial.X ^ d - Polynomial.C ((c : K) * c₀)).Monic :=
    Polynomial.monic_X_pow_sub_C _ hd.ne'
  have hroot : Polynomial.aeval a (Polynomial.X ^ d - Polynomial.C ((c : K) * c₀)) = 0 := by
    simp [had]
  have hdeg := minpoly.min K a hmonic hroot
  rw [Polynomial.degree_X_pow_sub_C hd] at hdeg
  exact Polynomial.natDegree_le_of_degree_le hdeg

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- A generating family modulo existing nth powers suffices to generate the radical
field after choosing one root of each generator, because μₙ lies in the base. -/
theorem radicalField_eq_adjoin_generators (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (W : Subgroup Kˣ) (r : ℕ) (a : Fin r → W)
    (hgen : Subgroup.closure (Set.range (fun i =>
      (QuotientGroup.mk (a i) : W ⧸ (nthPowers K n).subgroupOf W))) = ⊤)
    (b : Fin r → AlgebraicClosure K)
    (hb : ∀ i, b i ^ n = algebraMap K (AlgebraicClosure K) ((a i : Kˣ) : K)) :
    radicalField K n W = IntermediateField.adjoin K (Set.range b) := by
  set E := IntermediateField.adjoin K (Set.range b) with hE
  have hbE : ∀ i, b i ∈ E := fun i => IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  have hroot : ∀ q : W ⧸ (nthPowers K n).subgroupOf W, ∀ w : W,
      (QuotientGroup.mk w : W ⧸ (nthPowers K n).subgroupOf W) = q →
      ∃ y ∈ E, y ≠ 0 ∧ y ^ n = algebraMap K (AlgebraicClosure K) ((w : Kˣ) : K) := by
    intro q
    have hq : q ∈ Subgroup.closure (Set.range (fun i =>
        (QuotientGroup.mk (a i) : W ⧸ (nthPowers K n).subgroupOf W))) := hgen ▸ Subgroup.mem_top q
    induction hq using Subgroup.closure_induction with
    | mem q hq' =>
      obtain ⟨i, rfl⟩ := hq'
      intro w hw
      have hmem := QuotientGroup.eq.mp hw.symm
      rw [Subgroup.mem_subgroupOf] at hmem
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hmem
      rw [powMonoidHom_apply] at hv
      have hbi0 : b i ≠ 0 := by
        intro h
        have := hb i
        rw [h, zero_pow hn.ne'] at this
        exact Units.ne_zero (a i : Kˣ)
          ((algebraMap K (AlgebraicClosure K)).injective (by rw [← this, map_zero]))
      refine ⟨b i * algebraMap K (AlgebraicClosure K) (v : K), E.mul_mem (hbE i)
        (E.algebraMap_mem _), mul_ne_zero hbi0 ((map_ne_zero _).mpr (Units.ne_zero v)), ?_⟩
      have hw' : ((w : W) : Kˣ) = (a i : Kˣ) * v ^ n := by
        rw [hv]
        simp
      rw [mul_pow, hb i, ← map_pow, ← map_mul, hw', Units.val_mul, Units.val_pow_eq_pow_val]
    | one =>
      intro w hw
      have hmem := (QuotientGroup.eq_one_iff w).mp hw
      rw [Subgroup.mem_subgroupOf] at hmem
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hmem
      rw [powMonoidHom_apply] at hv
      refine ⟨algebraMap K (AlgebraicClosure K) (v : K), E.algebraMap_mem _,
        (map_ne_zero _).mpr (Units.ne_zero v), ?_⟩
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hv]
    | mul q₁ q₂ _ _ ih₁ ih₂ =>
      intro w hw
      obtain ⟨y₁, hy₁E, hy₁0, hy₁⟩ := ih₁ q₁.out (QuotientGroup.out_eq' q₁)
      obtain ⟨y₂, hy₂E, hy₂0, hy₂⟩ := ih₂ (q₁.out⁻¹ * w) (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', hw,
          inv_mul_cancel_left])
      refine ⟨y₁ * y₂, E.mul_mem hy₁E hy₂E, mul_ne_zero hy₁0 hy₂0, ?_⟩
      rw [mul_pow, hy₁, hy₂, ← map_mul, ← Units.val_mul]
      congr 2
      simp
    | inv q _ ih =>
      intro w hw
      obtain ⟨y, hyE, hy0, hy⟩ := ih w⁻¹ (by rw [QuotientGroup.mk_inv, hw, inv_inv])
      refine ⟨y⁻¹, E.inv_mem hyE, inv_ne_zero hy0, ?_⟩
      rw [inv_pow, hy, ← map_inv₀, ← Units.val_inv_eq_inv_val]
      simp
  apply le_antisymm
  · rw [radicalField, IntermediateField.adjoin_le_iff]
    rintro x ⟨w, hwW, hx⟩
    obtain ⟨y, hyE, hy0, hy⟩ := hroot _ ⟨w, hwW⟩ rfl
    have h1 : (x / y) ^ n = 1 := by rw [div_pow, hx, ← hy, div_self (pow_ne_zero _ hy0)]
    obtain ⟨c, hc⟩ := rootOfUnity_mem_base K (AlgebraicClosure K) n hn ζ hζ _ h1
    have hxy : x = algebraMap K (AlgebraicClosure K) (c : K) * y := by
      rw [hc, div_mul_cancel₀ _ hy0]
    rw [SetLike.mem_coe, hxy]
    exact E.mul_mem (E.algebraMap_mem _) hyE
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin K _ ⟨(a i : Kˣ), (a i).2, hb i⟩

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Coordinate generators generate every finite product of cyclic groups. -/
theorem independent_generators_generate (n : ℕ) (W : Subgroup Kˣ)
    (r : ℕ) (d : Fin r → ℕ) (a : Fin r → W)
    (e : (W ⧸ (nthPowers K n).subgroupOf W) ≃* (∀ i, Multiplicative (ZMod (d i))))
    (ha : ∀ i, e (QuotientGroup.mk (a i)) = Pi.mulSingle i (Multiplicative.ofAdd 1)) :
    Subgroup.closure (Set.range (fun i =>
      (QuotientGroup.mk (a i) : W ⧸ (nthPowers K n).subgroupOf W))) = ⊤ := by
  rw [eq_top_iff]
  intro q _
  have key : ∀ g : (∀ i, Multiplicative (ZMod (d i))), e.symm g ∈ Subgroup.closure
      (Set.range (fun i => (QuotientGroup.mk (a i) : W ⧸ (nthPowers K n).subgroupOf W))) := by
    intro g
    rw [← Finset.univ_prod_mulSingle g, map_prod]
    refine Subgroup.prod_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd (g i))
    have hgi : g i = (Multiplicative.ofAdd (1 : ZMod (d i))) ^ k := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_zpow, toAdd_ofAdd, zsmul_one, hk]
    rw [hgi, Pi.mulSingle_zpow, map_zpow, ← ha i, MulEquiv.symm_apply_apply]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _
  simpa using key (e q)

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- The simple-field degree bounds multiply under finite adjoining. -/
theorem finrank_adjoin_le_prod (r : ℕ) (b : Fin r → AlgebraicClosure K)
    (d : Fin r → ℕ)
    (hd : ∀ i, Module.finrank K (IntermediateField.adjoin K {b i}) ≤ d i) :
    Module.finrank K (IntermediateField.adjoin K (Set.range b)) ≤ ∏ i, d i := by
  induction r with
  | zero =>
    rw [Set.range_eq_empty b, IntermediateField.adjoin_empty, IntermediateField.finrank_bot]
    simp
  | succ r ih =>
    have hrange : Set.range b = {b 0} ∪ Set.range (fun i : Fin r => b i.succ) := by
      rw [← Set.insert_eq]
      conv_lhs => rw [← Fin.cons_self_tail b]
      rw [Fin.range_cons]
      rfl
    rw [hrange, IntermediateField.adjoin_union, Fin.prod_univ_succ]
    exact (IntermediateField.finrank_sup_le _ _).trans (Nat.mul_le_mul (hd 0)
      (ih (fun i => b i.succ) (fun i => d i.succ) (fun i => hd i.succ)))

/-- The independent radicands bound the full radical degree by the quotient order. -/
theorem radicalField_finrank_le (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (W : Subgroup Kˣ)
    [Finite (W ⧸ (nthPowers K n).subgroupOf W)] :
    Module.finrank K (radicalField K n W) ≤
      Nat.card (W ⧸ (nthPowers K n).subgroupOf W) := by
  obtain ⟨r, d, a, hd, e, ha⟩ := exists_independent_quotient_generators K n W
  have hgen := independent_generators_generate K n W r d a e ha
  choose b hb using fun i => IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) ((a i : Kˣ) : K)) hn
  rw [radicalField_eq_adjoin_generators K n hn ζ hζ W r a hgen b hb]
  refine (finrank_adjoin_le_prod K r b d fun i => ?_).trans (le_of_eq ?_)
  · refine radical_simple_finrank_le K n hn ζ hζ (a i : Kˣ) (d i) (hd i) ?_ (b i) (hb i)
    have hone : (Multiplicative.ofAdd (1 : ZMod (d i))) ^ d i = 1 := by
      rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero]
    have h1 : (QuotientGroup.mk (a i ^ d i) : W ⧸ (nthPowers K n).subgroupOf W) = 1 := by
      apply e.injective
      rw [map_one e, QuotientGroup.mk_pow, map_pow e, ha i, ← Pi.mulSingle_pow, hone,
        Pi.mulSingle_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end Kummer

/-- Janusz V.8.1: the roots-of-unity hypothesis makes a finite radical field abelian. -/
theorem radicalField_isAbelianGalois (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (W : Subgroup Kˣ)
    [Finite (W ⧸ (nthPowers K n).subgroupOf W)] :
    IsAbelianGalois K (radicalField K n W) := by
  haveI := radicalField_finiteDimensional K n hn W
  haveI := Kummer.radicalField_normal K n hn W
  haveI : Algebra.IsSeparable K (radicalField K n W) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois K (radicalField K n W) := ⟨⟩
  haveI : IsMulCommutative ((radicalField K n W) ≃ₐ[K] (radicalField K n W)) :=
    ⟨⟨fun σ τ => (Kummer.radicalField_aut_commute K n hn ζ hζ W σ τ).eq⟩⟩
  exact ⟨⟩

namespace Kummer

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Every original radicand acquires a nonzero nth root in its radical field. -/
theorem le_radicalPowerRange (n : ℕ) (hn : 0 < n) (W : Subgroup Kˣ) :
    W ≤ radicalPowerRange K (radicalField K n W) n := by
  intro w hw
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (w : K)) hn
  have hxmem : x ∈ radicalField K n W := IntermediateField.subset_adjoin K _ ⟨w, hw, hx⟩
  have hx0 : (⟨x, hxmem⟩ : radicalField K n W) ≠ 0 := by
    intro h
    have h' := congrArg Subtype.val h
    simp only [IntermediateField.coe_zero] at h'
    rw [h', zero_pow hn.ne'] at hx
    exact Units.ne_zero w ((algebraMap K (AlgebraicClosure K)).injective (by rw [← hx, map_zero]))
  let a : (radicalField K n W)ˣ := Units.mk0 _ hx0
  have hpow : algebraMap K (radicalField K n W) (w : K) = (a : radicalField K n W) ^ n :=
    Subtype.ext (by simp [a, hx])
  have ha : a ∈ radicalUnits K (radicalField K n W) n :=
    ⟨w, Units.ext (by rw [Units.coe_map]; exact hpow)⟩
  refine ⟨⟨a, ha⟩, Units.ext ((algebraMap K (radicalField K n W)).injective ?_)⟩
  rw [radicalPowerHom_apply, ← hpow]

/-- The source degree bound rules out extra radicand classes. Powers already in K
account for the saturation when W does not itself contain all nth powers. -/
theorem radicalPowerRange_radicalField (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (W : Subgroup Kˣ)
    [Finite (W ⧸ (nthPowers K n).subgroupOf W)] :
    radicalPowerRange K (radicalField K n W) n = W ⊔ nthPowers K n := by
  haveI := radicalField_finiteDimensional K n hn W
  haveI := radicalField_isAbelianGalois K n hn ζ hζ W
  have hexp := radicalField_aut_pow K n hn ζ hζ W
  have hNR : nthPowers K n ≤ radicalPowerRange K (radicalField K n W) n :=
    nthPowers_le_radicalPowerRange K (radicalField K n W) n
  have hWR : W ⊔ nthPowers K n ≤ radicalPowerRange K (radicalField K n W) n :=
    sup_le (le_radicalPowerRange K n hn W) hNR
  obtain ⟨e1⟩ := radical_power_quotient_equiv K (radicalField K n W) n hn ζ hζ
  have h1 : (nthPowers K n).relIndex (radicalPowerRange K (radicalField K n W) n) =
      Module.finrank K (radicalField K n W) := by
    rw [← radical_quotient_card K (radicalField K n W) n hn ζ hζ hexp, Nat.card_congr e1.toEquiv]
    rfl
  have e2 := QuotientGroup.quotientInfEquivProdNormalQuotient W (nthPowers K n)
  have h2 : Module.finrank K (radicalField K n W) ≤
      (nthPowers K n).relIndex (W ⊔ nthPowers K n) := by
    refine (radicalField_finrank_le K n hn ζ hζ W).trans (le_of_eq ?_)
    rw [Nat.card_congr e2.toEquiv]
    rfl
  have hmul := Subgroup.relIndex_mul_relIndex (nthPowers K n) (W ⊔ nthPowers K n)
    (radicalPowerRange K (radicalField K n W) n) le_sup_right hWR
  rw [h1] at hmul
  have hpos : 0 < Module.finrank K (radicalField K n W) := Module.finrank_pos
  have h3 : (W ⊔ nthPowers K n).relIndex (radicalPowerRange K (radicalField K n W) n) = 1 := by
    set x := (nthPowers K n).relIndex (W ⊔ nthPowers K n)
    set y := (W ⊔ nthPowers K n).relIndex (radicalPowerRange K (radicalField K n W) n)
    have hy0 : y ≠ 0 := by
      rintro hy
      rw [hy, mul_zero] at hmul
      omega
    have hy1 : y ≤ 1 := by
      by_contra hc
      have hc' : 2 ≤ y := by omega
      nlinarith
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h3) hWR

-- The unused section instance is kept: the planned signature includes it.
set_option linter.unusedSectionVars false in
/-- Noether's second isomorphism theorem removes the harmless power saturation. -/
theorem saturated_quotient_equiv (n : ℕ) (W : Subgroup Kˣ) :
    Nonempty ((W ⧸ (nthPowers K n).subgroupOf W) ≃*
      ((W ⊔ nthPowers K n : Subgroup Kˣ) ⧸ (nthPowers K n).subgroupOf (W ⊔ nthPowers K n))) := by
  exact ⟨QuotientGroup.quotientInfEquivProdNormalQuotient W (nthPowers K n)⟩

end Kummer

/-- Janusz V.8.1 / V.9.4: the Galois group is noncanonically isomorphic to the radical
quotient. The proof uses finite character duality, not a canonical identification. -/
theorem radicalField_galois_equiv (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (W : Subgroup Kˣ)
    [Finite (W ⧸ (nthPowers K n).subgroupOf W)] :
    Nonempty (((radicalField K n W) ≃ₐ[K] (radicalField K n W)) ≃*
      (W ⧸ (nthPowers K n).subgroupOf W)) := by
  haveI := radicalField_finiteDimensional K n hn W
  haveI := radicalField_isAbelianGalois K n hn ζ hζ W
  have hexp := Kummer.radicalField_aut_pow K n hn ζ hζ W
  obtain ⟨d⟩ : Nonempty (((radicalField K n W) ≃ₐ[K] (radicalField K n W)) ≃*
      (((radicalField K n W) ≃ₐ[K] (radicalField K n W)) →* Kˣ)) := by
    open scoped IsMulCommutative in
    exact (by
      haveI := Kummer.enough_roots_of_exponent K
        ((radicalField K n W) ≃ₐ[K] (radicalField K n W)) n hn ζ hζ hexp
      obtain ⟨d⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
        ((radicalField K n W) ≃ₐ[K] (radicalField K n W)) K
      exact ⟨d.symm⟩)
  obtain ⟨e1⟩ := Kummer.radical_quotient_equiv_characters K (radicalField K n W) n hn ζ hζ hexp
  have he2 := Kummer.radical_power_quotient_equiv K (radicalField K n W) n hn ζ hζ
  rw [Kummer.radicalPowerRange_radicalField K n hn ζ hζ W] at he2
  obtain ⟨e2⟩ := he2
  obtain ⟨e3⟩ := Kummer.saturated_quotient_equiv K n W
  exact ⟨d.trans (e1.symm.trans (e2.trans e3.symm))⟩

/-- Janusz V.8.1: the radical degree is the subgroup index used in the paired calculation. -/
theorem radicalField_finrank (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (W : Subgroup Kˣ)
    [Finite (W ⧸ (nthPowers K n).subgroupOf W)] :
    Module.finrank K (radicalField K n W) = ((nthPowers K n).subgroupOf W).index := by
  haveI := radicalField_finiteDimensional K n hn W
  haveI := radicalField_isAbelianGalois K n hn ζ hζ W
  obtain ⟨e⟩ := radicalField_galois_equiv K n hn ζ hζ W
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr e.toEquiv]
  rfl

end Cox.ClassFieldTheory
