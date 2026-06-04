import Mathlib

/-!
# The field `ℚ(∛3)` via `AdjoinRoot`
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace XYin.NumberField.New.CubeRootThree

/-! ## 1. Basics -/

/-- The polynomial `X^3 - 3` over `ℚ`, defining `ℚ(∛3)`. -/
abbrev cubePolynomial : ℚ[X] := X ^ 3 - C (3 : ℚ)

/-- The polynomial `X^3 - 3` is irreducible over `ℚ`. -/
instance : Fact (Irreducible cubePolynomial) := by
  refine ⟨X_pow_sub_C_irreducible_of_prime (by norm_num) ?_⟩
  intro b hb
  have hint : IsIntegral ℤ b := by
    refine ⟨X ^ 3 - C 3, ?_, ?_⟩
    · monicity!
    · simp [hb]
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hn] at hb
  simp only [algebraMap_int_eq, eq_intCast] at hb
  have hn3 : n ^ 3 = 3 := by exact_mod_cast hb
  have hdvd : n ∣ 3 := ⟨n ^ 2, by rw [← hn3]; ring⟩
  have h2 : n ≤ 3 := Int.le_of_dvd (by norm_num) hdvd
  have h3 : -3 ≤ n := by
    have := Int.le_of_dvd (show (0 : ℤ) < 3 by norm_num) ((neg_dvd).mpr hdvd); linarith
  interval_cases n <;> omega

/-- The number field `ℚ(∛3)` as an `AdjoinRoot`. -/
abbrev K : Type := AdjoinRoot cubePolynomial

/-- The distinguished cube root of `3`. -/
abbrev cubeRootThree : K := AdjoinRoot.root cubePolynomial

/-- The field structure on `K`. -/
instance : Field K := by
  infer_instance

/-- The number-field structure on `K`. -/
instance : NumberField K := by
  infer_instance

/-- The ring of integers of `K`. -/
abbrev OK : Type := 𝓞 K

/-- The extension degree of `K = ℚ(∛3)` over `ℚ` is `3`. -/
theorem degree_eq_three : Module.finrank ℚ K = 3 := by
  have hf : cubePolynomial ≠ 0 := by
    intro h; simpa using congrArg natDegree h
  rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim hf]
  exact natDegree_X_pow_sub_C

/-! ## 2. Integral Basis -/

/-- The concrete integral-basis vectors `1, θ, θ²`, where `θ = ∛3`. -/
def integralBasisVectors : Fin 3 → K := ![1, cubeRootThree, cubeRootThree ^ 2]

/-- The concrete integral basis `1, θ, θ²` of `𝓞 K`. -/
noncomputable def concreteIntegralBasis : Basis (Fin 3) ℚ K := by
  sorry

/-- `NumberField.integralBasis K` agrees with the displayed integral basis, up to reindexing. -/
theorem numberField_integralBasis_eq :
    ∃ e : Fin 3 ≃ Free.ChooseBasisIndex ℤ OK,
      NumberField.integralBasis K = concreteIntegralBasis.reindex e := by
  sorry

/-! ## 3. Discriminant -/

/-- The number-field discriminant of `ℚ(∛3)` is `-243`. -/
theorem numberField_discr_eq : NumberField.discr K = (-243 : ℤ) := by
  sorry

/-! ## 4. Ring of integers -/

/-- The concrete order `ℤ[θ]` inside `K`, where `θ = ∛3`. -/
abbrev concreteRingOfIntegers : Type := Algebra.adjoin ℤ ({cubeRootThree} : Set K)

/-- The full ring of integers of `ℚ(∛3)` is `ℤ[θ]`. -/
theorem ringOfIntegers_eq : OK = concreteRingOfIntegers := by
  sorry

/-! ## 5. Ring of units -/

/-- A torsion generator of `𝓞 Kˣ`, mathematically `-1`. -/
abbrev torsionGenerator : OKˣ := -1

/-- The concrete torsion units `{1, -1}`. -/
def torsionUnits : Set OKˣ := {u | ∃ k : Fin 2, u = torsionGenerator ^ k.val}

/-- The torsion subgroup of `𝓞 Kˣ` is exactly `{1, -1}`. -/
theorem torsionUnits_eq : {u : OKˣ | IsOfFinOrder u} = torsionUnits := by
  sorry

/-- The torsion subgroup of `𝓞 Kˣ` has order `2`. -/
theorem torsionOrder_eq_two : NumberField.Units.torsionOrder K = 2 := by
  sorry

/-- The Dirichlet unit rank of `ℚ(∛3)` is `1`. -/
theorem unitRank_eq_one : NumberField.Units.rank K = 1 := by
  sorry

/-- A fundamental unit of `𝓞 K`, mathematically `θ² - 2`. -/
noncomputable def fundamentalUnit : OKˣ := by
  sorry

/-- The displayed singleton `{θ² - 2}` is a system of fundamental units. -/
def fundamentalUnitSystem : Set OKˣ := {fundamentalUnit}

/-- A system of fundamental units for `𝓞 Kˣ` is the singleton `{θ² - 2}`. -/
theorem fundamentalUnitSystem_eq :
    fundamentalUnitSystem = ({fundamentalUnit} : Set OKˣ) := by
  sorry

/-- The unit group is `μ₂ × ℤ` as an abstract abelian group. -/
theorem unitGroupStructure :
    Nonempty (OKˣ ≃* (Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ))) := by
  sorry

/-! ## 6. Class group -/

/-- The class number of `ℚ(∛3)` is `1`. -/
theorem classNumber_eq_one : NumberField.classNumber K = 1 := by
  sorry

/-- The class group of `𝓞 K` is trivial. -/
theorem classGroupStructure : Nonempty (ClassGroup OK ≃* Multiplicative (ZMod 1)) := by
  sorry

/-- The unit ideal as the concrete representative of the unique ideal class. -/
abbrev unitIdealRepresentative : (Ideal OK)⁰ := ⟨(⊤ : Ideal OK), by simp⟩

/-- Every ideal class is represented by the unit ideal. -/
theorem classGroupRepresentative (C : ClassGroup OK) :
    C = ClassGroup.mk0 unitIdealRepresentative := by
  sorry

/-! ## 7. Galois group -/

/-- The identity automorphism of `ℚ(∛3)`. -/
noncomputable def idAut : K ≃ₐ[ℚ] K := AlgEquiv.refl

/-- The extension `ℚ(∛3)/ℚ` is not Galois. -/
theorem not_isGalois : ¬ IsGalois ℚ K := by
  sorry

/-- The `ℚ`-automorphism group of `ℚ(∛3)` is trivial. -/
theorem galoisGroupStructure : Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 1)) := by
  sorry

/-- The identity automorphism sends `θ = ∛3` to itself. -/
theorem idAut_apply_cubeRootThree : idAut cubeRootThree = cubeRootThree := by
  rfl

/-- Every `ℚ`-automorphism of `ℚ(∛3)` is the identity. -/
theorem automorphism_eq_id (σ : K ≃ₐ[ℚ] K) : σ = idAut := by
  sorry

/-- The identity automorphism is the unique element of the automorphism group. -/
def galoisGroupElements : Set (K ≃ₐ[ℚ] K) := {idAut}

/-- The automorphism group consists exactly of the identity. -/
theorem galoisGroupElements_eq_univ : Set.univ = galoisGroupElements := by
  sorry

end XYin.NumberField.New.CubeRootThree
