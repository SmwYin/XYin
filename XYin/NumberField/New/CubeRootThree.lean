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
  have hodd : Odd (Module.finrank ℚ K) := by rw [degree_eq_three]; decide
  ext u
  simp only [Set.mem_setOf_eq, torsionUnits]
  constructor
  · intro hu
    have hmem : u ∈ NumberField.Units.torsion K := (CommGroup.mem_torsion _).mpr hu
    rcases NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank hodd ⟨u, hmem⟩ with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  · rintro ⟨k, rfl⟩
    have hgen : IsOfFinOrder (torsionGenerator) := by
      rw [isOfFinOrder_iff_pow_eq_one]; exact ⟨2, by norm_num, by rw [neg_one_sq]⟩
    exact hgen.pow

/-- The torsion subgroup of `𝓞 Kˣ` has order `2`. -/
theorem torsionOrder_eq_two : NumberField.Units.torsionOrder K = 2 := by
  apply NumberField.Units.torsionOrder_eq_two_of_odd_finrank
  rw [degree_eq_three]; decide

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
  rfl

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

/-- The generator `θ = ∛3` satisfies `θ³ = 3`. -/
theorem cubeRootThree_cube : cubeRootThree ^ 3 = 3 := by
  have h : (AdjoinRoot.mk cubePolynomial) (X ^ 3 - C 3) = 0 := AdjoinRoot.mk_self
  simp only [map_sub, map_pow, AdjoinRoot.mk_X, map_ofNat] at h
  linear_combination h

/-- `K = ℚ(∛3)` contains no primitive cube root of unity, since `ℚ(ζ₃)` has degree `2 ∤ 3`. -/
theorem no_primitive_cube_root (z : K) : z ^ 2 + z + 1 ≠ 0 := by
  intro hz
  have hz_int : IsIntegral ℚ z := Algebra.IsIntegral.isIntegral z
  have hirr : Irreducible (X ^ 2 + X + 1 : ℚ[X]) := by
    have h3 : (cyclotomic 3 ℚ) = X ^ 2 + X + 1 := by
      rw [cyclotomic_prime]; simp [Finset.sum_range_succ]; ring
    rw [← h3]; exact cyclotomic.irreducible_rat (by norm_num)
  have hroot : (aeval z) (X ^ 2 + X + 1 : ℚ[X]) = 0 := by
    simp only [map_add, map_pow, aeval_X, map_one]; exact hz
  have heq : (X ^ 2 + X + 1 : ℚ[X]) = minpoly ℚ z :=
    minpoly.eq_of_irreducible_of_monic hirr hroot (by monicity!)
  have hdvd : (minpoly ℚ z).natDegree ∣ Module.finrank ℚ K := minpoly.degree_dvd hz_int
  rw [← heq, degree_eq_three] at hdvd
  have h2 : (X ^ 2 + X + 1 : ℚ[X]).natDegree = 2 := by compute_degree!
  rw [h2] at hdvd; omega

/-- The only cube root of `1` in `K` is `1`. -/
theorem cube_root_one (w : K) (hw : w ^ 3 = 1) : w = 1 := by
  have hfac : (w - 1) * (w ^ 2 + w + 1) = 0 := by linear_combination hw
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (no_primitive_cube_root w)

/-- Every `ℚ`-automorphism of `K` fixes `θ`, hence equals the identity. -/
theorem aut_eq_id (σ : K ≃ₐ[ℚ] K) : σ = idAut := by
  have hθ3 : cubeRootThree ^ 3 = 3 := cubeRootThree_cube
  have hθ0 : cubeRootThree ≠ 0 := by intro h; rw [h] at hθ3; norm_num at hθ3
  have hσθ3 : (σ cubeRootThree) ^ 3 = 3 := by rw [← map_pow, hθ3, map_ofNat]
  have hw3 : (σ cubeRootThree / cubeRootThree) ^ 3 = 1 := by rw [div_pow, hσθ3, hθ3]; field_simp
  have hw1 : σ cubeRootThree / cubeRootThree = 1 := cube_root_one _ hw3
  have key : σ cubeRootThree = cubeRootThree := by rw [div_eq_one_iff_eq hθ0] at hw1; exact hw1
  have hAlg : σ.toAlgHom = idAut.toAlgHom := by
    apply AdjoinRoot.algHom_ext
    change σ cubeRootThree = idAut cubeRootThree
    rw [key]; rfl
  ext x
  exact AlgHom.congr_fun hAlg x

/-- The extension `ℚ(∛3)/ℚ` is not Galois. -/
theorem not_isGalois : ¬ IsGalois ℚ K := by
  intro h
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = Module.finrank ℚ K := IsGalois.card_aut_eq_finrank ℚ K
  rw [degree_eq_three] at hcard
  have huniq : Subsingleton (K ≃ₐ[ℚ] K) :=
    ⟨fun a b => by rw [aut_eq_id a, aut_eq_id b]⟩
  have h1 : Nat.card (K ≃ₐ[ℚ] K) = 1 := by
    rw [Nat.card_eq_one_iff_unique]; exact ⟨huniq, ⟨idAut⟩⟩
  omega

/-- The `ℚ`-automorphism group of `ℚ(∛3)` is trivial. -/
theorem galoisGroupStructure : Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 1)) := by
  haveI : Unique (K ≃ₐ[ℚ] K) := ⟨⟨idAut⟩, fun a => aut_eq_id a⟩
  exact ⟨MulEquiv.ofUnique⟩

/-- The identity automorphism sends `θ = ∛3` to itself. -/
theorem idAut_apply_cubeRootThree : idAut cubeRootThree = cubeRootThree := by
  rfl

/-- Every `ℚ`-automorphism of `ℚ(∛3)` is the identity. -/
theorem automorphism_eq_id (σ : K ≃ₐ[ℚ] K) : σ = idAut := aut_eq_id σ

/-- The identity automorphism is the unique element of the automorphism group. -/
def galoisGroupElements : Set (K ≃ₐ[ℚ] K) := {idAut}

/-- The automorphism group consists exactly of the identity. -/
theorem galoisGroupElements_eq_univ : Set.univ = galoisGroupElements := by
  ext σ
  simp only [Set.mem_univ, galoisGroupElements, Set.mem_singleton_iff, true_iff]
  exact automorphism_eq_id σ

end XYin.NumberField.New.CubeRootThree
