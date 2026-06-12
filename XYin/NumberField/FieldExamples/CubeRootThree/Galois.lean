import XYin.NumberField.FieldExamples.CubeRootThree.Euclidean

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

/-! ## 9. Galois group and Galois closure -/

/-- The identity automorphism of `ℚ(∛3)`. -/
noncomputable def idAut : K ≃ₐ[ℚ] K := AlgEquiv.refl

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

/-- Every `ℚ`-automorphism of `K` fixes `θ`, hence equals the identity: an automorphism sends
`θ` to a cube root of `3`, but `K` contains only one (the other two differ by `ζ₃ ∉ K`). -/
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

/-- The extension `ℚ(∛3)/ℚ` is not Galois: it has `1 < 3` automorphisms. -/
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

/-- The Galois closure of `ℚ(∛3)/ℚ`: the splitting field of `X³ - 3`, mathematically
`ℚ(∛3, ζ₃)`. -/
abbrev galoisClosure : Type := cubePolynomial.SplittingField

/-- The splitting field of `X³ - 3` is Galois over `ℚ` (normal, and separable in
characteristic zero). -/
theorem isGalois_galoisClosure : IsGalois ℚ galoisClosure := by
  haveI : IsSplittingField ℚ galoisClosure cubePolynomial :=
    Polynomial.IsSplittingField.splittingField cubePolynomial
  exact IsGalois.of_separable_splitting_field
    ((Fact.out : Irreducible cubePolynomial).separable)

/-- `K = ℚ(∛3)` embeds into its Galois closure, as any one of three conjugate (non-normal)
cubic subfields. -/
theorem nonempty_algHom_galoisClosure : Nonempty (K →ₐ[ℚ] galoisClosure) := by
  have hdeg : (cubePolynomial.map (algebraMap ℚ galoisClosure)).degree ≠ 0 := by
    rw [Polynomial.degree_map, degree_X_pow_sub_C (by norm_num : 0 < 3)]
    norm_num
  obtain ⟨x, hx⟩ := (Polynomial.SplittingField.splits cubePolynomial).exists_eval_eq_zero hdeg
  refine ⟨AdjoinRoot.liftAlgHom cubePolynomial (Algebra.ofId ℚ galoisClosure) x ?_⟩
  rw [Polynomial.eval₂_eq_eval_map]
  exact hx

/-- The Galois group of the closure `ℚ(∛3, ζ₃)/ℚ` is the full symmetric group `S₃`, acting by
permuting the three cube roots of `3`: `X³ - 3` is irreducible of prime degree with exactly
two non-real roots. -/
theorem galoisClosureGroupStructure :
    Nonempty ((galoisClosure ≃ₐ[ℚ] galoisClosure) ≃* Equiv.Perm (Fin 3)) := by
  have hf : cubePolynomial ≠ 0 := by intro h; simpa using congrArg natDegree h
  have p_irr : Irreducible cubePolynomial := Fact.out
  have p_deg : cubePolynomial.natDegree.Prime := by
    rw [natDegree_X_pow_sub_C]
    exact Nat.prime_three
  have hC : Fintype.card (cubePolynomial.rootSet ℂ) = 3 := by
    rw [Polynomial.card_rootSet_eq_natDegree p_irr.separable (IsAlgClosed.splits _)]
    exact natDegree_X_pow_sub_C
  have hr3 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 3)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have haev : ∀ x : ℝ, (Polynomial.aeval x) cubePolynomial = x ^ 3 - 3 := by
    intro x; simp [cubePolynomial]
  have hR : Fintype.card (cubePolynomial.rootSet ℝ) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨(3 : ℝ) ^ ((1 : ℝ) / 3), ?_⟩, ?_⟩
    · rw [Polynomial.mem_rootSet]
      exact ⟨hf, by rw [haev, hr3]; ring⟩
    · rintro ⟨y, hy⟩
      rw [Polynomial.mem_rootSet, haev] at hy
      have hy3 : y ^ (3 : ℕ) = ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by
        rw [hr3]
        have := hy.2
        nlinarith [hy.2]
      have hinj := (Odd.strictMono_pow (R := ℝ) (by norm_num : Odd 3)).injective
      exact Subtype.ext (hinj hy3)
  have hroots : Fintype.card (cubePolynomial.rootSet ℂ) =
      Fintype.card (cubePolynomial.rootSet ℝ) + 2 := by rw [hC, hR]
  have hbij := Polynomial.Gal.galActionHom_bijective_of_prime_degree p_irr p_deg hroots
  exact ⟨(MulEquiv.ofBijective _ hbij).trans (Fintype.equivFinOfCardEq hC).permCongrHom⟩

/-- The Galois closure `ℚ(∛3, ζ₃)` has degree `6 = |S₃| = [ℚ(∛3) : ℚ] · [ℚ(ζ₃) : ℚ]` over
`ℚ`: the closure is Galois, so its degree is the order of its Galois group. -/
theorem finrank_galoisClosure : Module.finrank ℚ galoisClosure = 6 := by
  haveI : IsGalois ℚ galoisClosure := isGalois_galoisClosure
  obtain ⟨e⟩ := galoisClosureGroupStructure
  have hcard := IsGalois.card_aut_eq_finrank ℚ galoisClosure
  rw [← hcard, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  simp [Fintype.card_perm]
  rfl


end NumberField.CubeRootThree
