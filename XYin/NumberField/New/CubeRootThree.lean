import Mathlib

/-!
# The field `ℚ(∛3)` via `AdjoinRoot`

The pure cubic number field `K = ℚ(∛3)`, realised as `AdjoinRoot (X ^ 3 - 3)`, and its main
arithmetic invariants:

* degree `3`, integral basis `1, θ, θ²`, ring of integers `ℤ[θ]` (sections 1–2);
* discriminant `-243 = -3⁵` (section 3);
* the norm form `x³ + 3y³ + 9z³ - 9xyz` and its unit ("cubic Pell") equation (section 4);
* splitting of rational primes: `3` ramifies totally, `2` splits as (deg 1)·(deg 2), `7` is
  inert, `61` splits completely (section 5);
* unit group `{±1} × (θ² - 2)^ℤ`, signature `(1, 1)`, regulator `|log(∛9 - 2)|` (section 6);
* class number one (section 7);
* the norm-Euclidean property (section 8);
* trivial automorphism group, hence non-Galois; Galois closure `ℚ(∛3, ζ₃)` of degree `6` with
  Galois group `S₃` (section 9).
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

/-- The extension degree of `K = ℚ(∛3)` over `ℚ` is `3`. -/
theorem degree_eq_three : Module.finrank ℚ K = 3 := by
  have hf : cubePolynomial ≠ 0 := by
    intro h; simpa using congrArg natDegree h
  rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim hf]
  exact natDegree_X_pow_sub_C

/-- The generator `θ = ∛3` satisfies `θ³ = 3`. -/
theorem cubeRootThree_cube : cubeRootThree ^ 3 = 3 := by
  have h : (AdjoinRoot.mk cubePolynomial) (X ^ 3 - C 3) = 0 := AdjoinRoot.mk_self
  simp only [map_sub, map_pow, AdjoinRoot.mk_X, map_ofNat] at h
  linear_combination h

/-! ## 2. Integral basis and ring of integers -/

/-- The generator `θ = ∛3` is integral over `ℤ` (it is a root of `X³ - 3`), hence lies in
`𝓞 K`. -/
theorem cubeRootThree_integral : cubeRootThree ∈ integralClosure ℤ K := by
  have h : IsIntegral ℤ cubeRootThree := by
    refine ⟨X ^ 3 - C 3, by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [cubeRootThree_cube]; simp
  exact h

/-- `θ = ∛3` as an element of the ring of integers `𝓞 K`. -/
noncomputable def thetaInt : 𝓞 K := ⟨cubeRootThree, cubeRootThree_integral⟩

/-- The integral generator also satisfies `θ³ = 3` in `𝓞 K`. -/
theorem thetaInt_cube : thetaInt ^ 3 = 3 := by
  have ht : (algebraMap (𝓞 K) K) thetaInt = cubeRootThree :=
    NumberField.RingOfIntegers.map_mk cubeRootThree cubeRootThree_integral
  have : (algebraMap (𝓞 K) K) (thetaInt ^ 3) = (algebraMap (𝓞 K) K) 3 := by
    rw [map_pow, map_ofNat, ht, cubeRootThree_cube]
  exact FaithfulSMul.algebraMap_injective (𝓞 K) K this

/-- The displayed integral-basis vectors `1, θ, θ²` (as elements of `K`), where `θ = ∛3`. -/
def integralBasisVectors : Fin 3 → K := ![1, cubeRootThree, cubeRootThree ^ 2]

/-- An element of `ℤ[θ] = Algebra.adjoin ℤ {θ}` is exactly a `ℤ`-combination of `1, θ, θ²`. -/
theorem mem_adjoin_iff (x : K) :
    x ∈ Algebra.adjoin ℤ ({cubeRootThree} : Set K) ↔
      ∃ a b c : ℤ, x = a • (1 : K) + b • cubeRootThree + c • cubeRootThree ^ 2 := by
  constructor
  · intro hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      exact ⟨0, 1, 0, by rw [hy]; simp⟩
    | algebraMap r =>
      refine ⟨r, 0, 0, ?_⟩
      simp
    | add y z _ _ hy hz =>
      obtain ⟨a, b, c, rfl⟩ := hy
      obtain ⟨a', b', c', rfl⟩ := hz
      exact ⟨a + a', b + b', c + c', by module⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, b, c, rfl⟩ := hy
      obtain ⟨a', b', c', rfl⟩ := hz
      refine ⟨a * a' + 3 * (b * c' + c * b'), a * b' + b * a' + 3 * c * c',
        a * c' + b * b' + c * a', ?_⟩
      have h3 : cubeRootThree ^ 3 = (3 : K) := cubeRootThree_cube
      have h4 : cubeRootThree ^ 4 = 3 * cubeRootThree := by
        rw [show (4 : ℕ) = 3 + 1 by rfl, pow_succ, h3]
      ring_nf
      rw [show cubeRootThree ^ 3 = (3 : K) from h3,
        show cubeRootThree ^ 4 = 3 * cubeRootThree from h4]
      ring
  · rintro ⟨a, b, c, rfl⟩
    have hθ : cubeRootThree ∈ Algebra.adjoin ℤ ({cubeRootThree} : Set K) :=
      Algebra.subset_adjoin (Set.mem_singleton _)
    have h1 : (1 : K) ∈ Algebra.adjoin ℤ ({cubeRootThree} : Set K) := one_mem _
    have h2 : cubeRootThree ^ 2 ∈ Algebra.adjoin ℤ ({cubeRootThree} : Set K) := pow_mem hθ 2
    refine add_mem (add_mem (zsmul_mem h1 a) (zsmul_mem hθ b)) (zsmul_mem h2 c)

/-- Span form of `mem_adjoin_iff`: the `ℤ`-submodule of `ℤ[θ]` is the span of `1, θ, θ²`. -/
theorem span_adjoin_eq :
    Subalgebra.toSubmodule (Algebra.adjoin ℤ ({cubeRootThree} : Set K)) =
      Submodule.span ℤ (Set.range integralBasisVectors) := by
  ext x
  rw [Subalgebra.mem_toSubmodule, mem_adjoin_iff]
  constructor
  · rintro ⟨a, b, c, rfl⟩
    have h0 : integralBasisVectors 0 = 1 := rfl
    have h1 : integralBasisVectors 1 = cubeRootThree := rfl
    have h2 : integralBasisVectors 2 = cubeRootThree ^ 2 := rfl
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.smul_mem _ a (Submodule.subset_span ⟨0, h0⟩)
    · exact Submodule.smul_mem _ b (Submodule.subset_span ⟨1, h1⟩)
    · exact Submodule.smul_mem _ c (Submodule.subset_span ⟨2, h2⟩)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      fin_cases i
      · exact ⟨1, 0, 0, by simp [integralBasisVectors]⟩
      · exact ⟨0, 1, 0, by simp [integralBasisVectors]⟩
      · exact ⟨0, 0, 1, by simp [integralBasisVectors]⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, b, c, rfl⟩ := hy
      obtain ⟨a', b', c', rfl⟩ := hz
      exact ⟨a + a', b + b', c + c', by module⟩
    | smul r y _ hy =>
      obtain ⟨a, b, c, rfl⟩ := hy
      exact ⟨r * a, r * b, r * c, by module⟩

/-- The norm form of `ℚ(∛3)` in the basis `1, θ, θ²`: the field norm of `x + yθ + zθ²` is the
cubic form `x³ + 3y³ + 9z³ - 9xyz`. -/
theorem norm_eq_normForm (x y z : ℚ) :
    Algebra.norm ℚ (x • (1 : K) + y • cubeRootThree + z • cubeRootThree ^ 2) =
      x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z := by
  have hf : cubePolynomial ≠ 0 := by intro h; simpa using congrArg natDegree h
  have hdim : (AdjoinRoot.powerBasis hf).dim = 3 := by
    rw [AdjoinRoot.powerBasis_dim hf]; exact natDegree_X_pow_sub_C
  set pb := AdjoinRoot.powerBasis hf with hpb
  -- the integral basis `1, θ, θ²` as a genuine `Basis (Fin 3) ℚ K`
  set b : Basis (Fin 3) ℚ K := pb.basis.reindex (finCongr hdim) with hb
  have hbpow : ∀ i : Fin 3, b i = cubeRootThree ^ (i : ℕ) := by
    intro i
    rw [hb, Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen]; simp
  have hb0 : b 0 = 1 := by rw [hbpow]; simp
  have hb1 : b 1 = cubeRootThree := by rw [hbpow]; simp
  have hb2 : b 2 = cubeRootThree ^ 2 := by rw [hbpow]; simp
  -- the action of `θ` on the basis: `θ·1 = θ`, `θ·θ = θ²`, `θ·θ² = θ³ = 3·1`
  have hm0 : cubeRootThree * b 0 = b 1 := by rw [hb0, hb1, mul_one]
  have hm1 : cubeRootThree * b 1 = b 2 := by rw [hb1, hb2, sq]
  have hm2 : cubeRootThree * b 2 = (3 : ℚ) • b 0 := by
    rw [hb0, hb2, Algebra.smul_def, mul_one, ← pow_succ', cubeRootThree_cube]; norm_num
  -- the companion matrix of left-multiplication by `θ`
  have hM : Algebra.leftMulMatrix b cubeRootThree = !![0, 0, 3; 1, 0, 0; 0, 1, 0] := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    fin_cases j <;>
      simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
        show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl]
    · rw [hm0, Basis.repr_self]; fin_cases i <;> simp
    · rw [hm1, Basis.repr_self]; fin_cases i <;> simp
    · rw [hm2, map_smul, Basis.repr_self]; fin_cases i <;> simp
  rw [Algebra.norm_eq_matrix_det b, map_add, map_add, map_smul, map_smul, map_smul,
    map_one, map_pow, hM]
  have hsum : x • (1 : Matrix (Fin 3) (Fin 3) ℚ) + y • !![0, 0, 3; 1, 0, 0; 0, 1, 0]
      + z • (!![0, 0, 3; 1, 0, 0; 0, 1, 0]) ^ 2 = !![x, 3 * z, 3 * y; y, x, 3 * z; z, y, x] := by
    rw [show (!![0, 0, 3; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℚ) ^ 2
          = !![0, 3, 0; 0, 0, 3; 1, 0, 0] by
      rw [pow_two]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three]]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.smul_apply] <;> ring
  rw [hsum]
  simp [Matrix.det_fin_three]; ring

/-- The discriminant of the power basis `1, θ, θ²` of `ℚ(∛3)` is `-243 = -3⁵`. -/
theorem discr_powerBasis_eq :
    Algebra.discr ℚ (AdjoinRoot.powerBasis
      (show cubePolynomial ≠ 0 by intro h; simpa using congrArg natDegree h)).basis
      = (-243 : ℚ) := by
  have hf : cubePolynomial ≠ 0 := by intro h; simpa using congrArg natDegree h
  have hmonic : cubePolynomial.Monic := by monicity!
  set pb := AdjoinRoot.powerBasis hf with hpb
  have hgen : pb.gen = cubeRootThree := AdjoinRoot.powerBasis_gen hf
  have hfr : Module.finrank ℚ K = 3 := degree_eq_three
  rw [Algebra.discr_powerBasis_eq_norm, hfr]
  -- minpoly ℚ pb.gen = cubePolynomial = X³ - 3, derivative = 3X²
  have hmin : minpoly ℚ pb.gen = cubePolynomial :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hmonic hf
  rw [hmin, hgen]
  have hderiv : derivative cubePolynomial = C (3 : ℚ) * X ^ 2 := by
    simp only [cubePolynomial, derivative_sub, derivative_pow, derivative_X, derivative_C,
      Nat.cast_ofNat, mul_one, sub_zero]
  rw [hderiv]
  have haeval : (aeval cubeRootThree) (C (3 : ℚ) * X ^ 2) = (3 : ℚ) • cubeRootThree ^ 2 := by
    rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.smul_def]
  rw [haeval]
  have hnorm : Algebra.norm ℚ ((3 : ℚ) • cubeRootThree ^ 2) = 243 := by
    have h := norm_eq_normForm 0 0 3
    simp only [zero_smul, zero_add, mul_zero, zero_mul, sub_zero] at h
    rw [h]; norm_num
  rw [hnorm]
  norm_num

/-- Pure-`ℤ` divisibility input to the peeling step: if the norm form of `a + bθ + cθ²` is
`27`-divisible (it equals `N(3z) = 27·N(z)`), then `3 ∣ a`, `3 ∣ b`, `3 ∣ c`. -/
theorem three_dvd_of_normForm_eq (a b c m : ℤ)
    (h : a ^ 3 + 3 * b ^ 3 + 9 * c ^ 3 - 9 * a * b * c = 27 * m) :
    3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c := by
  have hp : Prime (3 : ℤ) := Int.prime_three
  -- 3 ∣ a
  have hda : (3 : ℤ) ∣ a := by
    have h3a3 : (3 : ℤ) ∣ a ^ 3 := by
      refine ⟨9 * m - b ^ 3 - 3 * c ^ 3 + 3 * a * b * c, by linarith [h]⟩
    exact hp.dvd_of_dvd_pow h3a3
  obtain ⟨a₁, rfl⟩ := hda
  -- after substituting a = 3a₁ and dividing by 3: 9a₁³ + b³ + 3c³ − 9a₁bc = 9m, so 3 ∣ b
  have hb : b ^ 3 = 3 * (3 * m - 3 * a₁ ^ 3 - c ^ 3 + 3 * a₁ * b * c) := by
    have h3 : (3 : ℤ) * b ^ 3 = 3 * (3 * (3 * m - 3 * a₁ ^ 3 - c ^ 3 + 3 * a₁ * b * c)) := by
      linear_combination h
    exact mul_left_cancel₀ (by norm_num) h3
  obtain ⟨b₁, rfl⟩ := hp.dvd_of_dvd_pow ⟨_, hb⟩
  -- after substituting b = 3b₁ and dividing by 3: 3a₁³ + 9b₁³ + c³ − 9a₁b₁c = 3m, so 3 ∣ c
  have hc : c ^ 3 = 3 * (m - a₁ ^ 3 - 3 * b₁ ^ 3 + 3 * a₁ * b₁ * c) := by
    have h3 : (9 : ℤ) * c ^ 3 = 9 * (3 * (m - a₁ ^ 3 - 3 * b₁ ^ 3 + 3 * a₁ * b₁ * c)) := by
      linear_combination h
    exact mul_left_cancel₀ (show (9 : ℤ) ≠ 0 by norm_num) h3
  exact ⟨⟨a₁, rfl⟩, ⟨b₁, rfl⟩, hp.dvd_of_dvd_pow ⟨_, hc⟩⟩

/-- The norm (over `ℚ`) of an element of `K` integral over `ℤ` is the image of an integer. -/
theorem exists_intCast_norm (z : K) (hz : IsIntegral ℤ z) :
    ∃ m : ℤ, Algebra.norm ℚ z = (m : ℚ) := by
  have hint : IsIntegral ℤ (Algebra.norm ℚ z) := Algebra.isIntegral_norm ℚ hz
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨m, by rw [← hm]; simp⟩

/-- The peeling lemma (heart of the index argument): if `z` is integral and `3·z ∈ ℤ[θ]`, then
already `z ∈ ℤ[θ]`. -/
theorem peel (z : K) (hz : IsIntegral ℤ z)
    (h3z : (3 : K) * z ∈ Algebra.adjoin ℤ ({cubeRootThree} : Set K)) :
    z ∈ Algebra.adjoin ℤ ({cubeRootThree} : Set K) := by
  obtain ⟨a, b, c, habc⟩ := (mem_adjoin_iff _).mp h3z
  -- N(3z) = 27 · N(z); N(z) = (m : ℚ)
  obtain ⟨m, hm⟩ := exists_intCast_norm z hz
  have hN3z : Algebra.norm ℚ ((3 : K) * z) = 27 * (m : ℚ) := by
    rw [show (3 : K) = algebraMap ℚ K 3 by simp, map_mul, Algebra.norm_algebraMap,
      degree_eq_three, hm]
    norm_num
  -- compute N(3z) via the norm form using the basis representation
  have hNabc : Algebra.norm ℚ ((3 : K) * z) =
      (a : ℚ) ^ 3 + 3 * b ^ 3 + 9 * c ^ 3 - 9 * a * b * c := by
    rw [habc, ← Int.cast_smul_eq_zsmul ℚ a, ← Int.cast_smul_eq_zsmul ℚ b,
      ← Int.cast_smul_eq_zsmul ℚ c, norm_eq_normForm]
  rw [hNabc] at hN3z
  -- transfer to the integer identity and apply the divisibility lemma
  have hint : a ^ 3 + 3 * b ^ 3 + 9 * c ^ 3 - 9 * a * b * c = 27 * m := by exact_mod_cast hN3z
  obtain ⟨⟨a₁, rfl⟩, ⟨b₁, rfl⟩, ⟨c₁, rfl⟩⟩ := three_dvd_of_normForm_eq a b c m hint
  -- now z = a₁•1 + b₁•θ + c₁•θ², an element of ℤ[θ]
  have hz_eq :
      z = (a₁ : ℤ) • (1 : K) + (b₁ : ℤ) • cubeRootThree + (c₁ : ℤ) • cubeRootThree ^ 2 := by
    have h3 : (3 : K) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h3
    rw [habc]
    simp only [mul_add, mul_smul, zsmul_eq_mul, mul_one]; push_cast; ring
  rw [hz_eq]
  exact (mem_adjoin_iff _).mpr ⟨a₁, b₁, c₁, rfl⟩

/-- The order `ℤ[θ] = Algebra.adjoin ℤ {θ}` is maximal: it equals the full ring of integers
`integralClosure ℤ K`. This is the core index argument at `p = 3` (`3 ≢ ±1 mod 9`), proved by
the discriminant bound `discr = -3⁵` and five rounds of the peeling lemma. -/
theorem integralClosure_eq_adjoin :
    integralClosure ℤ K = Algebra.adjoin ℤ ({cubeRootThree} : Set K) := by
  apply le_antisymm
  · -- ⊆ : every integral `z` lies in `ℤ[θ]`, via the discriminant bound and peeling
    intro z hz
    have hzI : IsIntegral ℤ z := hz
    have hf : cubePolynomial ≠ 0 := by intro h; simpa using congrArg natDegree h
    set pb := AdjoinRoot.powerBasis hf with hpb
    have hgen : pb.gen = cubeRootThree := AdjoinRoot.powerBasis_gen hf
    have hgenInt : IsIntegral ℤ pb.gen := by rw [hgen]; exact cubeRootThree_integral
    -- discr • z ∈ ℤ[θ]; with discr = -243 this is (-243 : ℚ) • z ∈ ℤ[θ]
    have hmem : Algebra.discr ℚ pb.basis • z ∈
        Algebra.adjoin ℤ ({pb.gen} : Set K) :=
      Algebra.discr_mul_isIntegral_mem_adjoin ℚ hgenInt hzI
    rw [discr_powerBasis_eq, hgen] at hmem
    -- `(-243 : ℚ) • z = -(243 * z)`, so `243 * z ∈ ℤ[θ]`
    have h243z : (243 : K) * z ∈ Algebra.adjoin ℤ ({cubeRootThree} : Set K) := by
      have hneg : (243 : K) * z = -((-243 : ℚ) • z) := by
        rw [Algebra.smul_def]; simp
      rw [hneg]; exact neg_mem hmem
    -- peel off five factors of 3: 243 = 3⁵
    have hint : ∀ w : K, IsIntegral ℤ w → IsIntegral ℤ ((3 : K) * w) := fun w hw => by
      have : (3 : K) = algebraMap ℤ K 3 := by simp
      rw [this]; exact (isIntegral_algebraMap).mul hw
    have e1 : (243 : K) * z = (3 : K) * ((3 : K) * ((3 : K) * ((3 : K) * ((3 : K) * z)))) := by
      ring
    rw [e1] at h243z
    have z5 : IsIntegral ℤ ((3 : K) * ((3 : K) * ((3 : K) * ((3 : K) * z)))) :=
      hint _ (hint _ (hint _ (hint _ hzI)))
    have z4 := peel _ z5 h243z
    have z3 := peel _ (hint _ (hint _ (hint _ hzI))) z4
    have z2 := peel _ (hint _ (hint _ hzI)) z3
    have z1 := peel _ (hint _ hzI) z2
    exact peel _ hzI z1
  · -- ⊇ : `ℤ[θ] ⊆ 𝓞 K` since `θ` is integral
    rw [Algebra.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact cubeRootThree_integral

/-- `1, θ, θ²` is an integral basis of `ℚ(∛3)`: their `ℤ`-span in `K` is exactly the ring of
integers `𝓞 K`. Together with their `ℚ`-linear independence this says they form a `ℤ`-basis
of `𝓞 K`. This is where `3 ≢ ±1 (mod 9)` enters: for a squarefree `m ≡ ±1 (mod 9)` the pure
cubic field `ℚ(∛m)` has integers outside `ℤ[∛m]`. -/
theorem span_integralBasisVectors_eq :
    Submodule.span ℤ (Set.range integralBasisVectors) =
      Subalgebra.toSubmodule (integralClosure ℤ K) := by
  rw [integralClosure_eq_adjoin, ← span_adjoin_eq]

/-- The integral generators `1, θ, θ²` as elements of `𝓞 K`. -/
noncomputable def integralBasisVectorsInt : Fin 3 → 𝓞 K := ![1, thetaInt, thetaInt ^ 2]

/-- The `ℤ`-linear embedding `𝓞 K ↪ K`. -/
noncomputable def ringOfIntegersLinearMap : 𝓞 K →ₗ[ℤ] K :=
  (Algebra.linearMap (𝓞 K) K).restrictScalars ℤ

theorem ringOfIntegersLinearMap_apply (u : 𝓞 K) :
    ringOfIntegersLinearMap u = (algebraMap (𝓞 K) K) u := rfl

theorem ringOfIntegersLinearMap_injective :
    Function.Injective ringOfIntegersLinearMap :=
  FaithfulSMul.algebraMap_injective (𝓞 K) K

/-- The embedding sends the integral generators in `𝓞 K` to the displayed vectors `1, θ, θ²`. -/
theorem algebraMap_integralBasisVectorsInt :
    (fun i => (algebraMap (𝓞 K) K) (integralBasisVectorsInt i)) = integralBasisVectors := by
  funext i
  have ht : (algebraMap (𝓞 K) K) thetaInt = cubeRootThree :=
    NumberField.RingOfIntegers.map_mk cubeRootThree cubeRootThree_integral
  fin_cases i <;> simp [integralBasisVectorsInt, integralBasisVectors, ht]

/-- `1, θ, θ²` are `ℤ`-linearly independent in `𝓞 K`. -/
theorem linearIndependent_integralBasisVectorsInt :
    LinearIndependent ℤ integralBasisVectorsInt := by
  -- the displayed family `1, θ, θ²` is `ℚ`-linearly independent in `K`, via the power basis
  have hf : cubePolynomial ≠ 0 := by intro h; simpa using congrArg natDegree h
  have hdim : (AdjoinRoot.powerBasis hf).dim = 3 := by
    rw [AdjoinRoot.powerBasis_dim hf]; exact natDegree_X_pow_sub_C
  set pb := AdjoinRoot.powerBasis hf with hpb
  set b : Basis (Fin 3) ℚ K := pb.basis.reindex (finCongr hdim) with hb
  have hbpow : ∀ i : Fin 3, b i = cubeRootThree ^ (i : ℕ) := by
    intro i
    rw [hb, Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen]; simp
  have hbeq : integralBasisVectors = ⇑b := by
    funext i
    fin_cases i <;> simp [integralBasisVectors, hbpow]
  have hQ : LinearIndependent ℚ integralBasisVectors := by
    rw [hbeq]; exact b.linearIndependent
  -- restrict scalars `ℚ → ℤ`, then pull back through the injective embedding `𝓞 K ↪ K`
  have hZ : LinearIndependent ℤ integralBasisVectors := hQ.restrict_scalars' ℤ
  rw [← algebraMap_integralBasisVectorsInt] at hZ
  exact hZ.of_comp ringOfIntegersLinearMap

/-- The `ℤ`-span of `1, θ, θ²` in `𝓞 K` is everything. -/
theorem span_integralBasisVectorsInt_eq_top :
    Submodule.span ℤ (Set.range integralBasisVectorsInt) = ⊤ := by
  apply Submodule.map_injective_of_injective ringOfIntegersLinearMap_injective
  rw [Submodule.map_span, ← Set.range_comp]
  have hcomp : ringOfIntegersLinearMap ∘ integralBasisVectorsInt = integralBasisVectors := by
    funext i; rw [Function.comp_apply, ringOfIntegersLinearMap_apply,
      ← algebraMap_integralBasisVectorsInt]
  rw [hcomp, span_integralBasisVectors_eq, Submodule.map_top]
  -- the image of `⊤` under the embedding is exactly `toSubmodule (integralClosure ℤ K)`
  ext x
  rw [Subalgebra.mem_toSubmodule]
  constructor
  · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨u, rfl⟩; exact u.2

/-- The integral basis `1, θ, θ²` packaged as a genuine `ℤ`-basis of the ring of integers `𝓞 K`. -/
noncomputable def concreteIntegralBasis : Basis (Fin 3) ℤ (𝓞 K) :=
  Basis.mk linearIndependent_integralBasisVectorsInt
    (span_integralBasisVectorsInt_eq_top).ge

/-- The packaged integral basis is, vector by vector, the displayed family `1, θ, θ²`. -/
theorem concreteIntegralBasis_apply (i : Fin 3) :
    (algebraMap (𝓞 K) K) (concreteIntegralBasis i) = integralBasisVectors i := by
  rw [concreteIntegralBasis, Basis.mk_apply]
  exact congrFun algebraMap_integralBasisVectorsInt i

/-- The displayed integral basis `1, θ, θ²` spans the same `ℤ`-lattice in `K` as mathlib's
`NumberField.integralBasis K`. This is the correct form of "the two integral bases agree":
they generate the same lattice (a unimodular change of basis), not a mere reindexing. -/
theorem span_integralBasisVectors_eq_integralBasis :
    Submodule.span ℤ (Set.range integralBasisVectors) =
      Submodule.span ℤ (Set.range (NumberField.integralBasis K)) := by
  rw [span_integralBasisVectors_eq]
  ext x
  constructor
  · intro hx
    exact (NumberField.mem_span_integralBasis K).mpr ⟨⟨x, hx⟩, rfl⟩
  · intro hx
    obtain ⟨y, rfl⟩ := RingHom.mem_range.mp ((NumberField.mem_span_integralBasis K).mp hx)
    exact y.2

/-- The concrete order `ℤ[θ]` inside `K`, where `θ = ∛3`. -/
abbrev concreteRingOfIntegers : Subalgebra ℤ K := Algebra.adjoin ℤ ({cubeRootThree} : Set K)

/-- The full ring of integers of `ℚ(∛3)` is `ℤ[θ]`: the order `ℤ[θ]` is maximal, i.e. the
field is monogenic. Subalgebra-level restatement of `span_integralBasisVectors_eq`. -/
theorem ringOfIntegers_eq : integralClosure ℤ K = concreteRingOfIntegers :=
  integralClosure_eq_adjoin

/-! ## 3. Discriminant -/

/-- The number-field discriminant of `ℚ(∛3)` is `-243 = -3⁵` (for `X³ - a` one has
`disc = -27a²`). In particular `3` is the only ramified prime, cf. `ramified_iff_eq_three`. -/
theorem numberField_discr_eq : NumberField.discr K = (-243 : ℤ) := by
  have hf : cubePolynomial ≠ 0 := by intro h; simpa using congrArg natDegree h
  have hdim : (AdjoinRoot.powerBasis hf).dim = 3 := by
    rw [AdjoinRoot.powerBasis_dim hf]; exact natDegree_X_pow_sub_C
  set qb : Basis (Fin 3) ℚ K := (AdjoinRoot.powerBasis hf).basis.reindex (finCongr hdim)
    with hqb
  have hbpow : ∀ i : Fin 3, qb i = cubeRootThree ^ (i : ℕ) := by
    intro i
    rw [hqb, Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen]
    exact rfl
  have hqfun : ⇑qb = integralBasisVectors := by
    funext i
    rw [hbpow i]
    fin_cases i <;> simp [integralBasisVectors]
  have hspan : Submodule.span ℤ (Set.range ⇑qb) =
      Submodule.span ℤ (Set.range ⇑(NumberField.integralBasis K)) := by
    rw [hqfun]; exact span_integralBasisVectors_eq_integralBasis
  have h1 : ∀ i j, IsIntegral ℤ (qb.toMatrix (NumberField.integralBasis K) i j) := by
    intro i j
    have hmem : (NumberField.integralBasis K) j ∈ Submodule.span ℤ (Set.range ⇑qb) := by
      rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩
    rw [Basis.mem_span_iff_repr_mem] at hmem
    obtain ⟨m, hm⟩ := hmem i
    rw [Basis.toMatrix_apply, ← hm]
    exact isIntegral_algebraMap
  have h2 : ∀ i j, IsIntegral ℤ ((NumberField.integralBasis K).toMatrix qb i j) := by
    intro i j
    have hmem : qb j ∈ Submodule.span ℤ (Set.range ⇑(NumberField.integralBasis K)) := by
      rw [← hspan]; exact Submodule.subset_span ⟨j, rfl⟩
    rw [Basis.mem_span_iff_repr_mem] at hmem
    obtain ⟨m, hm⟩ := hmem i
    rw [Basis.toMatrix_apply, ← hm]
    exact isIntegral_algebraMap
  have hQ : (NumberField.discr K : ℚ) = (-243 : ℚ) := by
    rw [NumberField.coe_discr,
      ← Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral K h1 h2,
      hqb, Basis.coe_reindex, Algebra.discr_reindex]
    exact discr_powerBasis_eq
  exact_mod_cast hQ

/-! ## 4. Norm form -/

/-- The integral norm form: on `𝓞 K = ℤ[θ]` the norm of `x + yθ + zθ²` (with `x, y, z ∈ ℤ`)
is `x³ + 3y³ + 9z³ - 9xyz`. -/
theorem intNorm_eq_normForm (x y z : ℤ) :
    Algebra.norm ℤ (x • (1 : 𝓞 K) + y • thetaInt + z • thetaInt ^ 2) =
      x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z := by
  have ht : ((thetaInt : 𝓞 K) : K) = cubeRootThree :=
    NumberField.RingOfIntegers.map_mk cubeRootThree cubeRootThree_integral
  -- prove the identity after the injective cast `ℤ ↪ ℚ`, reducing to `norm_eq_normForm`
  have key : (Algebra.norm ℤ (x • (1 : 𝓞 K) + y • thetaInt + z • thetaInt ^ 2) : ℚ)
      = ((x : ℚ) ^ 3 + 3 * (y : ℚ) ^ 3 + 9 * (z : ℚ) ^ 3 - 9 * x * y * z) := by
    rw [Algebra.coe_norm_int]
    push_cast [ht]
    rw [← Int.cast_smul_eq_zsmul ℚ x, ← Int.cast_smul_eq_zsmul ℚ y, ← Int.cast_smul_eq_zsmul ℚ z,
      norm_eq_normForm]
  exact_mod_cast key

/-- The "cubic Pell equation" for `ℚ(∛3)`: `x + yθ + zθ²` is a unit of `ℤ[θ]` iff
`x³ + 3y³ + 9z³ - 9xyz = ±1`. Combined with `unit_eq_torsion_mul_fundamentalUnit_zpow`, all
integer solutions of `x³ + 3y³ + 9z³ - 9xyz = ±1` arise from `±(θ² - 2)ⁿ`, `n ∈ ℤ`. -/
theorem isUnit_iff_normForm (x y z : ℤ) :
    IsUnit (x • (1 : 𝓞 K) + y • thetaInt + z • thetaInt ^ 2) ↔
      x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z = 1 ∨
        x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z = -1 := by
  rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm,
    ← Algebra.coe_norm_int, intNorm_eq_normForm]
  constructor
  · intro h
    have h' : |x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z| = 1 := by exact_mod_cast h
    exact (abs_eq (by norm_num)).mp h'
  · intro h
    have h' : |x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z| = 1 :=
      (abs_eq (by norm_num)).mpr h
    exact_mod_cast h'

/-! ## 5. Splitting of primes -/

/-- `3` is totally ramified: `(3) = (θ)³` as ideals of `𝓞 K`, directly from `θ³ = 3`.
Together with `isPrime_span_theta` this gives ramification index `e = 3`. -/
theorem span_three_eq : Ideal.span {(3 : 𝓞 K)} = Ideal.span {thetaInt} ^ 3 := by
  rw [Ideal.span_singleton_pow, thetaInt_cube]

/-- The prime `(θ)` above `3` has norm `3` (residue degree `f = 1`). -/
theorem absNorm_span_theta : Ideal.absNorm (Ideal.span {thetaInt}) = 3 := by
  have h := intNorm_eq_normForm 0 1 0
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `(θ)` is a prime ideal — the unique prime of `𝓞 K` above `3`. -/
theorem isPrime_span_theta : (Ideal.span {thetaInt}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_span_theta]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- Any prime of `𝓞 K` containing `3` equals `(θ)`: the prime above `3` is unique. -/
theorem eq_span_theta_of_three_mem (P : Ideal (𝓞 K)) (hP : P.IsPrime) (h3 : (3 : 𝓞 K) ∈ P) :
    P = Ideal.span {thetaInt} := by
  have hθ : thetaInt ∈ P := hP.mem_of_pow_mem 3 (by rw [thetaInt_cube]; exact h3)
  have hle : Ideal.span {thetaInt} ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hθ
  have hbot : Ideal.span {thetaInt} ≠ ⊥ := by
    intro h
    have h3' := absNorm_span_theta
    rw [h, Ideal.absNorm_bot] at h3'
    norm_num at h3'
  exact ((isPrime_span_theta.isMaximal hbot).eq_of_le hP.ne_top hle).symm

/-- The elementary identity `2 = (θ - 1)(θ² + θ + 1)` in `ℤ[θ]`, from `θ³ = 3`. -/
theorem two_eq_mul : (2 : 𝓞 K) = (thetaInt - 1) * (thetaInt ^ 2 + thetaInt + 1) := by
  linear_combination -thetaInt_cube

/-- `2` splits as a product of two primes of residue degrees `1` and `2`, matching the
factorisation `X³ - 3 ≡ (X + 1)(X² + X + 1) (mod 2)`. -/
theorem span_two_eq :
    Ideal.span {(2 : 𝓞 K)} =
      Ideal.span {thetaInt - 1} * Ideal.span {thetaInt ^ 2 + thetaInt + 1} := by
  rw [Ideal.span_singleton_mul_span_singleton, ← two_eq_mul]

/-- The prime `(θ - 1)` above `2` has norm `2` (residue degree `f = 1`). -/
theorem absNorm_span_theta_sub_one : Ideal.absNorm (Ideal.span {thetaInt - 1}) = 2 := by
  have h := intNorm_eq_normForm (-1) 1 0
  have he : (-1 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • thetaInt + (0 : ℤ) • thetaInt ^ 2 =
      thetaInt - 1 := by ring
  rw [he] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- `(θ - 1)` is a prime ideal — the degree-`1` prime of `𝓞 K` above `2`. -/
theorem isPrime_span_theta_sub_one : (Ideal.span {thetaInt - 1}).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_span_theta_sub_one]
  exact (Nat.irreducible_iff_nat_prime _).mpr (by norm_num)

/-- `(θ² + θ + 1)` is a prime ideal — the degree-`2` prime of `𝓞 K` above `2`. -/
theorem isPrime_span_theta_sq_add_theta_add_one :
    (Ideal.span {thetaInt ^ 2 + thetaInt + 1}).IsPrime := by
  sorry

/-- The prime `(θ² + θ + 1)` above `2` has norm `4` (residue degree `f = 2`). -/
theorem absNorm_span_theta_sq_add_theta_add_one :
    Ideal.absNorm (Ideal.span {thetaInt ^ 2 + thetaInt + 1}) = 4 := by
  have h := intNorm_eq_normForm 1 1 1
  have he : (1 : ℤ) • (1 : 𝓞 K) + (1 : ℤ) • thetaInt + (1 : ℤ) • thetaInt ^ 2 =
      thetaInt ^ 2 + thetaInt + 1 := by ring
  rw [he] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- No prime of norm `2` contains `θ² + θ + 1`: in the residue field with two elements,
`t² + t + 1` has no root. This is the formal content of "`X² + X + 1` is irreducible mod `2`". -/
theorem absNorm_ne_two_of_quadFactor_mem (P : Ideal (𝓞 K)) (hP : P.IsMaximal)
    (hmem : thetaInt ^ 2 + thetaInt + 1 ∈ P) : Ideal.absNorm P ≠ 2 := by
  intro hcard
  haveI : P.IsMaximal := hP
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hcard
  haveI : Finite ((𝓞 K) ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h01 : ∀ x : (𝓞 K) ⧸ P, x = 0 ∨ x = 1 := by
    intro x
    by_contra hx
    push Not at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hinj : Function.Injective (![0, 1, x] : Fin 3 → (𝓞 K) ⧸ P) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hle := Nat.card_le_card_of_injective _ hinj
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, hcard] at hle
    omega
  have h2zero : (1 : (𝓞 K) ⧸ P) + 1 = 0 := by
    rcases h01 (1 + 1) with h | h
    · exact h
    · have h10 : (1 : (𝓞 K) ⧸ P) = 0 := by
        have := add_right_cancel (b := (1 : (𝓞 K) ⧸ P)) (a := (1 : (𝓞 K) ⧸ P)) (c := 0)
        rw [zero_add] at this
        exact this h
      exact absurd h10 one_ne_zero
  set t := Ideal.Quotient.mk P thetaInt with ht
  have htroot : t ^ 2 + t + 1 = 0 := by
    rw [ht, ← map_pow, ← map_add, ← map_one (Ideal.Quotient.mk P), ← map_add]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rcases h01 t with h | h
  · rw [h] at htroot
    simp at htroot
  · rw [h, one_pow] at htroot
    rw [h2zero, zero_add] at htroot
    exact one_ne_zero htroot

/-- `7` is inert in `ℚ(∛3)`: `X³ - 3` is irreducible mod `7`, since the nonzero cubes mod `7`
are `{1, 6}` and `3` is not among them. -/
theorem isPrime_span_seven : (Ideal.span {(7 : 𝓞 K)}).IsPrime := by
  sorry

/-- The prime `(7)` is inert with norm `7³` (residue degree `f = 3`). -/
theorem absNorm_span_seven : Ideal.absNorm (Ideal.span {(7 : 𝓞 K)}) = 343 := by
  have h := intNorm_eq_normForm 7 0 0
  have he : (7 : ℤ) • (1 : 𝓞 K) + (0 : ℤ) • thetaInt + (0 : ℤ) • thetaInt ^ 2 =
      (7 : 𝓞 K) := by ring
  rw [he] at h
  norm_num at h
  rw [Ideal.absNorm_span_singleton, h]
  rfl

/-- The prime `(61, θ - r)` of `𝓞 K` above `61`, for `r` a cube root of `3` mod `61`. The
roots of `X³ - 3` mod `61` are `4`, `5` and `52`. -/
def primeAbove61 (r : ℤ) : Ideal (𝓞 K) := Ideal.span {(61 : 𝓞 K), thetaInt - (r : 𝓞 K)}

/-- `61` splits completely: `61 ≡ 1 (mod 3)` and `3 ≡ 4³ (mod 61)` is a cubic residue, so
`X³ - 3 ≡ (X - 4)(X - 5)(X - 52) (mod 61)` and `(61)` is a product of three primes of norm
`61`. This is the generic split case of the cubic splitting law. -/
theorem span_sixtyOne_eq :
    Ideal.span {(61 : 𝓞 K)} = primeAbove61 4 * primeAbove61 5 * primeAbove61 52 := by
  sorry

/-- Each ideal `(61, θ - r)` for `r ∈ {4, 5, 52}` is prime. -/
theorem isPrime_primeAbove61 (r : ℤ) (hr : r = 4 ∨ r = 5 ∨ r = 52) :
    (primeAbove61 r).IsPrime := by
  sorry

/-- The three primes above `61` are pairwise distinct, so `61` is unramified and splits
completely. -/
theorem primeAbove61_pairwise_ne :
    primeAbove61 4 ≠ primeAbove61 5 ∧ primeAbove61 4 ≠ primeAbove61 52 ∧
      primeAbove61 5 ≠ primeAbove61 52 := by
  sorry

/-- The splitting law at ramified primes: a rational prime `p` ramifies in `ℚ(∛3)` (some prime
of `𝓞 K` divides `(p)` at least twice) iff `p = 3`, i.e. iff `p` divides the discriminant
`-3⁵`. -/
theorem ramified_iff_eq_three (p : ℕ) (hp : p.Prime) :
    (∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2) ↔ p = 3 := by
  sorry

/-! ## 6. Ring of units -/

/-- A torsion generator of `𝓞 Kˣ`, mathematically `-1`. -/
abbrev torsionGenerator : (𝓞 K)ˣ := -1

/-- The concrete torsion units `{1, -1}`. -/
def torsionUnits : Set ((𝓞 K)ˣ) := {u | ∃ k : Fin 2, u = torsionGenerator ^ k.val}

/-- The torsion subgroup of `𝓞 Kˣ` is exactly `{1, -1}`: a field of odd degree over `ℚ` has a
real embedding, so its only roots of unity are `±1`. -/
theorem torsionUnits_eq : {u : (𝓞 K)ˣ | IsOfFinOrder u} = torsionUnits := by
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

/-- `ℚ(∛3)` is not totally real: `θ = ∛3` has a non-real conjugate (`∛3 · ζ₃`), giving a
non-real complex embedding. -/
theorem not_totallyReal : ¬ NumberField.IsTotallyReal K := by
  intro h
  obtain ⟨c, hc3, hcim⟩ : ∃ c : ℂ, c ^ 3 = 3 ∧ c.im ≠ 0 := by
    obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 3 :=
      ⟨_, Complex.isPrimitiveRoot_exp 3 (by norm_num)⟩
    have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
    have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
    have hquad : ζ ^ 2 + ζ + 1 = 0 := by
      have hfac : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
      rcases mul_eq_zero.mp hfac with hh | hh
      · exact absurd (sub_eq_zero.mp hh) hζ1
      · exact hh
    have hζim : ζ.im ≠ 0 := by
      intro him
      have hre : (ζ ^ 2 + ζ + 1).re = 0 := by rw [hquad]; simp
      rw [sq] at hre
      simp only [Complex.add_re, Complex.mul_re, Complex.one_re, him, mul_zero, sub_zero] at hre
      nlinarith [hre, sq_nonneg ζ.re]
    obtain ⟨c0, hc0⟩ := IsAlgClosed.exists_pow_nat_eq (3 : ℂ) (n := 3) (by norm_num)
    have hc0ne : c0 ≠ 0 := by intro hh; rw [hh] at hc0; norm_num at hc0
    by_cases hc0im : c0.im = 0
    · refine ⟨c0 * ζ, by rw [mul_pow, hc0, hζ3]; ring, ?_⟩
      rw [Complex.mul_im, hc0im, zero_mul, add_zero]
      exact mul_ne_zero (fun hh => hc0ne (Complex.ext hh hc0im)) hζim
    · exact ⟨c0, hc0, hc0im⟩
  have hroot : eval₂ (algebraMap ℚ ℂ) c cubePolynomial = 0 := by
    simp only [cubePolynomial, eval₂_sub, eval₂_pow, eval₂_X, map_ofNat]
    rw [hc3]; norm_num
  let φ : K →+* ℂ := AdjoinRoot.lift (algebraMap ℚ ℂ) c hroot
  have hφ : φ cubeRootThree = c := AdjoinRoot.lift_root hroot
  have hreal : NumberField.ComplexEmbedding.IsReal φ := h.complexEmbedding_isReal φ
  rw [NumberField.ComplexEmbedding.isReal_iff] at hreal
  have hpt := RingHom.congr_fun hreal cubeRootThree
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, hφ] at hpt
  exact hcim (Complex.conj_eq_iff_im.mp hpt)

/-- `ℚ(∛3)` has exactly one complex place: the signature is `(r₁, r₂) = (1, 1)`. -/
theorem nrComplexPlaces_eq_one : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  have hsig : NumberField.InfinitePlace.nrRealPlaces K +
      2 * NumberField.InfinitePlace.nrComplexPlaces K = 3 := by
    rw [← degree_eq_three]; exact NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 := by
    rw [Ne, NumberField.nrComplexPlaces_eq_zero_iff]; exact not_totallyReal
  omega

/-- The Dirichlet unit rank of `ℚ(∛3)` is `1`: the signature is `(r₁, r₂) = (1, 1)`, so the
rank is `r₁ + r₂ - 1 = 1`. -/
theorem unitRank_eq_one : NumberField.Units.rank K = 1 := by
  have hsig : NumberField.InfinitePlace.nrRealPlaces K +
      2 * NumberField.InfinitePlace.nrComplexPlaces K = 3 := by
    rw [← degree_eq_three]; exact NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 := by
    rw [Ne, NumberField.nrComplexPlaces_eq_zero_iff]; exact not_totallyReal
  have hcard : Fintype.card (NumberField.InfinitePlace K) = 2 := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega
  rw [NumberField.Units.rank, hcard]

/-- A fundamental unit of `𝓞 K`, mathematically `θ² - 2` (of norm `1`), with explicit inverse
`2θ² + 3θ + 4`. -/
noncomputable def fundamentalUnit : (𝓞 K)ˣ where
  val := thetaInt ^ 2 - 2
  inv := 2 * thetaInt ^ 2 + 3 * thetaInt + 4
  val_inv := by have h := thetaInt_cube; linear_combination (2 * thetaInt + 3) * h
  inv_val := by have h := thetaInt_cube; linear_combination (2 * thetaInt + 3) * h

/-- The system of fundamental units for the rank-`1` unit group: the single unit `θ² - 2`. -/
noncomputable def fundamentalUnitSystem : Fin (NumberField.Units.rank K) → (𝓞 K)ˣ :=
  fun _ => fundamentalUnit

/-- The displayed family is a system of fundamental units: together with roots of unity, it
generates all units of `𝓞 K`. In rank `1` this says exactly that `θ² - 2` is a fundamental
unit (not a proper power times torsion). -/
theorem fundamentalUnitSystem_isFundamental :
    Subgroup.closure (Set.range fundamentalUnitSystem) ⊔ NumberField.Units.torsion K = ⊤ := by
  sorry

/-- Equivalently, every unit is a root of unity times a power of `θ² - 2`. -/
theorem unit_eq_torsion_mul_fundamentalUnit_zpow (u : (𝓞 K)ˣ) :
    ∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ∃ n : ℤ, u = ζ * fundamentalUnit ^ n := by
  have hu : u ∈ Subgroup.closure (Set.range fundamentalUnitSystem) ⊔
      NumberField.Units.torsion K := by
    rw [fundamentalUnitSystem_isFundamental]; trivial
  rw [Subgroup.mem_sup] at hu
  obtain ⟨x, hx, y, hy, hxy⟩ := hu
  have hrange : Set.range fundamentalUnitSystem = {fundamentalUnit} := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩; rfl
    · rintro rfl
      exact ⟨⟨0, by rw [unitRank_eq_one]; exact Nat.zero_lt_one⟩, rfl⟩
  rw [hrange, Subgroup.mem_closure_singleton] at hx
  obtain ⟨n, hn⟩ := hx
  exact ⟨y, hy, n, by rw [hn, ← hxy]; exact mul_comm x y⟩

/-- The unit group is `μ₂ × ℤ` as an abstract abelian group. -/
theorem unitGroupStructure :
    Nonempty ((𝓞 K)ˣ ≃* (Multiplicative (ZMod 2) × Multiplicative (Fin 1 → ℤ))) := by
  sorry

/-- The regulator of `ℚ(∛3)` is `|log(∛9 - 2)| = log(2∛9 + 3∛3 + 4) ≈ 2.5246`, the covolume
of the unit lattice. This is the analytic restatement that `θ² - 2` is a fundamental unit:
the regulator equals the absolute logarithm of its image under the real embedding. -/
theorem regulator_eq :
    NumberField.Units.regulator K = |Real.log ((3 : ℝ) ^ ((2 : ℝ) / 3) - 2)| := by
  sorry

/-! ## 7. Class group -/

/-- The class number of `ℚ(∛3)` is `1`. The Minkowski bound is
`(4/π) · (3!/3³) · √243 ≈ 4.41`, and the primes `2` and `3` below it are products of principal
primes (`N(θ - 1) = 2`, `(3) = (θ)³`), cf. section 5. -/
theorem classNumber_eq_one : NumberField.classNumber K = 1 := by
  sorry

/-- The ring of integers `ℤ[θ]` is a principal ideal domain — the ring-theoretic content of
class number one. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 K) := by
  rw [← NumberField.classNumber_eq_one_iff]
  exact classNumber_eq_one

/-- The class group of `𝓞 K` is trivial. -/
theorem classGroupStructure : Nonempty (ClassGroup (𝓞 K) ≃* Multiplicative (ZMod 1)) := by
  have h1 : Nat.card (ClassGroup (𝓞 K)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 K)) := (Nat.card_eq_one_iff_unique.mp h1).1
  haveI : Unique (ClassGroup (𝓞 K)) := uniqueOfSubsingleton 1
  exact ⟨MulEquiv.ofUnique⟩

/-- The unit ideal as the concrete representative of the unique ideal class. -/
abbrev unitIdealRepresentative : (Ideal (𝓞 K))⁰ := ⟨(⊤ : Ideal (𝓞 K)), by simp⟩

/-- Every ideal class is represented by the unit ideal. -/
theorem classGroupRepresentative (C : ClassGroup (𝓞 K)) :
    C = ClassGroup.mk0 unitIdealRepresentative := by
  have h1 : Nat.card (ClassGroup (𝓞 K)) = 1 := by
    simpa [NumberField.classNumber] using classNumber_eq_one
  haveI : Subsingleton (ClassGroup (𝓞 K)) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim _ _

/-! ## 8. Euclidean structure -/

/-- `ℚ(∛3)` is norm-Euclidean: division with remainder in `ℤ[θ]` with respect to the absolute
value of the field norm. This is a classical result for the pure cubic field of smallest
discriminant, and strengthens `isPrincipalIdealRing`. -/
theorem normEuclidean (a b : 𝓞 K) (hb : b ≠ 0) :
    ∃ q r : 𝓞 K, a = b * q + r ∧
      (Algebra.norm ℤ r).natAbs < (Algebra.norm ℤ b).natAbs := by
  sorry

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

/-- The Galois closure `ℚ(∛3, ζ₃)` has degree `6 = [ℚ(∛3) : ℚ] · [ℚ(ζ₃) : ℚ]` over `ℚ`. -/
theorem finrank_galoisClosure : Module.finrank ℚ galoisClosure = 6 := by
  sorry

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
permuting the three cube roots of `3`. -/
theorem galoisClosureGroupStructure :
    Nonempty ((galoisClosure ≃ₐ[ℚ] galoisClosure) ≃* Equiv.Perm (Fin 3)) := by
  sorry

end XYin.NumberField.New.CubeRootThree
