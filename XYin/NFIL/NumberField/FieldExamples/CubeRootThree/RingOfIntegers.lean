/-
Copyright (c) 2026 SmwYin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SmwYin
-/
import XYin.NFIL.NumberField.FieldExamples.CubeRootThree.Embeddings

/-!
# `ℚ(∛3)` RingOfIntegers

Integral basis, ring-of-integers description, and integral-coordinate norm forms.

This file is part of the reorganized `FieldExamples` case-study layout. The core files are
intended to import almost linearly:
`Basic → Galois → Embeddings → RingOfIntegers → Discriminant → PrimeSplitting →
ClassGroup → Units → Euclidean → LocalGlobal`, with a few field-specific special-topic files
kept separate.
-/

/-!
## Ring Of Integers
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

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
  set b : Basis (Fin 3) ℚ K := pb.basis.reindex (finCongr hdim) with hb
  have hbpow : ∀ i : Fin 3, b i = cubeRootThree ^ (i : ℕ) := by
    intro i
    rw [hb, Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen]; simp
  have hb0 : b 0 = 1 := by rw [hbpow]; simp
  have hb1 : b 1 = cubeRootThree := by rw [hbpow]; simp
  have hb2 : b 2 = cubeRootThree ^ 2 := by rw [hbpow]; simp
  have hm0 : cubeRootThree * b 0 = b 1 := by rw [hb0, hb1, mul_one]
  have hm1 : cubeRootThree * b 1 = b 2 := by rw [hb1, hb2, sq]
  have hm2 : cubeRootThree * b 2 = (3 : ℚ) • b 0 := by
    rw [hb0, hb2, Algebra.smul_def, mul_one, ← pow_succ', cubeRootThree_cube]; norm_num
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
  have hda : (3 : ℤ) ∣ a := by
    have h3a3 : (3 : ℤ) ∣ a ^ 3 := by
      refine ⟨9 * m - b ^ 3 - 3 * c ^ 3 + 3 * a * b * c, by linarith [h]⟩
    exact hp.dvd_of_dvd_pow h3a3
  obtain ⟨a₁, rfl⟩ := hda
  have hb : b ^ 3 = 3 * (3 * m - 3 * a₁ ^ 3 - c ^ 3 + 3 * a₁ * b * c) := by
    have h3 : (3 : ℤ) * b ^ 3 = 3 * (3 * (3 * m - 3 * a₁ ^ 3 - c ^ 3 + 3 * a₁ * b * c)) := by
      linear_combination h
    exact mul_left_cancel₀ (by norm_num) h3
  obtain ⟨b₁, rfl⟩ := hp.dvd_of_dvd_pow ⟨_, hb⟩
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
  obtain ⟨m, hm⟩ := exists_intCast_norm z hz
  have hN3z : Algebra.norm ℚ ((3 : K) * z) = 27 * (m : ℚ) := by
    rw [show (3 : K) = algebraMap ℚ K 3 by simp, map_mul, Algebra.norm_algebraMap,
      degree_eq_three, hm]
    norm_num
  have hNabc : Algebra.norm ℚ ((3 : K) * z) =
      (a : ℚ) ^ 3 + 3 * b ^ 3 + 9 * c ^ 3 - 9 * a * b * c := by
    rw [habc, ← Int.cast_smul_eq_zsmul ℚ a, ← Int.cast_smul_eq_zsmul ℚ b,
      ← Int.cast_smul_eq_zsmul ℚ c, norm_eq_normForm]
  rw [hNabc] at hN3z
  have hint : a ^ 3 + 3 * b ^ 3 + 9 * c ^ 3 - 9 * a * b * c = 27 * m := by exact_mod_cast hN3z
  obtain ⟨⟨a₁, rfl⟩, ⟨b₁, rfl⟩, ⟨c₁, rfl⟩⟩ := three_dvd_of_normForm_eq a b c m hint
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
    have hmem : Algebra.discr ℚ pb.basis • z ∈
        Algebra.adjoin ℤ ({pb.gen} : Set K) :=
      Algebra.discr_mul_isIntegral_mem_adjoin ℚ hgenInt hzI
    rw [discr_powerBasis_eq, hgen] at hmem
    have h243z : (243 : K) * z ∈ Algebra.adjoin ℤ ({cubeRootThree} : Set K) := by
      have hneg : (243 : K) * z = -((-243 : ℚ) • z) := by
        rw [Algebra.smul_def]; simp
      rw [hneg]; exact neg_mem hmem
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
  have hZ : LinearIndependent ℤ integralBasisVectors := hQ.restrict_scalars' ℤ
  rw [← algebraMap_integralBasisVectorsInt] at hZ
  exact hZ.of_comp ringOfIntegersLinearMap

/-- The `ℤ`-span of `1, θ, θ²` in `𝓞 K` is everything. -/
theorem span_integralBasisVectorsInt_eq_top :
    Submodule.span ℤ (Set.range integralBasisVectorsInt) = ⊤ := by
  apply Submodule.map_injective_of_injective ringOfIntegersLinearMap_injective
  rw [Submodule.map_span, ← Set.range_comp]
  have hcomp : ringOfIntegersLinearMap ∘ integralBasisVectorsInt = integralBasisVectors := by
    funext i
    rw [Function.comp_apply, ← algebraMap_integralBasisVectorsInt]
    rfl
  rw [hcomp, span_integralBasisVectors_eq, Submodule.map_top]
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

end NumberField.CubeRootThree

/-!
## Norm Form
-/

noncomputable section

open Module Polynomial
open scoped NumberField nonZeroDivisors

namespace NumberField.CubeRootThree

/-- The integral norm form: on `𝓞 K = ℤ[θ]` the norm of `x + yθ + zθ²` (with `x, y, z ∈ ℤ`)
is `x³ + 3y³ + 9z³ - 9xyz`. -/
theorem intNorm_eq_normForm (x y z : ℤ) :
    Algebra.norm ℤ (x • (1 : 𝓞 K) + y • thetaInt + z • thetaInt ^ 2) =
      x ^ 3 + 3 * y ^ 3 + 9 * z ^ 3 - 9 * x * y * z := by
  have ht : ((thetaInt : 𝓞 K) : K) = cubeRootThree :=
    NumberField.RingOfIntegers.map_mk cubeRootThree cubeRootThree_integral
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

end NumberField.CubeRootThree
