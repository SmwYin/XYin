/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldDefs
import Mathlib.RingTheory.DedekindDomain.Factorization

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
variable (K : Type*) [Field K] [NumberField K]

/-- A larger ideal modulus gives a smaller prime-to-modulus ideal group. -/
theorem coprimeIdeals_mono {m n : Ideal (𝓞 K)} (hmn : m ≤ n) :
    coprimeIdeals K m ≤ coprimeIdeals K n := by
  apply Subgroup.closure_mono
  rintro u ⟨A, hA, hAm, hu⟩
  exact ⟨A, hA, eq_top_iff.mpr ((eq_top_iff.mp hAm).trans (sup_le_sup_left hmn A)), hu⟩

/-- Integral ray generators are prime to their modulus. -/
theorem rayGenerators_mem_coprimeIdeals (m : Ideal (𝓞 K)) :
    rayGenerators K m ⊆ coprimeIdeals K m := by
  rintro u ⟨α, hα, hα1, hu⟩
  apply Subgroup.subset_closure
  refine ⟨Ideal.span {α}, by rwa [Ne, Ideal.span_singleton_eq_bot], ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    have h1 : α ∈ Ideal.span {α} ⊔ m := Ideal.mem_sup_left (Ideal.mem_span_singleton_self α)
    have h2 : α - 1 ∈ Ideal.span {α} ⊔ m := Ideal.mem_sup_right hα1
    simpa using Ideal.sub_mem _ h1 h2
  · rw [hu, FractionalIdeal.coeIdeal_span_singleton]

/-- Every nonzero ideal prime to the modulus has its fractional-ideal unit representative. -/
theorem exists_coprimeIdealUnit (m : Ideal (𝓞 K)) (A : Ideal (𝓞 K)) (hA : A ≠ ⊥) (hAm : A ⊔ m = ⊤) :
    ∃ u : coprimeIdeals K m,
      ((u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = A := by
  have hne : (A : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hA
  exact ⟨⟨Units.mk0 _ hne, Subgroup.subset_closure ⟨A, hA, hAm, rfl⟩⟩, rfl⟩

/-- The unit associated to a nonzero prime ideal. -/
def primeIdealUnit (v : HeightOneSpectrum (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K ⟨v.asIdeal, by
    simpa only [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot] using v.ne_bot⟩

/-- Its underlying fractional ideal is the chosen prime. -/
theorem primeIdealUnit_coe (v : HeightOneSpectrum (𝓞 K)) :
    (primeIdealUnit K v : FractionalIdeal (𝓞 K)⁰ K) = v.asIdeal := by
  rfl

/-- The finite prime-exponent vector of a nonzero fractional ideal. -/
def idealExponentVector (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => FractionalIdeal.count K v I)
    (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (I : FractionalIdeal (𝓞 K)⁰ K)))

/-- Exponent coordinates agree with the library's prime count. -/
theorem idealExponentVector_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    idealExponentVector K I v = FractionalIdeal.count K v I := by
  rfl

/-- Finite products of prime-ideal powers. -/
def exponentIdealProduct (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ := e.prod (fun v n => primeIdealUnit K v ^ n)

/-- The underlying fractional ideal of a finite product of prime-ideal powers. -/
theorem coe_exponentIdealProduct (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    (exponentIdealProduct K e : FractionalIdeal (𝓞 K)⁰ K) =
      e.prod (fun v n => (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n) := by
  classical
  unfold exponentIdealProduct
  rw [Finsupp.prod, Units.coe_prod, Finsupp.prod]
  simp only [Units.val_zpow_eq_zpow_val, primeIdealUnit_coe]

/-- Prime factorization reads the exponent of this finite product. -/
theorem count_exponentIdealProduct (e : HeightOneSpectrum (𝓞 K) →₀ ℤ)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (exponentIdealProduct K e) = e v := by
  classical
  rw [coe_exponentIdealProduct]
  exact FractionalIdeal.count_finsuppProd K v e

/-- Every ideal is reconstructed from its prime-exponent vector. -/
theorem exponentIdealProduct_idealExponentVector (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    exponentIdealProduct K (idealExponentVector K I) = I := by
  apply Units.ext
  rw [coe_exponentIdealProduct, Finsupp.prod]
  conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero]
  rw [finprod_eq_finsetProd_of_mulSupport_subset (s := (idealExponentVector K I).support)]
  · rfl
  · intro v hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, idealExponentVector_apply]
    intro h0
    apply hv
    simp [h0]

/-- Multiplication of ideal units adds prime-exponent vectors. -/
theorem idealExponentVector_mul (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    idealExponentVector K (I * J) = idealExponentVector K I + idealExponentVector K J := by
  ext v
  simp only [Finsupp.add_apply, idealExponentVector_apply, Units.val_mul]
  exact FractionalIdeal.count_mul K v I.ne_zero J.ne_zero

/-- Adding exponent vectors multiplies the associated ideals. -/
theorem exponentIdealProduct_add (a b : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    exponentIdealProduct K (a + b) = exponentIdealProduct K a * exponentIdealProduct K b := by
  classical
  unfold exponentIdealProduct
  exact Finsupp.prod_add_index (fun _ _ => zpow_zero _) (fun _ _ _ _ => zpow_add _ _ _)

/-- The subgroup supported at the prime factors of a modulus. -/
def modulusSupportedIdeals (m : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.closure {u | ∃ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal ∧
    (u : FractionalIdeal (𝓞 K)⁰ K) = v.asIdeal}

/-- For a nonzero integral ideal, a vanishing prime count means the prime does not divide it. -/
theorem integral_count_eq_zero_iff_not_le (A : Ideal (𝓞 K)) (hA : A ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (A : FractionalIdeal (𝓞 K)⁰ K) = 0 ↔ ¬A ≤ v.asIdeal := by
  rw [FractionalIdeal.count_coe K v hA, Nat.cast_eq_zero, ← Ideal.dvd_iff_le,
    ← Associates.count_ne_zero_iff_dvd hA v.irreducible, not_not]

/-- An integral ideal is prime to m exactly when its exponents at divisors of m vanish. -/
theorem integral_coprime_iff_count (m A : Ideal (𝓞 K)) (hA : A ≠ ⊥) :
    A ⊔ m = ⊤ ↔ ∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal →
      FractionalIdeal.count K v (A : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  constructor
  · intro h v hmv
    rw [integral_count_eq_zero_iff_not_le K A hA v]
    intro hAv
    exact v.isPrime.ne_top (eq_top_iff.mpr (h ▸ sup_le hAv hmv))
  · intro h
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hM0 : M ≠ ⊥ := fun h0 => hA (eq_bot_iff.mpr (h0 ▸ le_sup_left.trans hle))
    let v : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hM0⟩
    exact (integral_count_eq_zero_iff_not_le K A hA v).mp (h v (le_sup_right.trans hle))
      (le_sup_left.trans hle)

/-- The subgroup generated by an arbitrary specified collection of prime ideals. -/
def primeGeneratedGroup (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ := Subgroup.closure (primeIdealUnit K '' S)

/-- Prime powers from S have zero count at each prime outside S. -/
theorem count_zero_of_mem_primeGeneratedGroup (S : Set (HeightOneSpectrum (𝓞 K)))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hI : I ∈ primeGeneratedGroup K S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    FractionalIdeal.count K v I = 0 := by
  induction hI using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [primeIdealUnit_coe]
    exact FractionalIdeal.count_maximal_coprime K v (fun h => hv (h ▸ hw))
  | one => simp [FractionalIdeal.count_one]
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, FractionalIdeal.count_mul K v x.ne_zero y.ne_zero, hx, hy, add_zero]
  | inv x _ hx => rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hx, neg_zero]

/-- Vanishing exponents outside S reconstruct an ideal from primes in S. -/
theorem mem_primeGeneratedGroup_of_count_zero (S : Set (HeightOneSpectrum (𝓞 K)))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hI : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → FractionalIdeal.count K v I = 0) :
    I ∈ primeGeneratedGroup K S := by
  rw [← exponentIdealProduct_idealExponentVector K I]
  unfold exponentIdealProduct
  rw [Finsupp.prod]
  refine Subgroup.prod_mem _ fun v hv =>
    Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_image_of_mem (primeIdealUnit K) ?_)) _
  by_contra hvS
  rw [Finsupp.mem_support_iff, idealExponentVector_apply] at hv
  exact hv (hI v hvS)

/-- Good prime ideals generate the prime-to-modulus fractional ideal group. -/
theorem coprimeIdeals_eq_closure_primes (m : Ideal (𝓞 K)) :
    coprimeIdeals K m = Subgroup.closure
      {u : (FractionalIdeal (𝓞 K)⁰ K)ˣ |
        ∃ q : Ideal (𝓞 K), q.IsPrime ∧ q ≠ ⊥ ∧ q ⊔ m = ⊤ ∧
        (u : FractionalIdeal (𝓞 K)⁰ K) = q} := by
  apply le_antisymm
  · rw [coprimeIdeals, Subgroup.closure_le]
    rintro u ⟨A, hA, hAm, hu⟩
    have hmem : u ∈ primeGeneratedGroup K {v | ¬m ≤ v.asIdeal} := by
      apply mem_primeGeneratedGroup_of_count_zero
      intro v hv
      simp only [Set.mem_setOf_eq, not_not] at hv
      rw [hu]
      exact (integral_coprime_iff_count K m A hA).mp hAm v hv
    refine (Subgroup.closure_mono ?_) hmem
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨v.asIdeal, v.isPrime, v.ne_bot, ?_, primeIdealUnit_coe K v⟩
    by_contra hne
    exact hv (le_sup_right.trans (v.isMaximal.eq_of_le hne le_sup_left).ge)
  · rw [Subgroup.closure_le]
    rintro u ⟨q, -, hq0, hqm, hu⟩
    exact Subgroup.subset_closure ⟨q, hq0, hqm, hu⟩

/-- The prime-to-m group is generated by precisely the primes not dividing m. -/
theorem coprimeIdeals_eq_primeGeneratedGroup (m : Ideal (𝓞 K)) :
    coprimeIdeals K m = primeGeneratedGroup K {v | ¬m ≤ v.asIdeal} := by
  rw [coprimeIdeals_eq_closure_primes, primeGeneratedGroup]
  congr 1
  ext u
  constructor
  · rintro ⟨q, hq, hq0, hqm, hu⟩
    refine ⟨⟨q, hq, hq0⟩, fun hmq => hq.ne_top ?_, Units.ext (by rw [primeIdealUnit_coe, hu])⟩
    rw [← hqm]
    exact le_antisymm le_sup_left (sup_le le_rfl hmq)
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.asIdeal, v.isPrime, v.ne_bot, ?_, primeIdealUnit_coe K v⟩
    by_contra hne
    exact hv (le_sup_right.trans (v.isMaximal.eq_of_le hne le_sup_left).ge)

/-- The supported group is generated by precisely the primes dividing m. -/
theorem modulusSupportedIdeals_eq_primeGeneratedGroup (m : Ideal (𝓞 K)) :
    modulusSupportedIdeals K m = primeGeneratedGroup K {v | m ≤ v.asIdeal} := by
  rw [modulusSupportedIdeals, primeGeneratedGroup]
  congr 1
  ext u
  constructor
  · rintro ⟨v, hv, hu⟩
    exact ⟨v, hv, Units.ext (by rw [primeIdealUnit_coe, hu])⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, primeIdealUnit_coe K v⟩

/-- Good fractional ideals have zero prime exponent at every divisor of the modulus. -/
theorem mem_coprimeIdeals_iff_count_eq_zero (m : Ideal (𝓞 K))
    (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    u ∈ coprimeIdeals K m ↔
      ∀ p : HeightOneSpectrum (𝓞 K), m ≤ p.asIdeal →
        FractionalIdeal.count K p (u : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rw [coprimeIdeals_eq_primeGeneratedGroup]
  constructor
  · intro hu p hp
    exact count_zero_of_mem_primeGeneratedGroup K _ u hu p (by simpa using hp)
  · intro h
    exact mem_primeGeneratedGroup_of_count_zero K _ u fun v hv => h v (by simpa using hv)

/-- Supported fractional ideals have zero prime exponent outside the modulus support. -/
theorem mem_modulusSupportedIdeals_iff_count_eq_zero (m : Ideal (𝓞 K))
    (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    u ∈ modulusSupportedIdeals K m ↔
      ∀ p : HeightOneSpectrum (𝓞 K), ¬m ≤ p.asIdeal →
        FractionalIdeal.count K p (u : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rw [modulusSupportedIdeals_eq_primeGeneratedGroup]
  constructor
  · intro hu p hp
    exact count_zero_of_mem_primeGeneratedGroup K _ u hu p (by simpa using hp)
  · intro h
    exact mem_primeGeneratedGroup_of_count_zero K _ u fun v hv => h v (by simpa using hv)

/-- Unique prime factorization detects the identity fractional-ideal unit. -/
theorem fractionalIdealUnit_eq_one_of_count_eq_zero
    (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hu : ∀ p : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K p (u : FractionalIdeal (𝓞 K)⁰ K) = 0) : u = 1 := by
  rw [← exponentIdealProduct_idealExponentVector K u]
  have h0 : idealExponentVector K u = 0 := by
    ext v
    rw [idealExponentVector_apply]
    exact hu v
  rw [h0, exponentIdealProduct, Finsupp.prod_zero_index]

/-- Fractional ideals supported on m and prime to m have trivial intersection. -/
theorem modulusSupportedIdeals_inf_coprime (m : Ideal (𝓞 K)) :
    modulusSupportedIdeals K m ⊓ coprimeIdeals K m = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have h1 : u ∈ modulusSupportedIdeals K m := hu.1
  have h2 : u ∈ coprimeIdeals K m := hu.2
  rw [mem_modulusSupportedIdeals_iff_count_eq_zero] at h1
  rw [mem_coprimeIdeals_iff_count_eq_zero] at h2
  exact fractionalIdealUnit_eq_one_of_count_eq_zero K u fun p => by
    by_cases hp : m ≤ p.asIdeal
    · exact h2 p hp
    · exact h1 p hp

/-- The kernel of the principal-ideal homomorphism is the integer unit group. -/
theorem principalIdeal_eq_one_iff (a : Kˣ) :
    toPrincipalIdeal (𝓞 K) K a = 1 ↔
      ∃ u : (𝓞 K)ˣ, Units.map (algebraMap (𝓞 K) K).toMonoidHom u = a := by
  rw [toPrincipalIdeal_eq_iff, Units.val_one]
  constructor
  · intro h
    have ha : (a : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) :=
      h ▸ FractionalIdeal.mem_spanSingleton_self _ _
    obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    have h1 : (1 : K) ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) :=
      h ▸ (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
    obtain ⟨z, hz⟩ := (FractionalIdeal.mem_spanSingleton _).mp h1
    have hxz : x * z = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, hx, map_one, mul_comm, ← hz, Algebra.smul_def]
    refine ⟨⟨x, z, hxz, by rw [mul_comm]; exact hxz⟩, Units.ext ?_⟩
    simpa using hx
  · rintro ⟨u, rfl⟩
    change FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K (u : 𝓞 K)) = 1
    rw [← FractionalIdeal.coeIdeal_span_singleton,
      Ideal.span_singleton_eq_top.mpr u.isUnit, FractionalIdeal.coeIdeal_top]

/-- The class-group kernel is precisely the principal fractional ideals. -/
theorem classGroup_mk_ker_eq_principal_range :
    (ClassGroup.mk K : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ClassGroup (𝓞 K)).ker =
      (toPrincipalIdeal (𝓞 K) K).range := by
  ext I
  rw [MonoidHom.mem_ker, ClassGroup.mk_eq_one_iff, mem_principal_ideals_iff]
  constructor
  · rintro ⟨⟨x, hx⟩⟩
    exact ⟨x, FractionalIdeal.coeToSubmodule_inj.mp (by rw [FractionalIdeal.coe_spanSingleton, hx])⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, by rw [← hx, FractionalIdeal.coe_spanSingleton]⟩⟩

end Cox.ClassFieldTheory
