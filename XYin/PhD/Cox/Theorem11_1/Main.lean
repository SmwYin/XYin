/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassField
import XYin.PhD.Cox.Theorem11_1.Integrality
import XYin.PhD.Cox.Theorem11_1.SingularModulusBridge
import XYin.PhD.Cox.Theorem11_1.Reduction
import XYin.PhD.Cox.Theorem11_1.Residue

/-!
# Cox Theorem 11.1

For an order `O` of an imaginary quadratic field `K` and an invertible fractional ideal `I`
of `O`, the value `j(I)` is an algebraic integer (`theorem_11_1_i`), and `K(j(I))` is the
ring class field of `O` (`theorem_11_1_ii`). The ring class field is defined by its Artin
kernel, and its existence is proved independently of the modular invariant.

The proof follows the two prime-set inclusions of Cox, pp. 238–239. Primes splitting
completely in the ring class field split completely in `K(j(I))` (Cox (11.29)–(11.30)),
so `K(j(I))` lies in the ring class field. Conversely, a degree-one prime of `K(j(I))`
outside a finite set is a norm from `O` (Cox (11.31)–(11.33)), which gives the reverse
inclusion by Cox Proposition 8.20.
-/

open NumberField Polynomial
open scoped nonZeroDivisors Polynomial.Bivariate

noncomputable section

namespace Cox

variable {K : IntermediateField ℚ ℂ} [hNF : NumberField K]
variable (O : Subalgebra ℤ K) [hO : IsOrder O] [hIQ : IsImaginaryQuadraticField K]

include hNF hO hIQ

/-- Source: Cox Theorem 11.1, p. 220; integrality proof p. 237. -/
theorem theorem_11_1_i (I : (FractionalIdeal O⁰ K)ˣ) :
    IsIntegral ℤ (Order.idealJ O I) :=
  singularModulus_isIntegral (Order.idealJ_isSingularModulus O I)

/-- Source: Cox, p. 238, the diagonal equation for a primitive element of prime norm. -/
theorem prime_norm_diagonal_root (I : (FractionalIdeal O⁰ K)ˣ)
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (hp : (p : ℕ) ∈ Order.normPrimes O) :
    (modularPolynomialDiagonal p).eval₂ (Int.castRingHom ℂ) (Order.idealJ O I) = 0 := by
  obtain ⟨hpp, α, hα⟩ := hp
  have hN : Order.elementNorm O α = p := by
    have h := Order.elementNorm_eq_fieldNorm O α
    rw [hα] at h
    exact_mod_cast h
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h0 : Order.elementNorm O 0 = 0 := by simp [Order.elementNorm]
    rw [h0] at hN
    exact hpp.ne_zero hN.symm
  have hαK : (α : K) ≠ 0 := fun h => hα0 (Subtype.ext h)
  have hunit : IsUnit ((Ideal.span {α} : Ideal O) : FractionalIdeal O⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton]
    exact ⟨toPrincipalIdeal O K (Units.mk0 _ hαK), coe_toPrincipalIdeal _⟩
  have hprimI : Order.IsPrimitiveIdeal O (Ideal.span {α}) :=
    Order.isPrimitiveIdeal_of_prime_norm O _ hunit
      (by rw [Order.idealNorm_span_singleton, hN]; exact hpp)
  have hprim := (Order.isPrimitiveIdeal_span_singleton_iff O α hα0).mp hprimI
  have hpos : 0 < Order.elementNorm O α := by
    rw [hN]
    exact hpp.pos
  obtain ⟨S, hS⟩ := Order.exists_principal_cyclicSublattice O α hα0 hprim I hpos
  let S' : PeriodPair.CyclicSublattice (Order.periodPair O I) p :=
    ⟨S.carrier, S.index_eq.trans hN, S.cyclic⟩
  have hj : S'.j = S.j := PeriodPair.j_congr (by
    rw [PeriodPair.CyclicSublattice.toPeriodPair_lattice,
      PeriodPair.CyclicSublattice.toPeriodPair_lattice])
  rw [Polynomial.eval₂_eq_eval_map, modularPolynomialDiagonal,
    ← Polynomial.map_mapRingHom_eval_map, Polynomial.map_X, Polynomial.Bivariate.eval_eval_X]
  exact (theorem_11_23 p _ _).mpr ⟨_, S', by rw [hj, hS], rfl⟩

omit hNF hO hIQ in
/-- The diagonal modular polynomial evaluates as `Φ_m(x, x)`. -/
theorem modularPolynomialDiagonal_eval₂ {R : Type*} [CommRing R] (m : ℕ+) (x : R) :
    (modularPolynomialDiagonal m).eval₂ (Int.castRingHom R) x =
      ((modularPolynomial m).map (mapRingHom (Int.castRingHom R))).evalEval x x := by
  rw [Polynomial.eval₂_eq_eval_map, modularPolynomialDiagonal,
    ← Polynomial.map_mapRingHom_eval_map, Polynomial.map_X, Polynomial.Bivariate.eval_eval_X]

omit hNF hO hIQ in
/-- Ring maps commute with evaluating an integer polynomial. -/
theorem map_eval₂_intCast {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (q : ℤ[X]) (x : R) :
    g (q.eval₂ (Int.castRingHom R) x) = q.eval₂ (Int.castRingHom S) (g x) := by
  rw [Polynomial.hom_eval₂, RingHom.ext_int (g.comp (Int.castRingHom R)) (Int.castRingHom S)]

omit hNF hO hIQ in
/-- Ring maps commute with evaluating an integer bivariate polynomial. -/
theorem map_evalEval_intCast {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (Φ : ℤ[X][Y]) (x y : R) :
    g ((Φ.map (mapRingHom (Int.castRingHom R))).evalEval x y) =
      (Φ.map (mapRingHom (Int.castRingHom S))).evalEval (g x) (g y) := by
  rw [← Polynomial.map_mapRingHom_evalEval, Polynomial.map_map, Polynomial.mapRingHom_comp,
    RingHom.ext_int (g.comp (Int.castRingHom R)) (Int.castRingHom S)]

/-- Source: Cox (11.30), p. 238, reduction of the prime-norm diagonal equation. -/
theorem idealJ_pow_eq_of_normPrime (I : (FractionalIdeal O⁰ K)ˣ)
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (hp : (p : ℕ) ∈ Order.normPrimes O)
    (P : Ideal (𝓞 (generatedField K (Order.idealJ O I))))
    (hP : P ∈ (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ).primesOver
      (𝓞 (generatedField K (Order.idealJ O I))))
    (x : 𝓞 (generatedField K (Order.idealJ O I)))
    (hx : ((x : generatedField K (Order.idealJ O I)) : ℂ) = Order.idealJ O I) :
    (Ideal.Quotient.mk P x) ^ (p : ℕ) = Ideal.Quotient.mk P x := by
  haveI := generatedField_numberField K _ (theorem_11_1_i O I)
  haveI := hP.1
  haveI := residue_charP (Fact.out : (p : ℕ).Prime) P hP
  have hι : Function.Injective ((algebraMap (generatedField K (Order.idealJ O I)) ℂ).comp
      (algebraMap (𝓞 (generatedField K (Order.idealJ O I)))
        (generatedField K (Order.idealJ O I)))) := by
    rw [RingHom.coe_comp]
    exact (algebraMap (generatedField K (Order.idealJ O I)) ℂ).injective.comp
      (IsFractionRing.injective (𝓞 (generatedField K (Order.idealJ O I))) _)
  -- Reflect the diagonal equation into the ring of integers, then reduce modulo `P`.
  have hx0 : (modularPolynomialDiagonal p).eval₂ (Int.castRingHom _) x = 0 := by
    apply hι
    rw [map_zero, map_eval₂_intCast]
    change (modularPolynomialDiagonal p).eval₂ (Int.castRingHom ℂ)
      ((x : generatedField K (Order.idealJ O I)) : ℂ) = 0
    rw [hx]
    exact prime_norm_diagonal_root O I p hp
  have h := congrArg (Ideal.Quotient.mk P) hx0
  rw [map_zero, map_eval₂_intCast, modularPolynomialDiagonal_eval₂] at h
  exact pow_eq_of_modularPolynomial_diagonal_root p h

/-- Source: Cox (11.29), p. 238, using (11.30) and Exercise 11.21. -/
theorem splittingPrimes_almostSubset_generatedField {L : IntermediateField ℚ ℂ}
    (hL : Order.IsRingClassField O L) (I : (FractionalIdeal O⁰ K)ˣ) :
    AlmostSubset (splittingPrimes L) (splittingPrimes (generatedField K (Order.idealJ O I))) := by
  haveI := hL.numberField
  have hint := theorem_11_1_i O I
  haveI := generatedField_numberField K _ hint
  haveI := finite_quotient_generatedIntegerOrder K _ hint
  have hKM : K ≤ generatedField K (Order.idealJ O I) := le_generatedField K _
  letI : Algebra K (generatedField K (Order.idealJ O I)) :=
    (IntermediateField.inclusion hKM).toRingHom.toAlgebra
  obtain ⟨d, hd, hdS⟩ := exists_pos_nsmul_mem _ (generatedIntegerOrder K (Order.idealJ O I))
  -- Exceptions: the norm criterion, prime divisors of the index `d`, and ramified primes.
  refine (Set.Finite.union (Order.splittingPrimes_norm_criterion O hL)
    (Set.Finite.union (finite_prime_divisors d hd.ne')
      (finite_ramifiedPrimes (generatedField K (Order.idealJ O I))))).subset
    fun p ⟨hpL, hpM⟩ => ?_
  by_contra hmem
  have hpp : p.Prime := hpL.1.1
  have hpn : p ∈ Order.normPrimes O := by
    by_contra h
    exact hmem (Or.inl ⟨hpL, h⟩)
  have hpd : ¬ p ∣ d := fun h => hmem (Or.inr (Or.inl ⟨hpp, h⟩))
  have hpu : p ∈ unramifiedPrimes (generatedField K (Order.idealJ O I)) := by
    by_contra h
    exact hmem (Or.inr (Or.inr ⟨hpp, h⟩))
  have hpK : p ∈ splittingPrimes K := splittingPrimes_mono hL.le hpL
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpp).irreducible
  apply hpM
  refine ⟨hpu, fun P hP => ?_⟩
  haveI := hP.1
  haveI := hP.2
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  haveI := residue_charP hpp P hP
  rw [inertiaDeg_eq_one_iff_forall_pow_eq hpp P hP]
  letI : Field ((𝓞 (generatedField K (Order.idealJ O I))) ⧸ P) := Ideal.Quotient.field P
  intro z
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  -- Frobenius on the generators of `O_K[j]`, then on `O_M` since `p ∤ d`.
  refine pow_eq_of_nsmul_mem p (Ideal.Quotient.mk P) _ d hpd ?_ hdS w
  refine pow_eq_on_adjoin p (Ideal.Quotient.mk P) _ fun z hz => ?_
  rcases hz with hzK | hzj
  · -- Elements of `O_K`: the contraction of `P` has degree one since `p` splits in `K`.
    have hzint : IsIntegral ℤ (⟨_, hzK⟩ : K) :=
      (isIntegral_algHom_iff ((IntermediateField.inclusion hKM).restrictScalars ℤ)
        (IntermediateField.inclusion hKM).injective).mp (RingOfIntegers.isIntegral_coe z)
    have hzz : algebraMap (𝓞 K) _ ⟨⟨_, hzK⟩, hzint⟩ = z := RingOfIntegers.ext rfl
    have hqP : P.under (𝓞 K) ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) :=
      ⟨inferInstance, inferInstance⟩
    have hfrob := (inertiaDeg_eq_one_iff_forall_pow_eq hpp _ hqP).mp (hpK.2 _ hqP)
      (Ideal.Quotient.mk _ ⟨⟨_, hzK⟩, hzint⟩)
    have h := quotient_pow_eq_of_le_comap (algebraMap (𝓞 K) _) _ P le_rfl p _ hfrob
    rwa [hzz] at h
  · let p' : ℕ+ := ⟨p, hpp.pos⟩
    haveI : Fact (Nat.Prime (p' : ℕ)) := ⟨hpp⟩
    exact idealJ_pow_eq_of_normPrime O I p' hpn P hP z hzj

/-- Source: Cox, p. 238, Proposition 8.20(i) applied to (11.29). -/
theorem generatedField_le_ringClassField {L : IntermediateField ℚ ℂ}
    (hL : Order.IsRingClassField O L) (I : (FractionalIdeal O⁰ K)ˣ) :
    generatedField K (Order.idealJ O I) ≤ L := by
  haveI := hL.numberField
  haveI := Order.isGalois_ringClassField O hL
  haveI := generatedField_numberField K _ (theorem_11_1_i O I)
  exact (le_iff_splittingPrimes_almostSubset _ L).mpr
    (splittingPrimes_almostSubset_generatedField O hL I)

/-- Source: Cox, p. 239, the first inclusion holds for every proper ideal. -/
theorem idealJ_mem_ringClassField {L : IntermediateField ℚ ℂ}
    (hL : Order.IsRingClassField O L) (I : (FractionalIdeal O⁰ K)ˣ) :
    Order.idealJ O I ∈ L := by
  exact generatedField_le_ringClassField O hL I (mem_generatedField K _)

/-- Source: Cox, p. 239, every class value is an algebraic integer in the class field. -/
theorem exists_idealJ_integer {L : IntermediateField ℚ ℂ}
    (hL : Order.IsRingClassField O L) (I : (FractionalIdeal O⁰ K)ˣ) :
    ∃ x : 𝓞 L, ((x : L) : ℂ) = Order.idealJ O I := by
  haveI := hL.numberField
  have hmem := idealJ_mem_ringClassField O hL I
  have hint : IsIntegral ℤ (⟨_, hmem⟩ : L) :=
    (isIntegral_algHom_iff (L.val.restrictScalars ℤ) Subtype.val_injective).mp
      (theorem_11_1_i O I)
  exact ⟨⟨⟨_, hmem⟩, hint⟩, rfl⟩

/-- Source: Cox, p. 239, the values are indexed by the finite ideal class group. -/
theorem finite_idealJ_range : (Set.range (Order.idealJ O)).Finite := by
  classical
  haveI := Order.finite_classGroup O
  -- Choose one ideal in each class that occurs.
  let g : ClassGroup O → ℂ := fun c =>
    if h : ∃ J, Order.idealClass O J = c then Order.idealJ O h.choose else 0
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨I, rfl⟩
  have h : ∃ J, Order.idealClass O J = Order.idealClass O I := ⟨I, rfl⟩
  refine ⟨Order.idealClass O I, ?_⟩
  simp only [g, dif_pos h]
  exact (Order.idealJ_eq_iff_idealClass_eq O _ _).mpr h.choose_spec

/-- Source: Cox (11.31), p. 239: distinct class values stay distinct away from finitely many
primes. -/
theorem idealClass_eq_of_reduction_outside_finite {L : IntermediateField ℚ ℂ}
    (hL : Order.IsRingClassField O L) :
    ∃ e : Set ℕ, e.Finite ∧ ∀ p ∉ e, p.Prime →
      ∀ P ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L),
        ∀ (I J : (FractionalIdeal O⁰ K)ˣ) (x y : 𝓞 L),
          ((x : L) : ℂ) = Order.idealJ O I →
          ((y : L) : ℂ) = Order.idealJ O J →
          Ideal.Quotient.mk P x = Ideal.Quotient.mk P y →
          Order.idealClass O I = Order.idealClass O J := by
  haveI := hL.numberField
  haveI : Finite (Set.range (Order.idealJ O)) := (finite_idealJ_range O).to_subtype
  -- Integral lifts of the finitely many class values.
  have hlift : ∀ v : Set.range (Order.idealJ O), ∃ z : 𝓞 L, ((z : L) : ℂ) = v := by
    rintro ⟨_, I, rfl⟩
    exact exists_idealJ_integer O hL I
  choose j hj using hlift
  have hcoe : ∀ z w : 𝓞 L, ((z : L) : ℂ) = ((w : L) : ℂ) → z = w := fun z w h =>
    RingOfIntegers.ext (Subtype.ext h)
  have hinj : Function.Injective j := fun v w h =>
    Subtype.ext ((hj v).symm.trans ((congrArg (fun z : 𝓞 L => ((z : L) : ℂ)) h).trans (hj w)))
  obtain ⟨e, he, hred⟩ := finite_collision_primes L j hinj
  refine ⟨e, he, fun p hpe hp P hP I J x y hx hy hxy => ?_⟩
  have hxj : x = j ⟨_, I, rfl⟩ := hcoe _ _ (hx.trans (hj ⟨_, I, rfl⟩).symm)
  have hyj : y = j ⟨_, J, rfl⟩ := hcoe _ _ (hy.trans (hj ⟨_, J, rfl⟩).symm)
  rw [hxj, hyj] at hxy
  exact (Order.idealJ_eq_iff_idealClass_eq O I J).mp
    (congrArg Subtype.val (hred p hpe hp P hP hxy))

/-- Source: Cox, p. 239, the cyclic modular equation for the prime-ideal product. -/
theorem prime_norm_ideal_modularPolynomial (a : Ideal O)
    (ha : IsUnit (a : FractionalIdeal O⁰ K)) (I : (FractionalIdeal O⁰ K)ˣ)
    (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] (hp : Order.idealNorm O a = (p : ℕ)) :
    ((modularPolynomial p).map (mapRingHom (Int.castRingHom ℂ))).evalEval
      (Order.idealJ O I) (Order.idealJ O (Order.integralIdealUnit O a ha * I)) = 0 := by
  have hprim : Order.IsPrimitiveIdeal O a :=
    Order.isPrimitiveIdeal_of_prime_norm O a ha (by rw [hp]; exact Fact.out)
  have hpos : 0 < Order.idealNorm O a := by
    rw [hp]
    exact p.pos
  obtain ⟨S, hS⟩ := Order.exists_cyclicSublattice O a ha hprim I hpos
  let S' : PeriodPair.CyclicSublattice (Order.periodPair O I) p :=
    ⟨S.carrier, S.index_eq.trans hp, S.cyclic⟩
  have hj : S'.j = S.j := PeriodPair.j_congr (by
    rw [PeriodPair.CyclicSublattice.toPeriodPair_lattice,
      PeriodPair.CyclicSublattice.toPeriodPair_lattice])
  exact (theorem_11_23 p _ _).mpr ⟨_, S', by rw [hj, hS], rfl⟩

/-- Source: Cox, p. 239, cancel the ideal class and take the norm of a principal generator. -/
theorem normPrime_of_idealClass_mul_eq (a : Ideal O)
    (ha : IsUnit (a : FractionalIdeal O⁰ K)) (I : (FractionalIdeal O⁰ K)ˣ)
    (p : ℕ) (hp : p.Prime) (hnorm : Order.idealNorm O a = p)
    (hclass : Order.idealClass O (Order.integralIdealUnit O a ha * I) =
      Order.idealClass O I) : p ∈ Order.normPrimes O := by
  -- The class of `a` is trivial.
  have h1 : Order.idealClass O (Order.integralIdealUnit O a ha) = Order.idealClass O 1 := by
    have h := hclass
    rw [Order.idealClass, Order.idealClass, map_mul] at h
    rw [Order.idealClass, Order.idealClass, map_one]
    exact mul_right_cancel (h.trans (one_mul _).symm)
  obtain ⟨u, hu⟩ := (Order.idealClass_eq_iff_exists_principal O _ _).mp h1.symm
  have hu' : (a : FractionalIdeal O⁰ K) = FractionalIdeal.spanSingleton O⁰ (u : K) := by
    rw [← Order.coe_integralIdealUnit O a ha, ← hu, one_mul, coe_toPrincipalIdeal]
  -- Its generator lies in `a`, hence in `O`.
  have hmem : (u : K) ∈ (a : FractionalIdeal O⁰ K) := by
    rw [hu']
    exact FractionalIdeal.mem_spanSingleton_self O⁰ (u : K)
  obtain ⟨α, -, hα⟩ := (FractionalIdeal.mem_coeIdeal O⁰).mp hmem
  have hspan : a = Ideal.span {α} := by
    apply FractionalIdeal.coeIdeal_injective (K := K)
    beta_reduce
    rw [hu', FractionalIdeal.coeIdeal_span_singleton, hα]
  have hN : Order.elementNorm O α = p := by
    rw [← Order.idealNorm_span_singleton, ← hspan, hnorm]
  exact ⟨hp, α, by rw [← Order.elementNorm_eq_fieldNorm, hN]⟩

/-- Source: Cox, p. 239, (11.32)–(11.33), avoiding (11.31) and conductor primes. -/
theorem degreeOnePrimes_almostSubset_normPrimes {L : IntermediateField ℚ ℂ}
    (hL : Order.IsRingClassField O L) (I : (FractionalIdeal O⁰ K)ˣ) :
    AlmostSubset (degreeOnePrimes (generatedField K (Order.idealJ O I)))
      (Order.normPrimes O) := by
  haveI := hL.numberField
  have hint := theorem_11_1_i O I
  haveI := generatedField_numberField K _ hint
  have hKM : K ≤ generatedField K (Order.idealJ O I) := le_generatedField K _
  have hML : generatedField K (Order.idealJ O I) ≤ L := generatedField_le_ringClassField O hL I
  letI : Algebra K (generatedField K (Order.idealJ O I)) :=
    (IntermediateField.inclusion hKM).toRingHom.toAlgebra
  letI : Algebra (generatedField K (Order.idealJ O I)) L :=
    (IntermediateField.inclusion hML).toRingHom.toAlgebra
  obtain ⟨e, he, hcol⟩ := idealClass_eq_of_reduction_outside_finite O hL
  -- Exceptions: the collision primes and the prime divisors of the conductor.
  refine (Set.Finite.union he (Order.conductor O).divisors.finite_toSet).subset
    fun p ⟨hpM, hpn⟩ => ?_
  by_contra hmem
  have hpp : p.Prime := hpM.1.1
  have hpe : p ∉ e := fun h => hmem (Or.inl h)
  have hcop : p.Coprime (Order.conductor O) := (Nat.Prime.coprime_iff_not_dvd hpp).mpr fun h =>
    hmem (Or.inr (Finset.mem_coe.mpr (Nat.mem_divisors.mpr ⟨h, (Order.conductor_pos O).ne'⟩)))
  apply hpn
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpp).irreducible
  -- A degree-one prime `P` of `M = K(j(I))` over `p`; its contraction to `K` has norm `p`.
  obtain ⟨-, P, hP, hPf⟩ := hpM
  haveI := hP.1
  haveI := hP.2
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  haveI : (P.under (𝓞 K)).IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal (P.under (𝓞 K)) (Ideal.span {(p : ℤ)})
  have hf := Ideal.inertiaDeg_algebra_tower (Ideal.span {(p : ℤ)} : Ideal ℤ) (P.under (𝓞 K)) P
  rw [hPf] at hf
  have hqn : (P.under (𝓞 K)).absNorm = p := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg' _ hpp, (mul_eq_one.mp hf.symm).1, pow_one]
  -- Contract it to an invertible ideal `a` of `O` of norm `p`.
  have hq0 : P.under (𝓞 K) ≠ ⊥ := fun h => by
    rw [h, Ideal.absNorm_bot] at hqn
    exact hpp.ne_zero hqn.symm
  have hcard : Nat.card ((𝓞 K) ⧸ P.under (𝓞 K)) = p := by
    rw [← hqn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hcop' : (Nat.card ((𝓞 K) ⧸ P.under (𝓞 K))).Coprime (Order.conductor O) := hcard ▸ hcop
  have ha0 : Order.contractIdeal O (P.under (𝓞 K)) ≠ ⊥ := by
    intro h
    apply hq0
    rw [← Order.extend_contract O _ hcop', h, Order.extendIdeal, Ideal.map_bot]
  have hunit := Order.isUnit_of_isPrimeToConductor O _
    (Order.isPrimeToConductor_contract O _ hcop') ha0
  have hnorm : Order.idealNorm O (Order.contractIdeal O (P.under (𝓞 K))) = p :=
    (Order.idealNorm_contract O _ hcop').trans hcard
  -- A prime `Q` of `L` over `P`.
  obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) P
  haveI := hQ.1
  haveI := hQ.2
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  have hQp : Q ∈ (Ideal.span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 L) := ⟨hQ.1, inferInstance⟩
  -- Integral lifts of `j(I)` and `j(aI)` in `L`.
  obtain ⟨x, hx⟩ := exists_idealJ_integer O hL I
  obtain ⟨y, hy⟩ := exists_idealJ_integer O hL
    (Order.integralIdealUnit O (Order.contractIdeal O (P.under (𝓞 K))) hunit * I)
  let p' : ℕ+ := ⟨p, hpp.pos⟩
  haveI : Fact (Nat.Prime (p' : ℕ)) := ⟨hpp⟩
  haveI : CharP ((𝓞 L) ⧸ Q) (p' : ℕ) := residue_charP hpp Q hQp
  -- Reduce the modular equation modulo `Q`.
  have hι : Function.Injective ((algebraMap L ℂ).comp (algebraMap (𝓞 L) L)) :=
    fun _ _ h => IsFractionRing.injective _ _ ((algebraMap L ℂ).injective h)
  have hxy0 : ((modularPolynomial p').map (mapRingHom (Int.castRingHom (𝓞 L)))).evalEval
      x y = 0 := by
    apply hι
    rw [map_zero, map_evalEval_intCast]
    change ((modularPolynomial p').map (mapRingHom (Int.castRingHom ℂ))).evalEval
      ((x : L) : ℂ) ((y : L) : ℂ) = 0
    rw [hx, hy]
    exact prime_norm_ideal_modularPolynomial O _ hunit I p' hnorm
  have hxyQ := congrArg (Ideal.Quotient.mk Q) hxy0
  rw [map_zero, map_evalEval_intCast] at hxyQ
  -- Degree one in `M` gives the Frobenius identity for `j(I)`, which passes up to `Q`.
  let xM : 𝓞 (generatedField K (Order.idealJ O I)) := ⟨⟨_, mem_generatedField K _⟩,
    (isIntegral_algHom_iff ((generatedField K (Order.idealJ O I)).val.restrictScalars ℤ)
      Subtype.val_injective).mp hint⟩
  have hxM : algebraMap _ (𝓞 L) xM = x := RingOfIntegers.ext (Subtype.ext hx.symm)
  have hfrob := quotient_pow_eq_of_le_comap (algebraMap _ (𝓞 L)) P Q hQ.2.over.le p xM
    ((inertiaDeg_eq_one_iff_forall_pow_eq hpp P hP).mp hPf (Ideal.Quotient.mk P xM))
  rw [hxM] at hfrob
  -- Hence `j(aI) ≡ j(I)` modulo `Q`, so `aI` and `I` have the same class.
  have hyx := eq_of_modularPolynomial_root_of_pow_eq p' hxyQ hfrob
  exact normPrime_of_idealClass_mul_eq O _ hunit I p hpp hnorm
    (hcol p hpe hpp Q hQp _ I y x hy hx hyx)

/-- Source: Cox, p. 239, the reverse splitting-prime inclusion. -/
theorem degreeOnePrimes_almostSubset_ringClassField {L : IntermediateField ℚ ℂ}
    (hL : Order.IsRingClassField O L) (I : (FractionalIdeal O⁰ K)ˣ) :
    AlmostSubset (degreeOnePrimes (generatedField K (Order.idealJ O I)))
      (splittingPrimes L) := by
  exact AlmostSubset.trans (degreeOnePrimes_almostSubset_normPrimes O hL I)
    (Order.normPrimes_splitting_criterion O hL)

/-- Source: Cox, p. 239, Proposition 8.20(ii) applied to the reverse prime-set inclusion. -/
theorem ringClassField_le_generatedField {L : IntermediateField ℚ ℂ}
    (hL : Order.IsRingClassField O L) (I : (FractionalIdeal O⁰ K)ˣ) :
    L ≤ generatedField K (Order.idealJ O I) := by
  haveI := hL.numberField
  haveI := Order.isGalois_ringClassField O hL
  haveI := generatedField_numberField K _ (theorem_11_1_i O I)
  exact (le_iff_degreeOnePrimes_almostSubset L _).mpr
    (degreeOnePrimes_almostSubset_ringClassField O hL I)

/-- Source: Cox, conclusion of the proof of Theorem 11.1, p. 239. -/
theorem generatedField_eq_ringClassField {L : IntermediateField ℚ ℂ}
    (hL : Order.IsRingClassField O L) (I : (FractionalIdeal O⁰ K)ˣ) :
    generatedField K (Order.idealJ O I) = L := by
  exact le_antisymm (generatedField_le_ringClassField O hL I)
    (ringClassField_le_generatedField O hL I)

/-- Source: Cox Theorem 11.1, p. 220; ring-class-field proof pp. 238–239. -/
theorem theorem_11_1_ii (I : (FractionalIdeal O⁰ K)ˣ) :
    Order.IsRingClassField O (generatedField K (Order.idealJ O I)) := by
  obtain ⟨L, hL⟩ := Order.exists_ringClassField O
  rw [generatedField_eq_ringClassField O hL I]
  exact hL

end Cox
