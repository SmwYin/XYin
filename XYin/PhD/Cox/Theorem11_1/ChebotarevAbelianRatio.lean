/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevDefs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Proportions of elements with large order

Source: AINTLIB Abelian.lean, revision `953409d221e42e247e32db31def5444fe60f3f87`, lines 897–1295.
Only the general finite-group branch needed for the admissible prime moduli is included.
-/

noncomputable section
open Filter Topology
open scoped Nat
namespace Cox.Chebotarev

/-- Source: AINTLIB Abelian.lean:910–913, kernel/range cardinality calculation. -/
theorem card_pow_ker_mul_range (G : Type*) [CommGroup G] [Finite G] (M : ℕ) :
    Nat.card (powMonoidHom (α := G) M).ker * Nat.card (powMonoidHom (α := G) M).range
      = Nat.card G := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (powMonoidHom (α := G) M).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (powMonoidHom (α := G) M)).toEquiv]
  ring

/-- Source: AINTLIB Abelian.lean:917–920, cyclic subgroup contained in the power range. -/
theorem order_pow_le_card_range (G : Type*) [CommGroup G] [Finite G] (g : G) (M : ℕ) :
    orderOf (g ^ M) ≤ Nat.card (powMonoidHom (α := G) M).range := by
  rw [← Nat.card_zpowers]
  exact Nat.card_le_card_of_injective (Subgroup.inclusion (by
    rw [Subgroup.zpowers_le]; exact ⟨g, rfl⟩)) (Subgroup.inclusion_injective _)

/-- Source: AINTLIB Abelian.lean:914–916, an element of exponent order. -/
theorem exists_order_pow_eq_exponent_div_gcd (G : Type*) [CommGroup G] [Finite G] (M : ℕ) :
    ∃ g : G, orderOf (g ^ M) = Monoid.exponent G / Nat.gcd (Monoid.exponent G) M := by
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (Monoid.ExponentExists.of_finite (G := G))
  exact ⟨g, by rw [orderOf_pow, hg]⟩

/-- Source: AINTLIB Abelian.lean:903, finite-group proportion argument. -/
theorem torsion_card_le (G : Type*) [CommGroup G] [Finite G] (M : ℕ) :
    Nat.card {x : G // x ^ M = 1} * (Monoid.exponent G / Nat.gcd (Monoid.exponent G) M)
      ≤ Nat.card G := by
  classical
  have hker : Nat.card (powMonoidHom (α := G) M).ker = Nat.card {x : G // x ^ M = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by rw [MonoidHom.mem_ker]; rfl)
  obtain ⟨g, hord⟩ := exists_order_pow_eq_exponent_div_gcd G M
  rw [← hord]
  calc Nat.card {x : G // x ^ M = 1} * orderOf (g ^ M)
      = Nat.card (powMonoidHom (α := G) M).ker * orderOf (g ^ M) := by rw [hker]
    _ ≤ Nat.card (powMonoidHom (α := G) M).ker * Nat.card (powMonoidHom (α := G) M).range :=
        Nat.mul_le_mul_left _ (order_pow_le_card_range G g M)
    _ = Nat.card G := card_pow_ker_mul_range G M

/-- Source: AINTLIB Abelian.lean:929, finite-group proportion argument. -/
theorem factorization_ordCompl_mul_pow (E p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (q : ℕ) :
    (ordCompl[p] E * p ^ (v - 1)).factorization q
      = if q = p then v - 1 else E.factorization q := by
  rw [Nat.factorization_mul (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero)]
  simp only [Finsupp.coe_add, Pi.add_apply, hp.factorization_pow, Finsupp.single_apply,
    Nat.factorization_ordCompl]
  by_cases hq : q = p
  · subst hq; rw [Finsupp.erase_same, if_pos rfl, if_pos rfl, zero_add]
  · rw [Finsupp.erase_ne hq, if_neg fun h ↦ hq h.symm, if_neg hq, add_zero]

/-- Source: AINTLIB Abelian.lean:942, finite-group proportion argument. -/
theorem dvd_capped (E d p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (hd : d ∣ E)
    (hvp : d.factorization p ≤ v - 1) : d ∣ ordCompl[p] E * p ^ (v - 1) := by
  have hdne : d ≠ 0 := fun h ↦ by subst h; exact hE (Nat.eq_zero_of_zero_dvd hd)
  rw [← Nat.factorization_le_iff_dvd hdne
    (mul_ne_zero (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero))]
  intro q
  rw [factorization_ordCompl_mul_pow E p v hp hE q]
  by_cases hq : q = p
  · subst hq; rwa [if_pos rfl]
  · rw [if_neg hq]; exact (Nat.factorization_le_iff_dvd hdne hE).mpr hd q

/-- Source: AINTLIB Abelian.lean:954, finite-group proportion argument. -/
theorem M_dvd_E (E p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (hle : v - 1 ≤ E.factorization p) :
    ordCompl[p] E * p ^ (v - 1) ∣ E := by
  rw [← Nat.factorization_le_iff_dvd
    (mul_ne_zero (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero)) hE]
  intro q
  rw [factorization_ordCompl_mul_pow E p v hp hE q]
  by_cases hq : q = p
  · subst hq; rwa [if_pos rfl]
  · rw [if_neg hq]

/-- Source: AINTLIB Abelian.lean:966, finite-group proportion argument. -/
theorem E_eq_M_mul (E p v : ℕ) (hle : v - 1 ≤ E.factorization p) :
    E = ordCompl[p] E * p ^ (v - 1) * p ^ (E.factorization p - (v - 1)) := by
  rw [mul_assoc, ← pow_add,
    show v - 1 + (E.factorization p - (v - 1)) = E.factorization p by omega,
    mul_comm (ordCompl[p] E), Nat.ordProj_mul_ordCompl_eq_self]

/-- Source: AINTLIB Abelian.lean:998, finite-group proportion argument. -/
theorem bad_le_torsion (G : Type*) [Finite G] [Monoid G] (M p v : ℕ)
    (h : ∀ x : G, ¬ p ^ v ∣ orderOf x → x ^ M = 1) :
    Nat.card {x : G // ¬ p ^ v ∣ orderOf x} ≤ Nat.card {x : G // x ^ M = 1} := by
  exact Nat.card_le_card_of_injective _ (Subtype.impEmbedding _ _ h).injective

/-- Source: AINTLIB Abelian.lean:1005, finite-group proportion argument. -/
theorem exists_prime_pow_not_dvd (n d : ℕ) (hn : n ≠ 0) (hd : d ≠ 0) (hndvd : ¬ n ∣ d) :
    ∃ p ∈ n.primeFactors, ¬ p ^ (n.factorization p) ∣ d := by
  by_contra! hcon
  apply hndvd
  rw [← Nat.factorization_le_iff_dvd hn hd]
  intro p
  by_cases hp : p ∈ n.primeFactors
  · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact (Nat.Prime.pow_dvd_iff_le_factorization hpp hd).mp (hcon p hp)
  · have hzero : n.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hp
    rw [hzero]; exact Nat.zero_le _

/-- Source: AINTLIB Abelian.lean:1020, finite-group proportion argument. -/
theorem card_le_sum_card {G : Type*} [Finite G] {ι : Type*} (s : Finset ι)
    (P : G → Prop) (Q : ι → G → Prop) (h : ∀ x, P x → ∃ i ∈ s, Q i x) :
    Nat.card {x : G // P x} ≤ ∑ i ∈ s, Nat.card {x : G // Q i x} := by
  classical
  have : Fintype G := Fintype.ofFinite G
  simp only [Nat.card_eq_fintype_card]
  calc Fintype.card {x : G // P x}
      = (Finset.univ.filter P).card := by rw [Fintype.card_subtype]
    _ ≤ (s.biUnion (fun i ↦ Finset.univ.filter (Q i))).card := by
        refine Finset.card_le_card (fun x hx ↦ ?_)
        rw [Finset.mem_filter] at hx
        obtain ⟨i, hi, hqi⟩ := h x hx.2
        exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hqi⟩⟩
    _ ≤ ∑ i ∈ s, (Finset.univ.filter (Q i)).card := Finset.card_biUnion_le
    _ = ∑ i ∈ s, Fintype.card {x : G // Q i x} :=
        Finset.sum_congr rfl (fun i _ ↦ by rw [Fintype.card_subtype])

/-- Source: AINTLIB Abelian.lean:1039, finite-group proportion argument. -/
theorem capped_exponent_tendsto (v : ℕ) (hv : 1 ≤ v) :
    Tendsto (fun k : ℕ ↦ k * v - v - 1) atTop atTop := by
  refine tendsto_atTop_mono (f := fun k : ℕ ↦ k - (v + 1)) (fun k ↦ ?_)
    (tendsto_sub_atTop_nat (v + 1))
  have : k ≤ k * v := Nat.le_mul_of_pos_right k hv
  change k - (v + 1) ≤ k * v - v - 1
  omega

/-- Source: AINTLIB Abelian.lean:1039–1050, geometric tail after reindexing. -/
theorem summand_tendsto (p v : ℕ) (hp : 2 ≤ p) (hv : 1 ≤ v) :
    Tendsto (fun k : ℕ ↦ (1 : ℝ) / (p : ℝ) ^ (k * v - v - 1)) atTop (𝓝 0) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hpinv1 : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ hp0]; exact_mod_cast hp.trans_lt' Nat.one_lt_two
  have hbase : Tendsto (fun m : ℕ ↦ ((p : ℝ)⁻¹) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hpinv1
  refine (hbase.comp (capped_exponent_tendsto v hv)).congr (fun k ↦ ?_)
  simp [Function.comp_apply, one_div, inv_pow]

/-- Source: AINTLIB Abelian.lean:1056, finite-group proportion argument. -/
theorem ratio_bound (bad total : ℕ) (s : Finset ℕ) (badp : ℕ → ℕ) (e : ℕ → ℕ) (P : ℕ → ℕ)
    (htot : 0 < total) (hcover : bad ≤ ∑ p ∈ s, badp p) (hP : ∀ p ∈ s, 0 < P p)
    (hbound : ∀ p ∈ s, badp p * (P p) ^ (e p) ≤ total) :
    (bad : ℝ) / total ≤ ∑ p ∈ s, (1 : ℝ) / (P p : ℝ) ^ (e p) := by
  have htotR : (0 : ℝ) < total := by exact_mod_cast htot
  have hnum : (bad : ℝ) ≤ ∑ p ∈ s, (badp p : ℝ) := by
    calc (bad : ℝ) ≤ ((∑ p ∈ s, badp p : ℕ) : ℝ) := by exact_mod_cast hcover
      _ = ∑ p ∈ s, (badp p : ℝ) := by push_cast; ring
  calc (bad : ℝ) / total
      ≤ (∑ p ∈ s, (badp p : ℝ)) / total := by gcongr
    _ = ∑ p ∈ s, (badp p : ℝ) / total := by rw [Finset.sum_div]
    _ ≤ ∑ p ∈ s, (1 : ℝ) / (P p : ℝ) ^ (e p) := by
        refine Finset.sum_le_sum (fun p hps ↦ ?_)
        have hPp : (0 : ℝ) < (P p : ℝ) ^ (e p) := by have := hP p hps; positivity
        rw [div_le_div_iff₀ htotR hPp, one_mul]
        calc (badp p : ℝ) * (P p : ℝ) ^ (e p) = ((badp p * (P p) ^ (e p) : ℕ) : ℝ) := by
              push_cast; ring
          _ ≤ (total : ℝ) := by exact_mod_cast hbound p hps

/-- Source: AINTLIB Abelian.lean:1080, finite-group proportion argument. -/
theorem perprime_bound_core (G : Type*) [CommGroup G] [Finite G] (p v e : ℕ)
    (hp : p.Prime) (hv1 : 1 ≤ v) (he : e + (v - 1) ≤ (Monoid.exponent G).factorization p) :
    Nat.card {x : G // ¬ p ^ v ∣ orderOf x} * p ^ e ≤ Nat.card G := by
  classical
  set E := Monoid.exponent G with hE
  have hEne : E ≠ 0 := hE ▸ (Monoid.ExponentExists.of_finite (G := G)).exponent_ne_zero
  set M := ordCompl[p] E * p ^ (v - 1)
  have hMne : M ≠ 0 := mul_ne_zero (Nat.ordCompl_pos p hEne).ne' (pow_ne_zero _ hp.ne_zero)
  have hle1 : v - 1 ≤ E.factorization p := by omega
  have hMdvdE : M ∣ E := M_dvd_E E p v hp hEne hle1
  have hgcd : Nat.gcd E M = M := Nat.gcd_eq_right hMdvdE
  have hEdivM : E / M = p ^ (E.factorization p - (v - 1)) :=
    Nat.div_eq_of_eq_mul_right (Nat.pos_of_ne_zero hMne) (E_eq_M_mul E p v hle1)
  have hbad_sub : Nat.card {x : G // ¬ p ^ v ∣ orderOf x} ≤ Nat.card {x : G // x ^ M = 1} := by
    refine bad_le_torsion G M p v (fun x hx ↦ ?_)
    rw [← orderOf_dvd_iff_pow_eq_one]
    refine dvd_capped E (orderOf x) p v hp hEne ?_ ?_
    · rw [hE]; exact Monoid.order_dvd_exponent x
    · by_contra! hcon
      exact hx ((Nat.Prime.pow_dvd_iff_le_factorization hp (orderOf_pos x).ne').mpr (by omega))
  have hEM : p ^ e ≤ E / M := by
    rw [hEdivM]; exact pow_le_pow_right₀ hp.one_le (by omega)
  calc Nat.card {x : G // ¬ p ^ v ∣ orderOf x} * p ^ e
      ≤ Nat.card {x : G // x ^ M = 1} * p ^ e := Nat.mul_le_mul_right _ hbad_sub
    _ ≤ Nat.card {x : G // x ^ M = 1} * (E / M) := Nat.mul_le_mul_left _ hEM
    _ = Nat.card {x : G // x ^ M = 1} * (E / Nat.gcd E M) := by rw [hgcd]
    _ ≤ Nat.card G := torsion_card_le G M

/-- Source: AINTLIB Abelian.lean:1133, finite-group proportion argument. -/
theorem perprime_bound_exp (G : Type*) [CommGroup G] [Finite G] (p a v : ℕ)
    (hp : p.Prime) (hv1 : 1 ≤ v) (hav : v ≤ a) (hdvd : p ^ a ∣ Monoid.exponent G) :
    Nat.card {x : G // ¬ p ^ v ∣ orderOf x} * p ^ (a - v - 1) ≤ Nat.card G := by
  have haE : a ≤ (Monoid.exponent G).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp
      (Monoid.ExponentExists.of_finite (G := G)).exponent_ne_zero).mp hdvd
  exact perprime_bound_core G p v _ hp hv1 (by omega)

/-- Source: AINTLIB Abelian.lean:1148, finite-group proportion argument. -/
theorem H_n_ratio_ge (G : Type*) [CommGroup G] [Finite G] (n k : ℕ) (hn2 : 2 ≤ n)
    (hk : 1 ≤ k)
    (hexp : ∀ p ∈ n.primeFactors, p ^ (k * n.factorization p) ∣ Monoid.exponent G) :
    1 - (∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1))
      ≤ (Nat.card {τ : G // n ∣ orderOf τ} : ℝ) / Nat.card G := by
  classical
  set total : ℕ := Nat.card G with htotal
  set good : ℕ := Nat.card {τ : G // n ∣ orderOf τ} with hgood
  set bad : ℕ := Nat.card {τ : G // ¬ n ∣ orderOf τ} with hbad
  have htotpos : 0 < total := Nat.card_pos
  have hgb : good + bad = total := by
    have : Fintype G := Fintype.ofFinite G
    rw [hgood, hbad, htotal]
    simp only [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl]
    have hle : Fintype.card {τ : G // n ∣ orderOf τ} ≤ Fintype.card G :=
      Fintype.card_subtype_le _
    omega
  have hbadratio : (bad : ℝ) / total
      ≤ ∑ p ∈ n.primeFactors,
          (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1) := by
    refine ratio_bound bad total n.primeFactors
      (fun p ↦ Nat.card {τ : G // ¬ p ^ n.factorization p ∣ orderOf τ})
      (fun p ↦ k * n.factorization p - n.factorization p - 1) (fun p ↦ p)
      htotpos ?_ ?_ ?_
    · rw [hbad]
      refine card_le_sum_card n.primeFactors (fun τ ↦ ¬ n ∣ orderOf τ)
        (fun p τ ↦ ¬ p ^ n.factorization p ∣ orderOf τ) (fun τ hτ ↦ ?_)
      exact exists_prime_pow_not_dvd n (orderOf τ) (by omega) (orderOf_pos τ).ne' hτ
    · exact fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos
    · intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hv1 : 1 ≤ n.factorization p := Nat.Prime.factorization_pos_of_dvd hpp (by omega) hpn
      have hav : n.factorization p ≤ k * n.factorization p := Nat.le_mul_of_pos_left _ hk
      exact perprime_bound_exp G p (k * n.factorization p) (n.factorization p) hpp hv1 hav
        (hexp p hp)
  have htk : (total : ℝ) ≠ 0 := by exact_mod_cast htotpos.ne'
  have heq : (good : ℝ) / total = 1 - (bad : ℝ) / total := by
    have hgbk : (good : ℝ) + (bad : ℝ) = (total : ℝ) := by exact_mod_cast hgb
    field_simp
    linarith [hgbk]
  rw [heq]
  linarith [hbadratio]

/-- Source: AINTLIB Abelian.lean:1260, finite-group proportion argument. -/
theorem ratio_card_dvd_orderOf_tendsto_one (n : ℕ) (hn1 : 1 ≤ n) (m : ℕ → ℕ)
    (hmNeZero : ∀ k, NeZero (m k))
    (hdvd : ∀ k, 1 ≤ k → ∀ p ∈ n.primeFactors,
      p ^ (k * n.factorization p) ∣ Monoid.exponent (ZMod (m k))ˣ) :
    Filter.Tendsto (fun k : ℕ ↦ (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
      / Nat.card ((ZMod (m k))ˣ)) Filter.atTop (𝓝 1) := by
  rcases eq_or_lt_of_le hn1 with hn1' | hn2'
  · have hconst : ∀ k, (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
        / Nat.card ((ZMod (m k))ˣ) = 1 := fun k ↦ by
      have := hmNeZero k
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun x ↦ hn1'.symm ▸ one_dvd _)),
        div_self (by exact_mod_cast Nat.card_pos.ne')]
    rw [tendsto_congr hconst]
    exact tendsto_const_nhds
  · have hn2 : 2 ≤ n := hn2'
    set S : ℕ → ℝ := fun k ↦ ∑ p ∈ n.primeFactors,
      (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1) with hSdef
    have hSt : Filter.Tendsto S Filter.atTop (𝓝 0) := by
      rw [hSdef, show (0 : ℝ) = ∑ _p ∈ n.primeFactors, (0 : ℝ) by simp]
      refine tendsto_finsetSum _ (fun p hp ↦ ?_)
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact summand_tendsto p (n.factorization p) hpp.two_le
        (Nat.Prime.factorization_pos_of_dvd hpp (by omega) (Nat.dvd_of_mem_primeFactors hp))
    have hlo : Filter.Tendsto (fun k ↦ 1 - S k) Filter.atTop (𝓝 1) := by
      simpa using hSt.const_sub 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_
      (Filter.Eventually.of_forall (fun k ↦ ?_))
    · filter_upwards [Filter.eventually_ge_atTop 1] with k hk1
      have := hmNeZero k
      exact H_n_ratio_ge (ZMod (m k))ˣ n k hn2 hk1 (hdvd k hk1)
    · have := hmNeZero k
      rw [div_le_one (by exact_mod_cast (Nat.card_pos : 0 < Nat.card ((ZMod (m k))ˣ)))]
      exact_mod_cast Nat.card_le_card_of_injective
        (Subtype.val : {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} → _) Subtype.val_injective

end Cox.Chebotarev
