/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldResidueUnits
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Associated

/-!
# Janusz V.5.3 residue-unit independence

The two prime blocks have orders q^R and q^(R+1). Exact order labels force distinct primes; the
residue order bound makes all primes exceed the prescribed bound. The actual CRT map transfers the
coordinate argument to residue units.
-/

open scoped nonZeroDivisors
noncomputable section
namespace Cox.ClassFieldTheory
namespace ResidueIndependence

/-- A finite list of required exponents and an avoidance bound has a common exponent
at least two. -/
theorem exists_uniform_exponent {I : Type*} [Finite I] (e : I → ℕ) (B : ℕ) :
    ∃ R : ℕ, 2 ≤ R ∧ B ≤ R ∧ ∀ i, e i ≤ R := by
  have := Fintype.ofFinite I
  refine ⟨max 2 (max B (Finset.univ.sup e)), le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _), fun i => ?_⟩
  exact (Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The order of a nonzero residue class at a prime is strictly smaller than the prime. -/
theorem orderOf_residue_lt_prime (p : ℕ) (hp : p.Prime) (u : (ZMod p)ˣ) :
    orderOf u < p := by
  haveI := Fact.mk hp
  have h1 := ZMod.orderOf_units_dvd_card_sub_one u
  have h2 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have := Nat.le_of_dvd h2 h1
  omega

/-- The chosen large prime-power order forces the residue prime above the avoidance bound. -/
theorem prime_gt_bound_of_order (B p q r : ℕ) (hp : p.Prime) (hq : 2 ≤ q)
    (hBr : B ≤ r) (u : (ZMod p)ˣ) (hu : orderOf u = q ^ r) : B < p := by
  have h1 : r < q ^ r := Nat.lt_pow_self (by omega)
  have h2 := orderOf_residue_lt_prime p hp u
  omega

/-- Choose the source prime-order construction independently for every specified label. -/
theorem exists_prime_order_family {I : Type*} (a : ℕ) (ha : 2 ≤ a)
    (q r : I → ℕ) (hq : ∀ i, (q i).Prime) (hr : ∀ i, 2 ≤ r i) :
    ∃ p : I → ℕ, ∃ u : (i : I) → (ZMod (p i))ˣ,
      ∀ i, (p i).Prime ∧ (u i : ZMod (p i)) = a ∧ orderOf (u i) = q i ^ r i := by
  choose p hp u hu1 hu2 using fun i =>
    exists_prime_order_eq_primePower a (q i) (r i) ha (hq i) (hr i)
  exact ⟨p, u, fun i => ⟨hp i, hu1 i, hu2 i⟩⟩

/-- Distinct prime labels in the two successive exponent blocks are distinct ordered pairs. -/
theorem two_block_labels_injective {I : Type*} (q : I → ℕ)
    (hq : Function.Injective q) (R : ℕ) :
    Function.Injective (fun j : Bool × I ↦ (q j.2, if j.1 then R + 1 else R)) := by
  rintro ⟨b₁, i₁⟩ ⟨b₂, i₂⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain rfl := hq h1
  cases b₁ <;> cases b₂ <;> simp_all

/-- A fixed integer cannot have different positive prime-power orders modulo the same modulus. -/
theorem prime_family_injective_of_order_data {I : Type*} (a : ℕ) (q r p : I → ℕ)
    (hq : ∀ i, (q i).Prime) (hr : ∀ i, r i ≠ 0)
    (u : (i : I) → (ZMod (p i))ˣ) (hcast : ∀ i, (u i : ZMod (p i)) = a)
    (hord : ∀ i, orderOf (u i) = q i ^ r i)
    (hlabels : Function.Injective (fun i ↦ (q i, r i))) : Function.Injective p := by
  intro i j hij
  have key : ∀ k, orderOf ((a : ℕ) : ZMod (p k)) = q k ^ r k := fun k => by
    rw [← hcast k, orderOf_units, hord k]
  have h1 : q i ^ r i = q j ^ r j := by
    rw [← key i, ← key j]
    exact congrArg (fun n : ℕ => orderOf ((a : ℕ) : ZMod n)) hij
  obtain ⟨hqq, hrr⟩ := Nat.Prime.pow_inj' (hq i) (hq j) (hr i) (hr j) h1
  exact hlabels (Prod.ext hqq hrr)

/-- Distinct primes give the pairwise coprimality required by the finite CRT equivalence. -/
theorem pairwise_coprime_prime_family {I : Type*} (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Pairwise (fun i j ↦ (p i).Coprime (p j)) := by
  intro i j hij
  exact (Nat.coprime_primes (hp i) (hp j)).mpr (hinj.ne hij)

/-- Janusz V.5.3: the product of the two disjoint prime blocks is squarefree. -/
theorem squarefree_prod_prime_family {I : Type*} [Fintype I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j))) :
    Squarefree (∏ i, p i) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i _ j _ hij => ?_)
    (fun i _ => (hp i).prime.squarefree)
  exact Nat.coprime_iff_isRelPrime.mp (hcop hij)

/-- Every prime divisor of the selected modulus is one of its prime factors above the bound. -/
theorem prime_divisor_prod_gt {I : Type*} [Fintype I] (B : ℕ) (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hBp : ∀ i, B < p i) (l : ℕ) (hl : l.Prime)
    (hd : l ∣ ∏ i, p i) : B < l := by
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hl) _).mp hd
  rw [(Nat.prime_dvd_prime_iff_eq hl (hp i)).mp hi]
  exact hBp i

/-- A nonempty prime family produces a nontrivial modulus. -/
theorem one_lt_prod_prime_family {I : Type*} [Fintype I] [Nonempty I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) : 1 < ∏ i, p i := by
  obtain ⟨i⟩ := ‹Nonempty I›
  have hpos : 0 < ∏ j, p j := Finset.prod_pos fun j _ => (hp j).pos
  exact lt_of_lt_of_le (hp i).one_lt
    (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))

/-- The actual Chinese-remainder equivalence on residue units. -/
def crtUnitsEquiv {I : Type*} [Fintype I] (p : I → ℕ)
    (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j))) :
    (ZMod (∏ i, p i))ˣ ≃* ((i : I) → (ZMod (p i))ˣ) :=
  (Units.mapEquiv (ZMod.prodEquivPi p hcop).toMulEquiv).trans MulEquiv.piUnits

/-- The units CRT equivalence uses precisely the underlying pinned ring CRT coordinates. -/
theorem crtUnitsEquiv_apply_val {I : Type*} [Fintype I] (p : I → ℕ)
    (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j)))
    (u : (ZMod (∏ i, p i))ˣ) (i : I) :
    (crtUnitsEquiv p hcop u i : ZMod (p i)) =
      ZMod.prodEquivPi p hcop (u : ZMod (∏ i, p i)) i := by
  rfl

/-- Pulling back equal integer residues produces that same integer residue modulo the product. -/
theorem crtUnitsEquiv_symm_coe_natCast {I : Type*} [Fintype I] (p : I → ℕ)
    (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j))) (a : ℕ)
    (x : (i : I) → (ZMod (p i))ˣ) (hx : ∀ i, (x i : ZMod (p i)) = a) :
    ((crtUnitsEquiv p hcop).symm x : ZMod (∏ i, p i)) = a := by
  apply (ZMod.prodEquivPi p hcop).injective
  funext i
  rw [← crtUnitsEquiv_apply_val p hcop, MulEquiv.apply_symm_apply, hx i, map_natCast,
    Pi.natCast_apply]

/-- The prime-factorization powers suffice to test divisibility, including a zero target. -/
theorem dvd_of_prime_factorization_powers (n d : ℕ) (hn : n ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ^ (n.factorization q) ∣ d) : n ∣ d := by
  rcases eq_or_ne d 0 with rfl | hd
  · exact dvd_zero n
  · rw [← Nat.factorization_prime_le_iff_dvd hn hd]
    intro q hq
    exact (Nat.Prime.pow_dvd_iff_le_factorization hq hd).mp (h q hq)

/-- Prime-factor orders in selected coordinates divide the order of the full product element. -/
theorem dvd_orderOf_pi_of_primeFactor_components {J : Type*} {G : J → Type*}
    [∀ j, Monoid (G j)] (n : ℕ) (hn : n ≠ 0) (c : n.primeFactors → J)
    (x : (j : J) → G j)
    (h : ∀ q : n.primeFactors, (q : ℕ) ^ (n.factorization q) ∣ orderOf (x (c q))) :
    n ∣ orderOf x := by
  apply dvd_of_prime_factorization_powers n _ hn
  intro q hq
  by_cases hqn : q ∣ n
  · have hmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn⟩
    exact (h ⟨q, hmem⟩).trans (orderOf_apply_dvd_orderOf _)
  · rw [Nat.factorization_eq_zero_of_not_dvd hqn, pow_zero]
    exact one_dvd _

/-- A multiple of one element's order also annihilates any element whose order divides it. -/
theorem zpow_eq_one_of_orderOf_dvd {G H : Type*} [Group G] [Group H]
    (x : G) (y : H) (h : orderOf x ∣ orderOf y) (k : ℤ) (hy : y ^ k = 1) :
    x ^ k = 1 := by
  rw [← orderOf_dvd_iff_zpow_eq_one] at hy ⊢
  exact (Int.natCast_dvd_natCast.mpr h).trans hy

/-- Janusz V.5.3: the second prime block detects powers of the first and forces independence. -/
theorem disjoint_zpowers_masked_pi {I : Type*} {G : Bool × I → Type*}
    [∀ j, Group (G j)] (x : (j : Bool × I) → G j)
    (h : ∀ i, orderOf (x (false, i)) ∣ orderOf (x (true, i))) :
    Disjoint (Subgroup.zpowers x)
      (Subgroup.zpowers (fun j : Bool × I ↦ if j.1 then 1 else x j)) := by
  rw [Subgroup.disjoint_def]
  intro z hz1 hz2
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz1
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hz2
  have htrue : ∀ i, x (true, i) ^ k = 1 := by
    intro i
    have := congrFun hl (true, i)
    simp only [Pi.pow_apply] at this
    simpa using this.symm
  funext ⟨b, i⟩
  cases b
  · simp only [Pi.pow_apply, Pi.one_apply]
    exact zpow_eq_one_of_orderOf_dvd _ _ (h i) k (htrue i)
  · simp only [Pi.pow_apply, Pi.one_apply]
    exact htrue i

/-- Independence is preserved when the two coordinate elements are pulled back
through an equivalence. -/
theorem disjoint_zpowers_pullback {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x y : H) (h : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y)) :
    Disjoint (Subgroup.zpowers (e.symm x)) (Subgroup.zpowers (e.symm y)) := by
  have h2 := Subgroup.disjoint_map (f := e.symm.toMonoidHom) e.symm.injective h
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
  exact h2

/-- The two nonempty prime blocks and CRT give the source assertion for n at least two. -/
theorem exists_independent_residue_units_of_two_le (a n B : ℕ)
    (ha : 2 ≤ a) (hn : 2 ≤ n) :
    ∃ m : ℕ, 1 < m ∧ Squarefree m ∧
      (∀ p : ℕ, p.Prime → p ∣ m → B < p) ∧
      ∃ u v : (ZMod m)ˣ, (u : ZMod m) = a ∧ n ∣ orderOf u ∧ n ∣ orderOf v ∧
        Disjoint (Subgroup.zpowers u) (Subgroup.zpowers v) := by
  classical
  have hn0 : n ≠ 0 := by omega
  obtain ⟨R, hR2, hBR, hfR⟩ :=
    exists_uniform_exponent (fun q : n.primeFactors => n.factorization q) B
  have hqJ : ∀ j : Bool × n.primeFactors, (j.2 : ℕ).Prime :=
    fun j => Nat.prime_of_mem_primeFactors j.2.2
  have hrJ : ∀ j : Bool × n.primeFactors, 2 ≤ if j.1 then R + 1 else R := fun j => by
    split_ifs <;> omega
  obtain ⟨p, u, hpu⟩ := exists_prime_order_family a ha (fun j : Bool × n.primeFactors => (j.2 : ℕ))
    (fun j => if j.1 then R + 1 else R) hqJ hrJ
  have hp : ∀ j, (p j).Prime := fun j => (hpu j).1
  have hcast : ∀ j, (u j : ZMod (p j)) = a := fun j => (hpu j).2.1
  have hlabels : Function.Injective
      (fun j : Bool × n.primeFactors => ((j.2 : ℕ), if j.1 then R + 1 else R)) :=
    two_block_labels_injective (fun q : n.primeFactors => (q : ℕ)) Subtype.val_injective R
  have hinj : Function.Injective p :=
    prime_family_injective_of_order_data a _ _ p hqJ (fun j => by have := hrJ j; omega) u hcast
      (fun j => (hpu j).2.2) hlabels
  have hBp : ∀ j, B < p j := fun j =>
    prime_gt_bound_of_order B (p j) _ _ (hp j) (hqJ j).two_le
      (by split_ifs <;> omega) (u j) (hpu j).2.2
  have hcop := pairwise_coprime_prime_family p hp hinj
  haveI : Nonempty n.primeFactors :=
    (Nat.nonempty_primeFactors.mpr (by omega : 1 < n)).to_subtype
  have hfalse : ∀ q : n.primeFactors, orderOf (u (false, q)) = (q : ℕ) ^ R := fun q => by
    simpa using (hpu (false, q)).2.2
  have htrue : ∀ q : n.primeFactors, orderOf (u (true, q)) = (q : ℕ) ^ (R + 1) := fun q => by
    simpa using (hpu (true, q)).2.2
  refine ⟨∏ j, p j, one_lt_prod_prime_family p hp, squarefree_prod_prime_family p hp hcop,
    prime_divisor_prod_gt B p hp hBp, (crtUnitsEquiv p hcop).symm u,
    (crtUnitsEquiv p hcop).symm (fun j => if j.1 then 1 else u j),
    crtUnitsEquiv_symm_coe_natCast p hcop a u hcast, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact dvd_orderOf_pi_of_primeFactor_components n hn0 (fun q => (false, q)) u
      (fun q => by rw [hfalse q]; exact pow_dvd_pow _ (hfR q))
  · rw [MulEquiv.orderOf_eq]
    refine dvd_orderOf_pi_of_primeFactor_components n hn0 (fun q => (false, q)) _
      (fun q => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hfalse q]
    exact pow_dvd_pow _ (hfR q)
  · refine disjoint_zpowers_pullback _ u _ (disjoint_zpowers_masked_pi u fun i => ?_)
    rw [hfalse i, htrue i]
    exact pow_dvd_pow _ (Nat.le_succ R)

end ResidueIndependence

/-- Janusz V.5.3: two independent residue units of orders divisible by n,
with the squarefree modulus supported above an arbitrary bound. -/
theorem exists_independent_residue_units (a n B : ℕ) (ha : 2 ≤ a) (hn : 0 < n) :
    ∃ m : ℕ, 1 < m ∧ Squarefree m ∧
      (∀ p : ℕ, p.Prime → p ∣ m → B < p) ∧
      ∃ u v : (ZMod m)ˣ, (u : ZMod m) = a ∧ n ∣ orderOf u ∧ n ∣ orderOf v ∧
        Disjoint (Subgroup.zpowers u) (Subgroup.zpowers v) := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    obtain ⟨m, hm1, hsq, hB, u, v, hu, -, -, hdisj⟩ :=
      ResidueIndependence.exists_independent_residue_units_of_two_le a 2 B ha le_rfl
    exact ⟨m, hm1, hsq, hB, u, v, hu, one_dvd _, one_dvd _, hdisj⟩
  · exact ResidueIndependence.exists_independent_residue_units_of_two_le a n B ha hn2

end Cox.ClassFieldTheory
