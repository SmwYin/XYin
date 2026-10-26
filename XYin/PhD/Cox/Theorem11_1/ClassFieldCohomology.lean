/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldHexagon
import XYin.PhD.Cox.Theorem11_1.ClassFieldTateTransport
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # Janusz's cyclic Tate groups and Herbrand quotient

The quotient convention is H¹/H⁰_Tate. Coefficient-general quotient definitions
permit the local normal-basis lattice to use its actual valuation-ring coefficients.
-/

noncomputable section

namespace Cox.CyclicCohomology

variable {G A : Type*} [Group G] [Fintype G] [AddCommGroup A]
variable (ρ : Representation ℤ G A) (g : G)

/-- The source norm sum, reindexed by powers of the chosen cyclic generator. -/
theorem norm_eq_sum_generatorPowers (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    ρ.norm = ∑ i ∈ Finset.range (Fintype.card G), ρ (g ^ i) := by
  classical
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [Representation.norm, ← IsCyclic.image_range_card hg, Finset.sum_image,
    Nat.card_eq_fintype_card]
  intro i hi j hj hij
  exact pow_injOn_Iio_orderOf (by rw [hord]; simpa using hi) (by rw [hord]; simpa using hj) hij

/-- The weighted power sum used to telescope the norm/difference relation. -/
def weightedNorm : Module.End ℤ A :=
  ∑ i ∈ Finset.range (Fintype.card G), (i : ℤ) • ρ (g ^ i)

/-- A finite telescoping sum expresses |G| minus norm as a generator difference. -/
theorem difference_comp_weightedNorm (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    (ρ g - LinearMap.id) ∘ₗ weightedNorm ρ g =
      (Fintype.card G : ℤ) • (LinearMap.id : Module.End ℤ A) - ρ.norm := by
  have key : ∀ m : ℕ, (ρ g - LinearMap.id) ∘ₗ
      (∑ i ∈ Finset.range m, (i : ℤ) • ρ (g ^ i)) =
      (m : ℤ) • ρ (g ^ m) - ∑ i ∈ Finset.range (m + 1), ρ (g ^ i) + LinearMap.id := by
    intro m
    induction m with
    | zero => simp [Module.End.one_eq_id]
    | succ m ih =>
      rw [Finset.sum_range_succ, LinearMap.comp_add, ih, Finset.sum_range_succ (n := m + 1)]
      have hstep : (ρ g - LinearMap.id) ∘ₗ ((m : ℤ) • ρ (g ^ m)) =
          (m : ℤ) • ρ (g ^ (m + 1)) - (m : ℤ) • ρ (g ^ m) := by
        rw [LinearMap.comp_smul, LinearMap.sub_comp, LinearMap.id_comp, pow_succ', map_mul,
          Module.End.mul_eq_comp, smul_sub]
      rw [hstep]
      push_cast
      module
  rw [norm_eq_sum_generatorPowers ρ g hg, weightedNorm, key, Finset.sum_range_succ,
    pow_card_eq_one, map_one, Module.End.one_eq_id]
  abel

/-- Group order kills the invariant/norm Tate group. -/
theorem card_smul_tateZero (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (x : tateZero ρ g) : Fintype.card G • x = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hfix : ρ g (a : A) = a := sub_eq_zero.mp (LinearMap.mem_ker.mp a.2)
  have hinv : (a : A) ∈ ρ.invariants :=
    (ρ.mem_invariants_iff_of_forall_mem_zpowers g hg (a : A)).mpr hfix
  refine ⟨a, ?_⟩
  change ρ.norm (a : A) = ((Fintype.card G • a : LinearMap.ker (ρ g - LinearMap.id)) : A)
  rw [Representation.norm, LinearMap.sum_apply, Finset.sum_congr rfl fun σ _ => hinv σ,
    Finset.sum_const, Finset.card_univ]
  rfl

/-- Group order kills the norm-zero/difference Tate group. -/
theorem card_smul_tateOne (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (x : tateOne ρ g) : Fintype.card G • x = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨weightedNorm ρ g a, ?_⟩
  have h := LinearMap.congr_fun (difference_comp_weightedNorm ρ g hg) (a : A)
  rw [LinearMap.comp_apply] at h
  rw [h]
  change ((Fintype.card G : ℤ) • (LinearMap.id : Module.End ℤ A) - ρ.norm) (a : A) =
    ((Fintype.card G • a : LinearMap.ker ρ.norm) : A)
  rw [LinearMap.sub_apply, LinearMap.mem_ker.mp a.2, sub_zero, LinearMap.smul_apply,
    LinearMap.id_apply, natCast_zsmul]
  rfl

/-- A finitely generated abelian group annihilated by a positive integer is finite. -/
theorem finite_of_moduleFinite_annihilated {M : Type*} [AddCommGroup M]
    [Module.Finite ℤ M] (n : ℕ) (hn : 0 < n) (h : ∀ x : M, n • x = 0) :
    Finite M := by
  apply Module.finite_of_fg_torsion
  intro y
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
  change (n : ℤ) • y = 0
  rw [natCast_zsmul]
  exact h y

/-- Finite cyclic cohomology of a finitely generated abelian group is finite. -/
theorem finiteHerbrand_of_moduleFinite [Module.Finite ℤ A]
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) : FiniteHerbrand ρ g := by
  haveI : IsNoetherian ℤ A := inferInstance
  haveI : Module.Finite ℤ (tateZero ρ g) := Module.Finite.quotient ℤ _
  haveI : Module.Finite ℤ (tateOne ρ g) := Module.Finite.quotient ℤ _
  exact ⟨finite_of_moduleFinite_annihilated (Fintype.card G) Fintype.card_pos
      (card_smul_tateZero ρ g hg),
    finite_of_moduleFinite_annihilated (Fintype.card G) Fintype.card_pos
      (card_smul_tateOne ρ g hg)⟩

/-- A finite module has finite Tate groups. -/
theorem finiteHerbrand_of_finite [Finite A] : FiniteHerbrand ρ g :=
  ⟨Quotient.finite _, Quotient.finite _⟩

/-- Janusz V.1.3: a finite module has Herbrand quotient one. -/
theorem herbrandQuotient_eq_one_of_finite [Finite A] : herbrandQuotient ρ g = 1 := by
  have hlag : ∀ K P : Submodule ℤ A, P ≤ K →
      Nat.card K = Nat.card (K ⧸ P.comap K.subtype) * Nat.card P := by
    intro K P hPK
    rw [← Nat.card_congr (Submodule.comapSubtypeEquivOfLe hPK).toEquiv]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (P.comap K.subtype).toAddSubgroup
  have hrn : ∀ f : A →ₗ[ℤ] A,
      Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
    intro f
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup,
      mul_comm]
    congr 1
    exact Nat.card_congr f.quotKerEquivRange.toEquiv
  have h0 := hlag _ _ (range_norm_le_ker_difference ρ g)
  have h1 := hlag _ _ (range_difference_le_ker_norm ρ g)
  have hD := hrn (ρ g - LinearMap.id)
  have hN := hrn ρ.norm
  have hrN : 0 < Nat.card (LinearMap.range ρ.norm) := Nat.card_pos
  have hrD : 0 < Nat.card (LinearMap.range (ρ g - LinearMap.id)) := Nat.card_pos
  have heq : Nat.card (tateZero ρ g) = Nat.card (tateOne ρ g) := by
    have h := hD.symm.trans hN
    rw [h0, h1] at h
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hrN hrD)
    linear_combination h
  haveI := (finiteHerbrand_of_finite ρ g).2
  unfold herbrandQuotient
  rw [heq, div_self]
  exact_mod_cast (Nat.card_pos (α := tateOne ρ g)).ne'

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
/-- Janusz V.1.3: the exact cyclic hexagon gives multiplicativity of the quotient. -/
theorem herbrandQuotient_mul {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (τ : Representation ℤ G B) (υ : Representation ℤ G C)
    (f : ρ.IntertwiningMap τ) (h : τ.IntertwiningMap υ)
    (hf : Function.Injective f) (hh : Function.Surjective h)
    (hexact : LinearMap.range f.toLinearMap = LinearMap.ker h.toLinearMap)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hA : FiniteHerbrand ρ g) (hB : FiniteHerbrand τ g) (hC : FiniteHerbrand υ g) :
    herbrandQuotient τ g = herbrandQuotient ρ g * herbrandQuotient υ g := by
  haveI := hA.1
  haveI := hA.2
  haveI := hB.1
  haveI := hB.2
  haveI := hC.1
  haveI := hC.2
  have hprod := tate_card_product ρ τ υ g f h hf hh hexact hA hB hC
  have h1 : (0 : ℚ) < Nat.card (tateZero ρ g) := by exact_mod_cast Nat.card_pos
  have h2 : (0 : ℚ) < Nat.card (tateZero τ g) := by exact_mod_cast Nat.card_pos
  have h3 : (0 : ℚ) < Nat.card (tateZero υ g) := by exact_mod_cast Nat.card_pos
  unfold herbrandQuotient
  rw [div_mul_div_comm, div_eq_div_iff h2.ne' (mul_pos h1 h3).ne']
  have hq := congrArg (Nat.cast : ℕ → ℚ) hprod
  push_cast at hq
  linear_combination hq

-- The unused hypothesis is kept: the planned signature includes it.
set_option linter.unusedVariables false in
/-- The exact cyclic hexagon transfers Tate finiteness in either direction across
a stable submodule of finite index. -/
theorem finiteHerbrand_iff_subrepresentation (W : Submodule ℤ A)
    (hW : ∀ x, W ≤ W.comap (ρ x)) [Finite (A ⧸ W)]
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    FiniteHerbrand ρ g ↔ FiniteHerbrand (ρ.subrepresentation W hW) g := by
  have hQ := finiteHerbrand_of_finite (ρ.quotient W hW) g
  constructor
  · intro hA
    exact finiteHerbrand_of_middle_last (ρ.subrepresentation W hW) ρ (ρ.quotient W hW) g
      (submoduleIntertwining ρ W hW) (quotientIntertwining ρ W hW)
      (submoduleIntertwining_injective ρ W hW) (quotientIntertwining_surjective ρ W hW)
      (submodule_sequence_exact ρ W hW) hA hQ
  · intro hS
    exact finiteHerbrand_of_first_last (ρ.subrepresentation W hW) ρ (ρ.quotient W hW) g
      (submoduleIntertwining ρ W hW) (quotientIntertwining ρ W hW)
      (submoduleIntertwining_injective ρ W hW) (quotientIntertwining_surjective ρ W hW)
      (submodule_sequence_exact ρ W hW) hS hQ

/-- Janusz V.1.4: a stable finite-index submodule has the same Herbrand quotient. -/
theorem herbrandQuotient_subrepresentation (W : Submodule ℤ A)
    (hW : ∀ x, W ≤ W.comap (ρ x)) [Finite (A ⧸ W)]
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hA : FiniteHerbrand ρ g) (hS : FiniteHerbrand (ρ.subrepresentation W hW) g) :
    herbrandQuotient (ρ.subrepresentation W hW) g = herbrandQuotient ρ g := by
  have hQ := finiteHerbrand_of_finite (ρ.quotient W hW) g
  have h := herbrandQuotient_mul (ρ.subrepresentation W hW) g ρ (ρ.quotient W hW)
    (submoduleIntertwining ρ W hW) (quotientIntertwining ρ W hW)
    (submoduleIntertwining_injective ρ W hW) (quotientIntertwining_surjective ρ W hW)
    (submodule_sequence_exact ρ W hW) hg hS hA hQ
  rw [herbrandQuotient_eq_one_of_finite (ρ.quotient W hW) g, mul_one] at h
  exact h.symm

/-- Sum of the coefficients of an integral finite-support vector. -/
def coefficientSum (X : Type*) : (X →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ : X => (1 : ℤ))

omit [Fintype G] in
/-- A cyclic transitive permutation invariant has constant coordinates. -/
theorem permutation_invariant_iff_constant (X : Type*) [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) (hg : ∀ y : G, y ∈ Subgroup.zpowers g)
    (v : X →₀ ℤ) :
    ((Representation.ofMulAction ℤ G X) g) v = v ↔ ∃ c : ℤ, ∀ y, v y = c := by
  constructor
  · intro hv
    have hi : v ∈ (Representation.ofMulAction ℤ G X).invariants :=
      ((Representation.ofMulAction ℤ G X).mem_invariants_iff_of_forall_mem_zpowers
        g hg v).2 hv
    refine ⟨v x, ?_⟩
    intro y
    obtain ⟨γ, rfl⟩ := MulAction.exists_smul_eq G x y
    have h := congrArg (fun w : X →₀ ℤ ↦ w x) (hi γ⁻¹)
    simpa only [Representation.ofMulAction_apply, inv_inv] using h
  · rintro ⟨c, hc⟩
    ext y
    simp only [Representation.ofMulAction_apply, hc]

/-- The norm in a transitive permutation module is stabilizer order times coefficient sum. -/
theorem permutation_norm_apply (X : Type*) [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) (v : X →₀ ℤ) (y : X) :
    (Representation.ofMulAction ℤ G X).norm v y =
      (Nat.card (MulAction.stabilizer G x) : ℤ) * coefficientSum X v := by
  classical
  have hbase (a : ℤ) :
      (Representation.ofMulAction ℤ G X).norm (Finsupp.single x a) y =
        (Nat.card (MulAction.stabilizer G x) : ℤ) * a := by
    obtain ⟨δ, hδ⟩ := MulAction.exists_smul_eq G x y
    let e : MulAction.stabilizer G x ≃ {γ : G // γ • x = y} :=
      { toFun := fun s ↦ ⟨δ * s, by
          rw [mul_smul, show (s : G) • x = x from s.property]
          exact hδ⟩
        invFun := fun γ ↦ ⟨δ⁻¹ * γ, by
          change (δ⁻¹ * (γ : G)) • x = x
          rw [mul_smul, γ.property, ← hδ, inv_smul_smul]⟩
        left_inv := fun s ↦ Subtype.ext (by simp)
        right_inv := fun γ ↦ Subtype.ext (by simp) }
    have hcard := Nat.card_congr e
    calc
      (Representation.ofMulAction ℤ G X).norm (Finsupp.single x a) y =
          ∑ γ : G, if γ • x = y then a else 0 := by
        simp only [Representation.norm, LinearMap.sum_apply, Finsupp.finsetSum_apply,
          Representation.ofMulAction_single, Finsupp.single_apply]
      _ = ∑ γ ∈ Finset.univ.filter (fun γ : G ↦ γ • x = y), a := by
        rw [Finset.sum_filter]
      _ = ∑ _γ : {γ : G // γ • x = y}, a :=
        Finset.sum_subtype _ (by simp) (fun _ ↦ a)
      _ = (Nat.card (MulAction.stabilizer G x) : ℤ) * a := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card, ← hcard]
  have hsingle (z : X) (a : ℤ) :
      (Representation.ofMulAction ℤ G X).norm (Finsupp.single z a) y =
        (Nat.card (MulAction.stabilizer G x) : ℤ) * a := by
    obtain ⟨γ, rfl⟩ := MulAction.exists_smul_eq G x z
    rw [← Representation.ofMulAction_single (k := ℤ) γ x a,
      Representation.norm_self_apply]
    exact hbase a
  calc
    (Representation.ofMulAction ℤ G X).norm v y =
        (Representation.ofMulAction ℤ G X).norm
          (v.sum fun z a ↦ Finsupp.single z a) y := by rw [Finsupp.sum_single]
    _ = v.sum (fun z a ↦
        (Representation.ofMulAction ℤ G X).norm (Finsupp.single z a) y) := by
      simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
    _ = v.sum (fun _ a ↦ (Nat.card (MulAction.stabilizer G x) : ℤ) * a) := by
      simp only [hsingle]
    _ = (Nat.card (MulAction.stabilizer G x) : ℤ) * coefficientSum X v := by
      simp only [coefficientSum, Finsupp.linearCombination_apply, smul_eq_mul,
        mul_one, Finsupp.sum, Finset.mul_sum]

omit [Fintype G] in
/-- Orbitwise cumulative sums identify generator differences with coefficient-sum zero. -/
theorem permutation_range_difference (X : Type*) [Finite X] [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) (hg : ∀ y : G, y ∈ Subgroup.zpowers g) :
    LinearMap.range ((Representation.ofMulAction ℤ G X) g - LinearMap.id) =
      LinearMap.ker (coefficientSum X) := by
  classical
  have hsum (w : X →₀ ℤ) :
      coefficientSum X ((Representation.ofMulAction ℤ G X) g w) = coefficientSum X w := by
    simp only [coefficientSum, Finsupp.linearCombination_apply,
      Representation.ofMulAction_def, Finsupp.lmapDomain_apply]
    exact Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
      (fun _ _ _ ↦ by simp)
  have hsingle (y : X) (a : ℤ) :
      Finsupp.single y a - Finsupp.single x a ∈
        LinearMap.range ((Representation.ofMulAction ℤ G X) g - LinearMap.id) := by
    obtain ⟨γ, hγ⟩ := MulAction.exists_smul_eq G x y
    obtain ⟨k, rfl⟩ := hg γ
    have hcycle : (MulAction.toPermHom G X g).SameCycle x y := by
      refine ⟨k, ?_⟩
      rw [← map_zpow]
      change (g ^ k) • x = y
      exact hγ
    obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
    rw [← map_pow] at hn
    change (g ^ n) • x = y at hn
    cases n with
    | zero =>
      have hxy : x = y := by simpa only [pow_zero, one_smul] using hn
      exact ⟨0, by simp only [map_zero, ← hxy, sub_self]⟩
    | succ n =>
      refine ⟨Fin.partialSum
        (fun j : Fin (n + 1) ↦
          (Representation.ofMulAction ℤ G X) (g ^ (j : ℕ)) (Finsupp.single x a))
        (Fin.last _), ?_⟩
      simpa only [Representation.ofMulAction_single, hn] using
        (Representation.ofMulAction ℤ G X).apply_sub_id_partialSum_eq
          n g (Finsupp.single x a)
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    change coefficientSum X
      ((Representation.ofMulAction ℤ G X) g w - w) = 0
    simp only [map_sub, hsum, sub_self]
  · intro v hv
    have hvsum : v.sum (fun _ a ↦ a) = 0 := by
      simpa only [coefficientSum, Finsupp.linearCombination_apply, smul_eq_mul, mul_one]
        using (show coefficientSum X v = 0 from hv)
    have hreconstruct :
        v.sum (fun y a ↦ Finsupp.single y a - Finsupp.single x a) = v := by
      rw [Finsupp.sum_sub, Finsupp.sum_single,
        ← Finsupp.single_sum v (fun _ a ↦ a) x, hvsum, Finsupp.single_zero, sub_zero]
    rw [← hreconstruct]
    exact Submodule.finsuppSum_mem ℤ
      (LinearMap.range ((Representation.ofMulAction ℤ G X) g - LinearMap.id)) v
      (fun y a ↦ Finsupp.single y a - Finsupp.single x a)
      (fun y _ ↦ hsingle y (v y))

/-- The norm kernel has coefficient sum zero because stabilizer order is nonzero in ℤ. -/
theorem permutation_ker_norm (X : Type*) [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) :
    LinearMap.ker (Representation.ofMulAction ℤ G X).norm =
      LinearMap.ker (coefficientSum X) := by
  have hm : (Nat.card (MulAction.stabilizer G x) : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  ext v
  change (Representation.ofMulAction ℤ G X).norm v = 0 ↔ coefficientSum X v = 0
  constructor
  · intro hv
    have h := congrArg (fun w : X →₀ ℤ ↦ w x) hv
    change (Representation.ofMulAction ℤ G X).norm v x = 0 at h
    rw [permutation_norm_apply X x] at h
    exact (mul_eq_zero.mp h).resolve_left hm
  · intro hv
    ext y
    rw [permutation_norm_apply X x, hv, mul_zero]
    rfl

/-- The first Tate group of a transitive integral permutation module is trivial. -/
theorem tateOne_permutation_subsingleton (X : Type*) [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) (hg : ∀ y : G, y ∈ Subgroup.zpowers g) :
    Subsingleton (tateOne (Representation.ofMulAction ℤ G X) g) := by
  letI : Finite X :=
    Finite.of_surjective (fun γ : G ↦ γ • x) (MulAction.surjective_smul G x)
  have h := (permutation_range_difference g X x hg).trans
    (permutation_ker_norm (G := G) X x).symm
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro v _
  change (v : X →₀ ℤ) ∈ LinearMap.range
    ((Representation.ofMulAction ℤ G X) g - LinearMap.id)
  rw [h]
  exact v.property

/-- Invariants modulo norms in a transitive integral permutation module are ℤ/eℤ. -/
theorem tateZero_permutation_equiv (X : Type*) [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) (hg : ∀ y : G, y ∈ Subgroup.zpowers g) :
    Nonempty (tateZero (Representation.ofMulAction ℤ G X) g ≃+
      ZMod (Nat.card (MulAction.stabilizer G x))) := by
  classical
  letI : Finite X :=
    Finite.of_surjective (fun γ : G ↦ γ • x) (MulAction.surjective_smul G x)
  let m := Nat.card (MulAction.stabilizer G x)
  let K := LinearMap.ker ((Representation.ofMulAction ℤ G X) g - LinearMap.id)
  let P := (LinearMap.range (Representation.ofMulAction ℤ G X).norm).comap K.subtype
  let f : K →+ ZMod m :=
    { toFun := fun w ↦ ((w : X →₀ ℤ) x : ZMod m)
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective z
    let w : X →₀ ℤ := Finsupp.equivFunOnFinite.symm (fun _ : X ↦ a)
    have hw : (Representation.ofMulAction ℤ G X) g w = w :=
      (permutation_invariant_iff_constant g X x hg w).2 ⟨a, fun _ ↦ rfl⟩
    have hwK : w ∈ K := by
      change (Representation.ofMulAction ℤ G X) g w - w = 0
      exact sub_eq_zero.mpr hw
    exact ⟨⟨w, hwK⟩, ha⟩
  have hP : P.toAddSubgroup = f.ker := by
    ext w
    change ((w : X →₀ ℤ) ∈ LinearMap.range
      (Representation.ofMulAction ℤ G X).norm) ↔ ((w : X →₀ ℤ) x : ZMod m) = 0
    constructor
    · rintro ⟨v, hv⟩
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).2
      refine ⟨coefficientSum X v, ?_⟩
      rw [← hv, permutation_norm_apply X x]
    · intro hw
      obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1 hw
      have hwfix : (Representation.ofMulAction ℤ G X) g (w : X →₀ ℤ) = w := by
        apply sub_eq_zero.mp
        exact w.property
      obtain ⟨c, hc⟩ := (permutation_invariant_iff_constant g X x hg (w : X →₀ ℤ)).1 hwfix
      refine ⟨Finsupp.single x a, ?_⟩
      ext y
      rw [permutation_norm_apply X x]
      simp only [coefficientSum, Finsupp.linearCombination_single, smul_eq_mul, mul_one]
      exact ha.symm.trans ((hc x).trans (hc y).symm)
  change Nonempty (K ⧸ P.toAddSubgroup ≃+ ZMod m)
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hP).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf)⟩

/-- Janusz V.1.5: a transitive integral permutation module contributes the reciprocal
of its point stabilizer order. -/
theorem herbrandQuotient_permutation (X : Type*) [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) (hg : ∀ y : G, y ∈ Subgroup.zpowers g) :
    herbrandQuotient (Representation.ofMulAction ℤ G X) g =
      (Nat.card (MulAction.stabilizer G x) : ℚ)⁻¹ := by
  letI := tateOne_permutation_subsingleton g X x hg
  obtain ⟨e⟩ := tateZero_permutation_equiv g X x hg
  have h1 : Nat.card (tateOne (Representation.ofMulAction ℤ G X) g) = 1 :=
    Nat.card_of_subsingleton 0
  have h0 : Nat.card (tateZero (Representation.ofMulAction ℤ G X) g) =
      Nat.card (MulAction.stabilizer G x) :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)
  simp only [herbrandQuotient, h1, h0, Nat.cast_one, one_div]

/-- The regular representation has trivial invariant/norm quotient over every
commutative coefficient ring, including a local valuation ring. -/
theorem tateZero_regular_coeff_subsingleton (R : Type*) [CommRing R]
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Subsingleton (tateZero (Representation.ofMulAction R G G) g) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  rintro ⟨x, hx⟩ -
  change x ∈ LinearMap.range (Representation.ofMulAction R G G).norm
  have hfix : (Representation.ofMulAction R G G) g x = x :=
    sub_eq_zero.mp (LinearMap.mem_ker.mp hx)
  have hconst := Representation.apply_eq_of_leftRegular_eq_of_generator (k := R) g hg x hfix
  refine ⟨Finsupp.single 1 (x g), ?_⟩
  ext γ
  simp [Representation.norm, Finsupp.finsetSum_apply, Representation.ofMulAction_single,
    hconst γ]

/-- Norm-zero vectors are differences in the regular representation over an arbitrary
commutative coefficient ring. -/
theorem tateOne_regular_coeff_subsingleton (R : Type*) [CommRing R]
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Subsingleton (tateOne (Representation.ofMulAction R G G) g) := by
  have h : LinearMap.range ((Representation.ofMulAction R G G) g - LinearMap.id) =
      LinearMap.ker (Representation.ofMulAction R G G).norm := by
    rw [← Representation.FiniteCyclicGroup.coinvariantsKer_eq_range _ g hg,
      Representation.FiniteCyclicGroup.coinvariantsKer_leftRegular_eq_ker,
      Representation.ker_leftRegular_norm_eq]
  apply Submodule.Quotient.subsingleton_iff.mpr
  rw [h, Submodule.comap_subtype_self]

/-- The regular coefficient module has finite Tate groups even when the coefficient
ring has an infinite additive group. -/
theorem finiteHerbrand_regular_coeff (R : Type*) [CommRing R]
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    FiniteHerbrand (Representation.ofMulAction R G G) g := by
  haveI := tateZero_regular_coeff_subsingleton g R hg
  haveI := tateOne_regular_coeff_subsingleton g R hg
  exact ⟨Finite.of_subsingleton, Finite.of_subsingleton⟩

/-- Janusz V.3.9 uses the regular action with additive base-valuation-ring coefficients. -/
theorem herbrandQuotient_regular_coeff (R : Type*) [CommRing R]
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    herbrandQuotient (Representation.ofMulAction R G G) g = 1 := by
  haveI := tateZero_regular_coeff_subsingleton g R hg
  haveI := tateOne_regular_coeff_subsingleton g R hg
  simp only [herbrandQuotient, Nat.card_of_subsingleton (0 : tateZero _ g),
    Nat.card_of_subsingleton (0 : tateOne _ g), Nat.cast_one, div_one]

/-- The regular integral permutation representation has trivial Tate cohomology. -/
theorem tateZero_regular_subsingleton (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Subsingleton (tateZero (Representation.ofMulAction ℤ G G) g) := by
  exact tateZero_regular_coeff_subsingleton g ℤ hg

/-- The norm-zero vectors in a regular permutation representation are differences. -/
theorem tateOne_regular_subsingleton (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Subsingleton (tateOne (Representation.ofMulAction ℤ G G) g) := by
  exact tateOne_regular_coeff_subsingleton g ℤ hg

section Transport

variable {R S B : Type*} [CommRing R] [CommRing S] [AddCommGroup B]
variable [Module R A] [Module S B]
variable (ρ : Representation R G A) (τ : Representation S G B) (e : A ≃+ B)

/-- Equivariant additive equivalences transport the invariant/norm quotient,
independently of the scalar rings used to present the two modules. -/
theorem tateZero_equiv (h : ∀ γ x, e (ρ γ x) = τ γ (e x)) :
    Nonempty (tateZero ρ g ≃+ tateZero τ g) := by
  exact kernelRangeQuotient_equiv _ _ _ _ e (addEquiv_difference ρ τ e h g)
    (addEquiv_norm ρ τ e h)

/-- Equivariant additive equivalences also transport the norm-one/difference quotient. -/
theorem tateOne_equiv (h : ∀ γ x, e (ρ γ x) = τ γ (e x)) :
    Nonempty (tateOne ρ g ≃+ tateOne τ g) := by
  exact kernelRangeQuotient_equiv _ _ _ _ e (addEquiv_norm ρ τ e h)
    (addEquiv_difference ρ τ e h g)

/-- Finiteness of the Tate groups is invariant under an equivariant additive equivalence. -/
theorem finiteHerbrand_iff (h : ∀ γ x, e (ρ γ x) = τ γ (e x)) :
    FiniteHerbrand ρ g ↔ FiniteHerbrand τ g := by
  obtain ⟨e0⟩ := tateZero_equiv g ρ τ e h
  obtain ⟨e1⟩ := tateOne_equiv g ρ τ e h
  exact ⟨fun ⟨h0, h1⟩ => ⟨Finite.of_equiv _ e0.toEquiv, Finite.of_equiv _ e1.toEquiv⟩,
    fun ⟨h0, h1⟩ => ⟨Finite.of_equiv _ e0.symm.toEquiv, Finite.of_equiv _ e1.symm.toEquiv⟩⟩

/-- The Herbrand quotient only depends on the underlying group action,
not on a particular coefficient-ring presentation. -/
theorem herbrandQuotient_congr (h : ∀ γ x, e (ρ γ x) = τ γ (e x)) :
    herbrandQuotient ρ g = herbrandQuotient τ g := by
  obtain ⟨e0⟩ := tateZero_equiv g ρ τ e h
  obtain ⟨e1⟩ := tateOne_equiv g ρ τ e h
  simp only [herbrandQuotient, Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv]

end Transport

section LibraryComparison

variable {G A : Type} [CommGroup G] [Fintype G] [AddCommGroup A]
variable (ρ : Representation ℤ G A) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)

include hg in
/-- Positive even cyclic cohomology, not ordinary degree zero, is the Tate denominator. -/
theorem tateZero_equiv_groupCohomology_two :
    Nonempty (tateZero ρ g ≃+ groupCohomology (Rep.of ρ) 2) := by
  let π := Rep.FiniteCyclicGroup.groupCohomologyπEven (Rep.of ρ) g hg 2 even_two
  have hsurj : Function.Surjective π.hom :=
    (ModuleCat.epi_iff_surjective π).1 inferInstance
  have hker : LinearMap.ker π.hom =
      (LinearMap.range ρ.norm).comap (LinearMap.ker (ρ g - LinearMap.id)).subtype := by
    ext x
    exact Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff (Rep.of ρ) g hg 2 even_two x
  exact ⟨((Submodule.quotEquivOfEq _ _ hker.symm).trans
    (LinearMap.quotKerEquivOfSurjective π.hom hsurj)).toAddEquiv⟩

include hg in
/-- The numerator agrees with the existing first cyclic cohomology group. -/
theorem tateOne_equiv_groupCohomology_one :
    Nonempty (tateOne ρ g ≃+ groupCohomology (Rep.of ρ) 1) := by
  let π := Rep.FiniteCyclicGroup.groupCohomologyπOdd (Rep.of ρ) g hg 1 odd_one
  have hsurj : Function.Surjective π.hom :=
    (ModuleCat.epi_iff_surjective π).1 inferInstance
  have hker : LinearMap.ker π.hom =
      (LinearMap.range (ρ g - LinearMap.id)).comap (LinearMap.ker ρ.norm).subtype := by
    ext x
    exact Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff (Rep.of ρ) g hg 1 odd_one x
  exact ⟨((Submodule.quotEquivOfEq _ _ hker.symm).trans
    (LinearMap.quotKerEquivOfSurjective π.hom hsurj)).toAddEquiv⟩

end LibraryComparison
end Cox.CyclicCohomology
