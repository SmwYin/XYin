/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ChebotarevIdealCounting
import XYin.PhD.Cox.Theorem11_1.ChebotarevDensity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# Source-local cyclotomic analytic prerequisites

Source: AINTLIB revision `953409d221e42e247e32db31def5444fe60f3f87`; not an imported dependency.
-/
noncomputable section
open Filter NumberField Topology Set MeasureTheory
namespace Cox.Chebotarev
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

open scoped Classical in
/-- Planning source: ZetaProduct.lean:80; source-local planning contract. -/
def galoisCharacterOnIdeal (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) : ℂ :=
  ∏ 𝔭 ∈ (UniqueFactorizationMonoid.normalizedFactors 𝔞).toFinset,
    (if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0)
      ^ (UniqueFactorizationMonoid.normalizedFactors 𝔞).count 𝔭

open scoped Classical in
/-- Planning source: ZetaProduct.lean:91; source-local planning contract. -/
theorem galoisCharacterOnIdeal_eq_map_prod
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) :
    galoisCharacterOnIdeal K L χ 𝔞 =
      ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
        (fun 𝔭 ↦ if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0)).prod := by
  rw [galoisCharacterOnIdeal, Finset.prod_multiset_map_count]

open scoped Classical in
/-- Planning source: ZetaProduct.lean:104; source-local planning contract. -/
theorem galoisCharacterOnIdeal_apply_prime
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    galoisCharacterOnIdeal K L χ 𝔭 =
      if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0 := by
  rw [galoisCharacterOnIdeal_eq_map_prod, UniqueFactorizationMonoid.normalizedFactors_irreducible
    (Ideal.prime_of_isPrime h𝔭 ‹_›).irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

/-- Planning source: ZetaProduct.lean:115; source-local planning contract. -/
theorem galoisCharacterOnIdeal_mul
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) :
    galoisCharacterOnIdeal K L χ (𝔞 * 𝔟) =
      galoisCharacterOnIdeal K L χ 𝔞 * galoisCharacterOnIdeal K L χ 𝔟 := by
  rw [galoisCharacterOnIdeal_eq_map_prod, galoisCharacterOnIdeal_eq_map_prod,
    galoisCharacterOnIdeal_eq_map_prod, UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟,
    Multiset.map_add, Multiset.prod_add]

/-- Planning source: ZetaProduct.lean:125; source-local planning contract. -/
theorem galoisCharacterOnIdeal_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) :
    galoisCharacterOnIdeal K L χ ⊤ = 1 := by
  rw [galoisCharacterOnIdeal_eq_map_prod, ← Ideal.one_eq_top,
    UniqueFactorizationMonoid.normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]

/-- Planning source: ZetaProduct.lean:161; source-local planning contract. -/
theorem norm_galoisCharacter_out
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (c : ConjClasses Gal(L/K)) :
    ‖(χ c.out : ℂ)‖ = 1 :=
  (((Units.coeHom ℂ).comp χ).isOfFinOrder (isOfFinOrder_of_finite c.out)).norm_eq_one

/-- Planning source: ZetaProduct.lean:170; source-local planning contract. -/
theorem norm_galoisCharacterOnIdeal_le_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) :
    ‖galoisCharacterOnIdeal K L χ 𝔞‖ ≤ 1 := by
  rw [galoisCharacterOnIdeal, norm_prod]
  refine Finset.prod_le_one (fun i _ ↦ norm_nonneg _) (fun 𝔭 _ ↦ ?_)
  rw [norm_pow]
  by_cases h : UnramifiedIn K L 𝔭
  · rw [if_pos h, norm_galoisCharacter_out, one_pow]
  · rw [if_neg h, norm_zero]
    exact zero_pow_le_one _

/-- Planning source: ZetaProduct.lean:193; source-local planning contract. -/
theorem exists_artinLSeries_eulerProduct_abelian
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [_hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L) :
    ∀ s : ℂ, 1 < s.re →
      (∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
        = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
            galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) := by
  intro s hs
  set w : Ideal (𝓞 K) → ℂ := galoisCharacterOnIdeal K L χ with hw
  rw [← weighted_eulerProduct_eq_tsum K (s := s) hs w (galoisCharacterOnIdeal_one K L χ)
    (fun {𝔞 𝔟} h𝔞 h𝔟 ↦ galoisCharacterOnIdeal_mul K L χ h𝔞 h𝔟)
    (norm_galoisCharacterOnIdeal_le_one K L χ)]
  set g : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} →
      {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := fun 𝔭 ↦ ⟨𝔭.1, 𝔭.2.1, 𝔭.2.2.ne_bot⟩ with hg
  set f : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℂ :=
    fun 𝔭 ↦ (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ with hf
  have hg_inj : Function.Injective g := fun _ _ hab ↦
    Subtype.ext (congrArg (fun x : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ x.1) hab)
  have hsupp : Function.mulSupport f ⊆ Set.range g := by
    intro 𝔭 hmem
    simp only [Function.mem_mulSupport, hf] at hmem
    haveI := 𝔭.2.1
    have hunr : UnramifiedIn K L 𝔭.1 := by
      by_contra hnr
      apply hmem
      rw [hw, galoisCharacterOnIdeal_apply_prime K L χ 𝔭.1 𝔭.2.2, if_neg hnr, zero_mul, sub_zero,
        inv_one]
    exact ⟨⟨𝔭.1, 𝔭.2.1, hunr⟩, rfl⟩
  rw [← hg_inj.tprod_eq hsupp]
  refine tprod_congr fun 𝔭 ↦ ?_
  simp only [hf, hg, hw]
  haveI := 𝔭.2.1
  rw [galoisCharacterOnIdeal_apply_prime K L χ 𝔭.1 𝔭.2.2.ne_bot, if_pos 𝔭.2.2]

/-- Planning source: ZetaProduct.lean:1787; source-local planning contract. -/
theorem exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) :
    ∃ κ C' : ℝ, ∀ g : Gal(L/K), ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g} : ℝ)
          - κ * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot K L (Set.mem_singleton m) (NeZero.ne m)
  rcases Nat.lt_or_ge (Module.finrank ℚ K) 2 with hlt | hge
  · have hd1 : Module.finrank ℚ K = 1 := le_antisymm (by omega) Module.finrank_pos
    exact card_fibre_bound_eq_one K L m hζ hd1 hm
  · exact card_fibre_bound_two_le K L m hζ hge

/-- Planning source: ZetaProduct.lean:511; source-local planning contract. -/
theorem unramifiedIn_of_mem_normalizedFactors_of_galoisCharacterOnIdeal_ne_zero
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) {𝔞 𝔭 : Ideal (𝓞 K)} (h : galoisCharacterOnIdeal K L χ 𝔞 ≠ 0)
    (h𝔭 : 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞) : UnramifiedIn K L 𝔭 := by
  by_contra hnr
  refine h ?_
  rw [galoisCharacterOnIdeal_eq_map_prod]
  exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨𝔭, h𝔭, if_neg hnr⟩)

/-- Planning source: ZetaProduct.lean:491; source-local planning contract. -/
theorem galoisCharacterOnIdeal_eq_char_frobeniusIdeal
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) {𝔞 : Ideal (𝓞 K)}
    (hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) :
    galoisCharacterOnIdeal K L χ 𝔞 = (χ (frobeniusIdeal K L 𝔞) : ℂ) := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  have hfrob : (χ (frobeniusIdeal K L 𝔞) : ℂ) =
      ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
        (fun 𝔭 ↦ (χ (frobeniusClass K L 𝔭).out : ℂ))).prod := by
    rw [frobeniusIdeal, map_multiset_prod, ← Units.coeHom_apply, map_multiset_prod,
      Multiset.map_map, Multiset.map_map]
    rfl
  rw [galoisCharacterOnIdeal_eq_map_prod, hfrob]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun 𝔭 h𝔭 ↦ ?_)
  rw [if_pos (hU 𝔭 h𝔭)]

/-- Planning source: ZetaProduct.lean:529; source-local planning contract. -/
theorem card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (ζ : ℂ) (hζ : ζ ≠ 0) (N : ℕ) :
    Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ}
        = Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
              (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun 𝔞 ↦ and_congr_right fun h𝔞 ↦
    and_congr_right fun _hN ↦ ?_)
  constructor
  · intro hval
    have hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭 :=
      fun 𝔭 ↦ unramifiedIn_of_mem_normalizedFactors_of_galoisCharacterOnIdeal_ne_zero K L χ
        (hval ▸ hζ)
    exact ⟨hU, by rwa [← galoisCharacterOnIdeal_eq_char_frobeniusIdeal K L m χ hU]⟩
  · rintro ⟨hU, hfrob⟩
    rw [galoisCharacterOnIdeal_eq_char_frobeniusIdeal K L m χ hU]
    exact hfrob

/-- Planning source: ZetaProduct.lean:2043; source-local planning contract. -/
theorem finite_nonzeroIdeal_absNorm_le (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    Finite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N} :=
  haveI : Finite {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N} :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
  Finite.of_injective (fun a ↦ (⟨a.1, a.2.2⟩ : {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N}))
    fun _ _ hab ↦ Subtype.ext (by simpa using hab)

/-- Planning source: ZetaProduct.lean:1808; source-local planning contract. -/
theorem card_unramifiedSupported_frobeniusValueFibre_eq_sum
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (ζ : ℂ) (N : ℕ) :
    Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
              (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ}
        = ∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ}, Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
              frobeniusIdeal K L 𝔞 = g.1} := by
  classical
  haveI hfinN : Finite {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N} :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
  haveI hfin : ∀ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
      Finite {𝔞 : Ideal (𝓞 K) //
        𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
            frobeniusIdeal K L 𝔞 = g.1} := fun g ↦
    Finite.of_injective
      (fun a ↦ (⟨a.1, a.2.2.1⟩ : {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N}))
      (fun _ _ hab ↦ by ext1; simpa using hab)
  rw [← Nat.card_sigma]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun a ↦ (⟨a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, by rw [a.2.2.2.2.2]; exact a.1.2⟩ :
      {𝔞 : Ideal (𝓞 K) //
        𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
            (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ})) ⟨?_, ?_⟩)).symm
  · rintro ⟨⟨g₁, hg₁⟩, ⟨𝔞, ha1, ha2, haU, ha3⟩⟩ ⟨⟨g₂, hg₂⟩, ⟨𝔟, hb1, hb2, hbU, hb3⟩⟩ hab
    have h𝔞𝔟 : 𝔞 = 𝔟 := congrArg Subtype.val hab
    subst h𝔞𝔟
    have hg : g₁ = g₂ := ha3.symm.trans hb3
    subst hg
    rfl
  · rintro ⟨𝔞, h1, h2, hU, h3⟩
    exact ⟨⟨⟨frobeniusIdeal K L 𝔞, h3⟩, ⟨𝔞, h1, h2, hU, rfl⟩⟩, rfl⟩

/-- Planning source: ZetaProduct.lean:553; source-local planning contract. -/
theorem charFibre_mem_range {G : Type*} [CommGroup G] [Finite G] (χ : G →* ℂˣ) (ζ : ℂˣ)
    (hζ : ζ ^ orderOf χ = 1) :
    ∃ g : G, χ g = ζ := by
  classical
  haveI : NeZero (orderOf χ) := ⟨(orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)).ne'⟩
  haveI : Finite (MonoidHom.range χ) :=
    Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  have hpow : ∀ g : G, (χ g) ^ orderOf χ = 1 := fun g ↦ by
    rw [← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply]
  have hsub : MonoidHom.range χ ≤ rootsOfUnity (orderOf χ) ℂ := by
    rintro x ⟨g, rfl⟩
    exact (mem_rootsOfUnity (orderOf χ) (χ g)).mpr (hpow g)
  have hpowexp : ∀ g : G, (χ g) ^ Monoid.exponent (MonoidHom.range χ) = 1 := fun g ↦ by
    have hmem : χ g ∈ MonoidHom.range χ := ⟨g, rfl⟩
    simpa using congrArg Subtype.val (Monoid.pow_exponent_eq_one (⟨χ g, hmem⟩ : MonoidHom.range χ))
  have hoe : orderOf χ = Monoid.exponent (MonoidHom.range χ) := by
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one]
      exact MonoidHom.ext fun g ↦ by simpa [MonoidHom.pow_apply] using hpowexp g
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨x, g, rfl⟩
      exact Subtype.ext (by simpa [Subgroup.coe_pow] using hpow g)
  have heq : MonoidHom.range χ = rootsOfUnity (orderOf χ) ℂ :=
    Subgroup.eq_of_le_of_card_ge hsub (by
      rw [Nat.card_eq_fintype_card (α := rootsOfUnity _ ℂ), Complex.card_rootsOfUnity, hoe,
        IsCyclic.exponent_eq_card (α := MonoidHom.range χ)])
  exact χ.mem_range.mp (heq ▸ (mem_rootsOfUnity (orderOf χ) ζ).mpr hζ)

/-- Planning source: ZetaProduct.lean:585; source-local planning contract. -/
theorem card_charFibre_eq_card_ker {G : Type*} [CommGroup G] [Finite G] (χ : G →* ℂˣ) (ζ : ℂˣ)
    (hζ : ζ ^ orderOf χ = 1) :
    Nat.card {g : G // χ g = ζ} = Nat.card (MonoidHom.ker χ) := by
  obtain ⟨g₀, hg₀⟩ := charFibre_mem_range χ ζ hζ
  refine Nat.card_congr ((Equiv.subtypeEquivProp ?_).trans (χ.fiberEquivKer g₀))
  ext g
  simp [Set.mem_preimage, hg₀]

/-- Planning source: ZetaProduct.lean:1872; source-local planning contract. -/
theorem exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ C C' : ℝ, ∀ ζ : ℂ, ζ ^ orderOf χ = 1 → ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ} : ℝ)
          - C * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨κ, C₂, hL2⟩ := exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le K L m hm
  set κ₀ : ℕ := Nat.card (MonoidHom.ker χ) with hκ₀
  refine ⟨(κ₀ : ℝ) * κ, (κ₀ : ℝ) * C₂, fun ζ hζ N hN ↦ ?_⟩
  set P : ℝ := (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) with hP
  have hord : 0 < orderOf χ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)
  have hζ0 : ζ ≠ 0 := by
    intro h; subst h
    rw [zero_pow hord.ne'] at hζ
    exact zero_ne_one hζ
  set ζu : ℂˣ := Units.mk0 ζ hζ0
  have hζuval : (ζu : ℂ) = ζ := rfl
  have hζun : ζu ^ orderOf χ = 1 := by
    apply Units.ext; push_cast; rw [hζuval]; exact hζ
  set B : ℝ := (Nat.card {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
        (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
          (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ} : ℝ) with hB
  have hAB : (Nat.card {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ} : ℝ) = B := by
    rw [hB]
    exact congrArg _
      (card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre K L m χ ζ hζ0 N)
  rw [hAB]
  have hpart : B = ∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
      (Nat.card {𝔞 : Ideal (𝓞 K) //
        𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
            frobeniusIdeal K L 𝔞 = g.1} : ℝ) := by
    rw [hB, card_unramifiedSupported_frobeniusValueFibre_eq_sum K L m χ ζ N, Nat.cast_sum]
  have hSκ₀ : Nat.card {g : Gal(L/K) // (χ g : ℂ) = ζ} = κ₀ := by
    rw [hκ₀]
    have heq : {g : Gal(L/K) // (χ g : ℂ) = ζ} = {g : Gal(L/K) // χ g = ζu} := by
      congr 1; ext g
      rw [← hζuval]
      exact ⟨fun h ↦ Units.ext h, fun h ↦ congrArg Units.val h⟩
    rw [heq]
    letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
    exact card_charFibre_eq_card_ker χ ζu hζun
  have hcardℝ : (Fintype.card {g : Gal(L/K) // (χ g : ℂ) = ζ} : ℝ) = (κ₀ : ℝ) := by
    rw [← Nat.card_eq_fintype_card, hSκ₀]
  rw [hpart]
  calc
    |∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
          (Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g.1} : ℝ)
          - (κ₀ : ℝ) * κ * N|
        = |∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
            ((Nat.card {𝔞 : Ideal (𝓞 K) //
              𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
                (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                  frobeniusIdeal K L 𝔞 = g.1} : ℝ) - κ * N)| := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardℝ]
          ring_nf
    _ ≤ ∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
          |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g.1} : ℝ) - κ * N| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : {g : Gal(L/K) // (χ g : ℂ) = ζ}, C₂ * P :=
          Finset.sum_le_sum fun g _ ↦ hL2 g.1 N hN
    _ = (κ₀ : ℝ) * C₂ * P := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardℝ]; ring

/-- Planning source: ZetaProduct.lean:1971; source-local planning contract. -/
theorem galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) :
    galoisCharacterOnIdeal K L χ 𝔞 ∈
      insert (0 : ℂ) (Polynomial.nthRootsFinset (orderOf χ) 1) := by
  classical
  by_cases hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭
  · refine Finset.mem_insert_of_mem
      (Polynomial.mem_nthRootsFinset (orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)) 1 |>.mpr ?_)
    rw [galoisCharacterOnIdeal_eq_char_frobeniusIdeal K L m χ hU,
      ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
      MonoidHom.one_apply, Units.val_one]
  · push Not at hU
    obtain ⟨𝔭, h𝔭, hram⟩ := hU
    rw [galoisCharacterOnIdeal_eq_map_prod,
      Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨𝔭, h𝔭, if_neg hram⟩)]
    exact Finset.mem_insert_self _ _

/-- Planning source: ZetaProduct.lean:1948; source-local planning contract. -/
theorem sum_nthRootsFinset_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) :
    ∑ v ∈ Polynomial.nthRootsFinset n (1 : R), v = 0 := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn0
  have hmem : ∀ {z : R}, z ∈ Polynomial.nthRootsFinset n (1 : R) ↔ z ^ n = 1 := fun {z} ↦
    Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn0) 1
  have himg : (Polynomial.nthRootsFinset n (1 : R)).image (ζ * ·) =
      Polynomial.nthRootsFinset n 1 := by
    refine Finset.eq_of_subset_of_card_le (fun x hx ↦ ?_)
      (Finset.card_image_of_injective _ (mul_right_injective₀ hζ0)).ge
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact hmem.mpr (by rw [mul_pow, hζ.pow_eq_one, one_mul, hmem.mp hv])
  have hshift : ∑ v ∈ Polynomial.nthRootsFinset n (1 : R), v =
      ζ * ∑ v ∈ Polynomial.nthRootsFinset n 1, v := by
    nth_rewrite 1 [← himg]
    rw [Finset.sum_image fun a _ b _ h ↦ mul_right_injective₀ hζ0 h, Finset.mul_sum]
  rcases mul_eq_zero.mp (by rw [sub_mul, one_mul, ← hshift, sub_self] :
      (ζ - 1) * ∑ v ∈ Polynomial.nthRootsFinset n (1 : R), v = 0) with h | h
  · exact absurd (sub_eq_zero.mp h) (hζ.ne_one hn)
  · exact h

/-- Planning source: ZetaProduct.lean:1990; source-local planning contract. -/
theorem sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (hord2 : 1 < orderOf χ) (C₀ : ℝ)
    (N : ℕ) [Fintype {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N}] :
    ∑ 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
        galoisCharacterOnIdeal K L χ 𝔞.1
      = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1,
          (((Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
              - C₀ * N : ℝ) : ℂ) * v := by
  classical
  obtain ⟨ζ₀, hζ₀⟩ : ∃ z : ℂ, IsPrimitiveRoot z (orderOf χ) :=
    ⟨_, Complex.isPrimitiveRoot_exp _ (by omega)⟩
  have h0R : (0 : ℂ) ∉ Polynomial.nthRootsFinset (orderOf χ) 1 := fun h ↦ by
    rw [Polynomial.mem_nthRootsFinset (by omega) 1, zero_pow (by omega)] at h
    exact zero_ne_one h
  calc ∑ 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
        galoisCharacterOnIdeal K L χ 𝔞.1
      = ∑ v ∈ insert (0 : ℂ) (Polynomial.nthRootsFinset (orderOf χ) 1),
          ∑ 𝔞 ∈ (Finset.univ : Finset {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N})
            with galoisCharacterOnIdeal K L χ 𝔞.1 = v, v :=
        (Finset.sum_fiberwise_of_maps_to'
          (fun 𝔞 _ ↦ galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset K L m χ 𝔞.1)
          fun z : ℂ ↦ z).symm
    _ = ∑ v ∈ insert (0 : ℂ) (Polynomial.nthRootsFinset (orderOf χ) 1),
          (Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℂ) * v := by
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        refine congrArg (· * v) (congrArg (Nat.cast : ℕ → ℂ) ?_)
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
        exact Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter
          (fun 𝔞 : Ideal (𝓞 K) ↦ 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N)
          (fun 𝔞 ↦ galoisCharacterOnIdeal K L χ 𝔞 = v)).trans
          (Equiv.subtypeEquivRight fun 𝔞 ↦ and_assoc))
    _ = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1, (Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℂ) * v := by
        rw [Finset.sum_insert h0R, mul_zero, zero_add]
    _ = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1, ((((Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
            - C₀ * N : ℝ) : ℂ) * v + ((C₀ * N : ℝ) : ℂ) * v) := by
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        push_cast
        ring
    _ = ∑ v ∈ Polynomial.nthRootsFinset (orderOf χ) 1, (((Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
            - C₀ * N : ℝ) : ℂ) * v := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          sum_nthRootsFinset_eq_zero hζ₀ hord2, mul_zero, add_zero]

/-- Planning source: ZetaProduct.lean:2055; source-local planning contract. -/
theorem character_sum_geometry_of_numbers_bound
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖∑' 𝔞 : {𝔞 : Ideal (𝓞 K) //
                𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
        galoisCharacterOnIdeal K L χ 𝔞.1‖
        ≤ C * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨C₀, C', hcount⟩ := exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow K L m hm χ _hχ
  refine ⟨(orderOf χ : ℝ) * C', fun N ↦ ?_⟩
  have hC' : 0 ≤ C' := (abs_nonneg _).trans (by simpa using hcount 1 (one_pow _) 1 le_rfl)
  rcases Nat.eq_zero_or_pos N with rfl | hN1
  · haveI : IsEmpty {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ 0} :=
      ⟨fun 𝔞 ↦ 𝔞.2.1 (Ideal.absNorm_eq_zero_iff.mp (Nat.le_zero.mp 𝔞.2.2))⟩
    rw [tsum_empty, norm_zero]
    positivity
  have hord0 : orderOf χ ≠ 0 := (orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)).ne'
  have hord2 : 1 < orderOf χ :=
    lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hord0) fun h ↦ _hχ (orderOf_eq_one_iff.mp h.symm)
  obtain ⟨ζ₀, hζ₀⟩ : ∃ z : ℂ, IsPrimitiveRoot z (orderOf χ) :=
    ⟨_, Complex.isPrimitiveRoot_exp _ hord0⟩
  set R : Finset ℂ := Polynomial.nthRootsFinset (orderOf χ) (1 : ℂ) with hR
  have hmemR : ∀ {z : ℂ}, z ∈ R ↔ z ^ orderOf χ = 1 := fun {z} ↦
    Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hord0) 1
  haveI := finite_nonzeroIdeal_absNorm_le K N
  haveI := Fintype.ofFinite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N}
  rw [tsum_fintype, sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul K L m χ hord2 C₀ N]
  calc ‖∑ v ∈ R, (((Nat.card {𝔞 : Ideal (𝓞 K) //
        𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
          - C₀ * N : ℝ) : ℂ) * v‖
      ≤ ∑ v ∈ R, ‖(((Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = v} : ℝ)
            - C₀ * N : ℝ) : ℂ) * v‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ R, C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
        refine Finset.sum_le_sum fun v hv ↦ ?_
        rw [norm_mul, Complex.norm_eq_one_of_pow_eq_one (hmemR.mp hv) hord0, mul_one,
          Complex.norm_real, Real.norm_eq_abs]
        exact hcount v (hmemR.mp hv) N hN1
    _ = (orderOf χ : ℝ) * C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
        rw [Finset.sum_const, hR, hζ₀.card_nthRootsFinset, nsmul_eq_mul]
        ring

/-- Planning source: ZetaProduct.lean:2102; source-local planning contract. -/
def galoisCharacterCoeff
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (n : ℕ) : ℂ :=
  ∑' 𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n}, galoisCharacterOnIdeal K L χ 𝔞.1.1

/-- Each norm fibre of nonzero ideals is finite (AINTLIB ZetaProduct.lean:2109). -/
theorem finite_nonzeroIdeal_absNorm_eq
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n} :=
  Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal K ↦ I.1)
    ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
    (fun _ _ _ _ ↦ Subtype.ext)

/-- Planning source: ZetaProduct.lean:2149; source-local planning contract. -/
theorem sum_galoisCharacterCoeff_eq_tsum_absNorm_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, galoisCharacterCoeff K L χ k =
      ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n},
        galoisCharacterOnIdeal K L χ 𝔞.1 := by
  classical
  haveI := finite_nonzeroIdeal_absNorm_le K n
  haveI := Fintype.ofFinite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n}
  rw [tsum_fintype, ← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc 1 n)
      (g := fun 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n} ↦ Ideal.absNorm 𝔞.1)
      (fun 𝔞 _ ↦ Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp 𝔞.2.1), 𝔞.2.2⟩)
      (fun 𝔞 ↦ galoisCharacterOnIdeal K L χ 𝔞.1)]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [galoisCharacterCoeff, ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  haveI := finite_nonzeroIdeal_absNorm_eq K k
  haveI := Fintype.ofFinite {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = k}
  rw [tsum_fintype]
  exact Fintype.sum_equiv
    { toFun := fun ⟨⟨𝔞, h𝔞ne⟩, hnorm⟩ ↦
        (⟨⟨𝔞, h𝔞ne, hnorm.le.trans (Finset.mem_Icc.mp hk).2⟩, hnorm⟩ :
          {x : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ n} // Ideal.absNorm x.1 = k})
      invFun := fun ⟨⟨𝔞, h𝔞⟩, hnorm⟩ ↦ ⟨⟨𝔞, h𝔞.1⟩, hnorm⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl } _ _ fun _ ↦ rfl

/-- Planning source: ZetaProduct.lean:2179; source-local planning contract. -/
theorem sum_galoisCharacterCoeff_isBigO
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, galoisCharacterCoeff K L χ k)
      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹)) := by
  obtain ⟨C, hC⟩ := character_sum_geometry_of_numbers_bound K L m hm χ _hχ
  refine Asymptotics.isBigO_iff.mpr ⟨C, Filter.Eventually.of_forall fun n ↦ ?_⟩
  rw [sum_galoisCharacterCoeff_eq_tsum_absNorm_le K L χ n,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact hC n

/-- Planning source: ZetaProduct.lean:2126; source-local planning contract. -/
theorem norm_galoisCharacterCoeff_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (n : ℕ) :
    ‖galoisCharacterCoeff K L χ n‖ ≤ (idealNormMultiplicity K n : ℝ) := by
  haveI := finite_nonzeroIdeal_absNorm_eq K n
  haveI := Fintype.ofFinite {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n}
  calc ‖galoisCharacterCoeff K L χ n‖
      ≤ ∑' 𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n},
          ‖galoisCharacterOnIdeal K L χ 𝔞.1.1‖ :=
        norm_tsum_le_tsum_norm Summable.of_finite
    _ = ∑ 𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n},
          ‖galoisCharacterOnIdeal K L χ 𝔞.1.1‖ := tsum_fintype _
    _ ≤ ∑ _𝔞 : {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = n}, (1 : ℝ) :=
        Finset.sum_le_sum fun 𝔞 _ ↦ norm_galoisCharacterOnIdeal_le_one K L χ 𝔞.1.1
    _ = (idealNormMultiplicity K n : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, idealNormMultiplicity,
          Nat.card_eq_fintype_card]
        simp [Finset.card_univ]

/-- Planning source: ZetaProduct.lean:2195; source-local planning contract. -/
theorem sum_norm_galoisCharacterCoeff_isBigO
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖galoisCharacterCoeff K L χ k‖)
      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
  refine (Asymptotics.isBigO_of_le Filter.atTop fun n ↦ ?_).trans
    (sum_idealNormMultiplicity_isBigO K)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)]
  exact Finset.sum_le_sum fun k _ ↦ norm_galoisCharacterCoeff_le K L χ k

/-- Planning source: ZetaProduct.lean:2117; source-local planning contract. -/
theorem galoisCharacterCoeff_zero
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) : galoisCharacterCoeff K L χ 0 = 0 := by
  have : IsEmpty {𝔞 : NonzeroIdeal K // Ideal.absNorm 𝔞.1 = 0} :=
    ⟨fun 𝔞 ↦ 𝔞.1.2 (Ideal.absNorm_eq_zero_iff.mp 𝔞.2)⟩
  rw [galoisCharacterCoeff, tsum_empty]

/-- Planning source: ZetaProduct.lean:2212; source-local planning contract. -/
theorem lseries_galoisCharacterCoeff_eq_tsum
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (s : ℂ) (hs : 1 < s.re) :
    LSeries (galoisCharacterCoeff K L χ) s =
      ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
        galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) := by
  classical
  set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1) with he
  have hsummable : Summable fun I : NonzeroIdeal K ↦
      ‖galoisCharacterOnIdeal K L χ I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun I ↦ ?_)
      (hasSum_nonzeroIdeal_absNorm_cpow K hs).summable.norm
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_galoisCharacterOnIdeal_le_one K L χ I.1)
  have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦
      galoisCharacterOnIdeal K L χ (e p).1 * (Ideal.absNorm (e p).1 : ℂ) ^ (-s) :=
    (e.summable_iff (f := fun I : NonzeroIdeal K ↦
      galoisCharacterOnIdeal K L χ I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s))).mpr hsummable.of_norm
  have hfiber_val : ∀ n : ℕ,
      (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
        galoisCharacterOnIdeal K L χ (y.1).1 * (Ideal.absNorm (y.1).1 : ℂ) ^ (-s))
        = galoisCharacterCoeff K L χ n * (n : ℂ) ^ (-s) := fun n ↦ by
    have hconst : ∀ y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
        galoisCharacterOnIdeal K L χ (y.1).1 * (Ideal.absNorm (y.1).1 : ℂ) ^ (-s) =
          galoisCharacterOnIdeal K L χ (y.1).1 * (n : ℂ) ^ (-s) := fun y ↦ by rw [y.2]
    rw [tsum_congr hconst, tsum_mul_right, galoisCharacterCoeff]
  rw [show LSeries (galoisCharacterCoeff K L χ) s =
      ∑' n, galoisCharacterCoeff K L χ n * (n : ℂ) ^ (-s) from
    tsum_congr fun n ↦ LSeries.term_def₀ (galoisCharacterCoeff_zero K L χ) s n,
    ← e.tsum_eq (fun I : NonzeroIdeal K ↦
      galoisCharacterOnIdeal K L χ I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)),
    hsummable_sigma.tsum_sigma]
  exact (tsum_congr hfiber_val).symm

/-- Planning source: ZetaProduct.lean:2247; source-local planning contract. -/
theorem setIntegral_Ioi_one_mul_cpow_eq_mellin (S : ℝ → ℂ) (hS : ∀ t < 1, S t = 0) (s : ℂ) :
    ∫ t in Ioi (1 : ℝ), S t * (t : ℂ) ^ (-(s + 1)) = mellin S (-s) := by
  rw [mellin, show (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-s - 1) • S t) =
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) • S t from ?_]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    rw [smul_eq_mul]
    ring_nf
  · have hinter : Ioi (0 : ℝ) ∩ Ioi (1 : ℝ) = Ioi (1 : ℝ) :=
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num))
    rw [← hinter, ← setIntegral_indicator measurableSet_Ioi]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 1 from
      ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 1} = 0)] with t ht _
    rw [indicator_apply]
    by_cases h1 : t ∈ Ioi (1 : ℝ)
    · rw [if_pos h1]
    · rw [if_neg h1, hS t (lt_of_le_of_ne (not_lt.mp (by simpa using h1)) ht), smul_zero]

/-- Planning source: ZetaProduct.lean:2290; source-local planning contract. -/
theorem artinLSeries_analytic_extension
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ Lf : ℂ → ℂ,
      AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        Lf s =
          ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
            galoisCharacterOnIdeal K L χ 𝔞.1 *
              (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) := by
  classical
  set r : ℝ := 1 - (Module.finrank ℚ K : ℝ)⁻¹ with hr_def
  have hrinv : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ := by
    rw [inv_pos]; exact_mod_cast Module.finrank_pos
  have hr0 : 0 ≤ r := by
    rw [hr_def, sub_nonneg, inv_le_one_iff₀]; right; exact_mod_cast Module.finrank_pos
  have hr1 : r < 1 := by rw [hr_def]; linarith
  set S : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, galoisCharacterCoeff K L χ k with hS_def
  have hS_zero : ∀ t : ℝ, t < 1 → S t = 0 := fun t ht ↦ by
    change ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, galoisCharacterCoeff K L χ k = 0
    rw [Nat.floor_eq_zero.mpr ht, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
  have hS_bigO : S =O[Filter.atTop] (fun t : ℝ ↦ t ^ r) :=
    ((sum_galoisCharacterCoeff_isBigO K L m hm χ _hχ).comp_tendsto
      tendsto_nat_floor_atTop).trans <|
      Asymptotics.isEquivalent_nat_floor.isBigO.rpow hr0 (Filter.eventually_ge_atTop 0)
  refine ⟨fun s ↦ s * mellin S (-s), ?_, fun s hs ↦ ?_⟩
  · refine DifferentiableOn.analyticOn (fun s₀ hs₀ ↦ ?_)
      (isOpen_lt continuous_const Complex.continuous_re)
    have hs₀' : r < s₀.re := hs₀
    have hfc : LocallyIntegrableOn S (Ioi (0 : ℝ)) := by
      simpa only [one_mul] using (locallyIntegrableOn_mul_sum_Icc (a := 0) (m := 1)
        (galoisCharacterCoeff K L χ) le_rfl (locallyIntegrableOn_const 1)).mono_set
          Set.Ioi_subset_Ici_self
    have hf_top : S =O[Filter.atTop] (fun t : ℝ ↦ t ^ (-(-r))) := by rw [neg_neg]; exact hS_bigO
    have hf_bot : S =O[𝓝[>] (0 : ℝ)] (fun t : ℝ ↦ t ^ (-(-s₀.re - 1))) :=
      Filter.EventuallyEq.trans_isBigO
        (by filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht using
          hS_zero t (Set.mem_Ioo.mp ht).2) (Asymptotics.isBigO_zero _ _)
    have hmellin : DifferentiableAt ℂ (mellin S) (-s₀) :=
      mellin_differentiableAt_of_isBigO_rpow hfc hf_top (by rw [Complex.neg_re]; linarith)
        hf_bot (by rw [Complex.neg_re]; linarith)
    exact (differentiableAt_id.mul (hmellin.comp s₀ differentiableAt_id.neg)).differentiableWithinAt
  · have hssum : LSeriesSummable (galoisCharacterCoeff K L χ) s :=
      LSeriesSummable_of_sum_norm_bigO (sum_norm_galoisCharacterCoeff_isBigO K L χ) zero_le_one
        (by exact_mod_cast hs)
    rw [← lseries_galoisCharacterCoeff_eq_tsum K L χ s hs,
      LSeries_eq_mul_integral (galoisCharacterCoeff K L χ) hr0
        (lt_of_lt_of_le hr1 (by exact_mod_cast hs.le)) hssum
        (sum_galoisCharacterCoeff_isBigO K L m hm χ _hχ),
      setIntegral_Ioi_one_mul_cpow_eq_mellin S hS_zero s]

/-- Planning source: ZetaProduct.lean:2927; source-local planning contract. -/
theorem analyticAt_one_of_analyticOn_finrankDomain (K : Type*) [Field K] [NumberField K]
    {Lf : ℂ → ℂ} (hLf : AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re}) :
    AnalyticAt ℂ Lf 1 := by
  have hmem : (1 : ℂ) ∈ {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} := by
    have hdpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ := by
      have : 0 < Module.finrank ℚ K := Module.finrank_pos
      positivity
    simp only [Set.mem_setOf_eq, Complex.one_re]; linarith
  exact hLf.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)

/-- Planning source: ZetaProduct.lean:2440; source-local planning contract. -/
def artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (s : ℂ) : ℂ :=
  ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
    galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)

/-- Planning source: ZetaProduct.lean:2451; source-local planning contract. -/
theorem norm_one_sub_inv_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) :
    ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := by
  have hyne1 : (1 : ℂ) - y ≠ 0 := sub_ne_zero.mpr (by rintro rfl; norm_num at hy)
  have heq : (1 - y)⁻¹ - 1 = y * (1 - y)⁻¹ := by field_simp; ring
  rw [heq, norm_mul]
  have hnorm_lb : (2 : ℝ)⁻¹ ≤ ‖(1 : ℂ) - y‖ :=
    calc (2 : ℝ)⁻¹ = 1 - 1 / 2 := by norm_num
      _ ≤ 1 - ‖y‖ := by linarith
      _ ≤ ‖(1 : ℂ)‖ - ‖y‖ := by rw [norm_one]
      _ ≤ ‖(1 : ℂ) - y‖ := norm_sub_norm_le 1 y
  have hinv : ‖(1 - y)⁻¹‖ ≤ 2 := by
    rw [norm_inv, show (2 : ℝ) = (2⁻¹ : ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) hnorm_lb
  rw [mul_comm 2 ‖y‖]
  gcongr

/-- Planning source: ZetaProduct.lean:2469; source-local planning contract. -/
theorem two_le_absNorm {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] {𝔭 : Ideal R} (hp : 𝔭.IsPrime) (hb : 𝔭 ≠ ⊥) :
    2 ≤ Ideal.absNorm 𝔭 := by
  have hne0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ hb (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ hp.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

/-- Planning source: ZetaProduct.lean:2478; source-local planning contract. -/
theorem norm_absNorm_cpow_neg_le_half {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] {s : ℂ} (hs : 1 < s.re)
    (𝔭 : {𝔭 : Ideal R // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have h2le : 2 ≤ Ideal.absNorm 𝔭.1 := two_le_absNorm 𝔭.2.1 𝔭.2.2
  have hpos : 0 < Ideal.absNorm 𝔭.1 := by omega
  rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
  have hb2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by exact_mod_cast h2le
  have hb1 : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := one_le_two.trans hb2
  calc (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re)
      ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    _ = ((Ideal.absNorm 𝔭.1 : ℝ))⁻¹ := Real.rpow_neg_one _
    _ ≤ (2 : ℝ)⁻¹ := by rw [inv_le_inv₀ (by linarith) (by norm_num)]; exact hb2
    _ = 1 / 2 := by norm_num

/-- Planning source: ZetaProduct.lean:2498; source-local planning contract. -/
theorem summable_norm_primeIdeal_factor_sub_one
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re) :
    Summable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖ := by
  have hsum : Summable fun 𝔞 : NonzeroIdeal L ↦ ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)‖ :=
    (hasSum_nonzeroIdeal_absNorm_cpow L hs).summable.norm
  have hsumP : Summable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      ‖(Ideal.absNorm 𝔓.1 : ℂ) ^ (-s)‖ :=
    hsum.comp_injective (i := fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      (⟨𝔓.1, 𝔓.2.2⟩ : NonzeroIdeal L))
      (fun a b h ↦ Subtype.ext (by simpa using h))
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun 𝔓 ↦ ?_) (hsumP.mul_left 2)
  exact norm_one_sub_inv_sub_one_le (norm_absNorm_cpow_neg_le_half (R := 𝓞 L) hs 𝔓)

/-- Planning source: ZetaProduct.lean:2516; source-local planning contract. -/
theorem hasProd_primeIdeal_factor
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹) (NumberField.dedekindZeta L s) := by
  have hmul : Multipliable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ := by
    simpa using multipliable_one_add_of_summable
      (f := fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1)
      (summable_norm_primeIdeal_factor_sub_one L hs)
  rw [dedekindZeta_eq_tprod_primeIdeal L hs]
  exact hmul.hasProd

/-- Planning source: ZetaProduct.lean:2533; source-local planning contract. -/
theorem multipliable_primeIdeal_factor_subtype
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re)
    (p : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} → Prop) :
    Multipliable fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} ↦
      (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ := by
  have hsum : Summable ((fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
      ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖) ∘ (↑) :
      {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} → ℝ) :=
    (summable_norm_primeIdeal_factor_sub_one L hs).subtype p
  simpa using multipliable_one_add_of_summable
    (f := fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} ↦
      (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ - 1) hsum

/-- Planning source: ZetaProduct.lean:2714; source-local planning contract. -/
theorem dedekindZeta_eq_unramifiedNested_mul_ramifiedNested
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹) *
        ∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ := by
  -- `f`/`S` are pinned explicitly so `HasProd.mul_compl` does no higher-order unification
  -- (`?f ∘ Subtype.val`) on the nested `Ideal (𝓞 L)` prime subtype — that is the `whnf` bomb.
  let f : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} → ℂ :=
    fun 𝔓 ↦ (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹
  let S : Set {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} :=
    {𝔓 | UnramifiedIn K L (𝔓.1.under (𝓞 K))}
  have hSU := (multipliable_primeIdeal_factor_subtype L hs
    (fun 𝔓 ↦ UnramifiedIn K L (𝔓.1.under (𝓞 K)))).hasProd
  have hSUc := (multipliable_primeIdeal_factor_subtype L hs
    (fun 𝔓 ↦ ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K)))).hasProd
  exact ((hSU.mul_compl (f := f) (s := S) hSUc).unique
    (hasProd_primeIdeal_factor L hs)).symm

/-- Planning source: ZetaProduct.lean:2550; source-local planning contract. -/
theorem multipliable_artinLocalFactor
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ := by
  have hsum : Summable fun 𝔞 : NonzeroIdeal K ↦ ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)‖ :=
    (hasSum_nonzeroIdeal_absNorm_cpow K hs).summable.norm
  have hsumP : Summable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ :=
    hsum.comp_injective (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (⟨𝔭.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩ : NonzeroIdeal K))
      (fun _ _ h ↦ Subtype.ext (by simpa using h))
  have hsummable : Summable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      ‖(1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ - 1‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun 𝔭 ↦ ?_) (hsumP.mul_left 2)
    set y : ℂ := (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s) with hy
    have hynorm : ‖y‖ ≤ 1 / 2 := by
      rw [hy, norm_mul, norm_galoisCharacter_out, one_mul]
      exact norm_absNorm_cpow_neg_le_half (R := 𝓞 K) hs
        ⟨𝔭.1, 𝔭.2.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩
    calc ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := norm_one_sub_inv_sub_one_le hynorm
      _ = 2 * ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ := by
          rw [hy, norm_mul, norm_galoisCharacter_out, one_mul]
  simpa using multipliable_one_add_of_summable
    (f := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ - 1) hsummable

/-- Planning source: ZetaProduct.lean:250; source-local planning contract. -/
def charEval {G : Type*} [CommGroup G] [Finite G] (σ : G) :
    (G →* ℂˣ) →* ℂˣ := (CommGroup.monoidHomMonoidHomEquiv G ℂ).symm σ

/-- Planning source: ZetaProduct.lean:253; source-local planning contract. -/
theorem charEval_apply {G : Type*} [CommGroup G] [Finite G] (σ : G) (φ : G →* ℂˣ) :
    charEval σ φ = φ σ := by
  rw [charEval, CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply]

/-- Planning source: ZetaProduct.lean:258; source-local planning contract. -/
theorem charEval_ker_card {G : Type*} [CommGroup G] [Finite G] (σ : G) :
    Nat.card (charEval σ).ker = Nat.card G / orderOf σ := by
  have h1 : (charEval σ).ker = (MonoidHom.restrictHom (Subgroup.zpowers σ) ℂˣ).ker := by
    ext φ
    simp only [MonoidHom.mem_ker, MonoidHom.restrictHom_apply, MonoidHom.restrict_eq_one_iff]
    refine ⟨fun hφ y hy ↦ ?_, fun hφ ↦ ?_⟩
    · rw [charEval_apply] at hφ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [map_zpow, hφ, one_zpow]
    · rw [charEval_apply]
      exact hφ σ (Subgroup.mem_zpowers σ)
  rw [h1, CommGroup.card_restrictHom_ker]
  have hpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  have key : Nat.card G = Nat.card (G ⧸ Subgroup.zpowers σ) * orderOf σ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers σ), Nat.card_zpowers]
  rw [key, Nat.mul_div_cancel _ hpos]

/-- Planning source: ZetaProduct.lean:244; source-local planning contract. -/
theorem prod_one_sub_nthRoots (f : ℕ) (hf : 0 < f) (Y : ℂ) :
    ∏ ζ ∈ Polynomial.nthRootsFinset f (1 : ℂ), (1 - ζ * Y) = 1 - Y ^ f := by
  rw [← (Complex.isPrimitiveRoot_exp f hf.ne').pow_sub_pow_eq_prod_sub_mul 1 Y hf, one_pow]

open Finset in
/-- Planning source: ZetaProduct.lean:282; source-local planning contract. -/
theorem prod_galoisCharacter_one_sub {G : Type*} [CommGroup G] [Finite G]
    [Fintype (G →* ℂˣ)] (σ : G) (Y : ℂ) :
    ∏ χ : G →* ℂˣ, (1 - ((χ σ : ℂˣ) : ℂ) * Y)
      = (1 - Y ^ orderOf σ) ^ (Nat.card G / orderOf σ) := by
  classical
  set f := orderOf σ with hf
  have hfpos : 0 < f := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  set evC : (G →* ℂˣ) →* ℂ := (Units.coeHom ℂ).comp (charEval σ) with hevC
  have hevC_apply : ∀ χ : G →* ℂˣ, evC χ = ((χ σ : ℂˣ) : ℂ) := fun χ ↦ by
    rw [hevC, MonoidHom.comp_apply, Units.coeHom_apply, charEval_apply]
  have hfib1 : #{χ : G →* ℂˣ | evC χ = 1} = Nat.card (charEval σ).ker := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun χ ↦ ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_ker, hevC_apply]
    rw [Units.val_eq_one, ← charEval_apply σ χ]
  have huniform : ∀ c ∈ Set.range evC, #{χ : G →* ℂˣ | evC χ = c} = Nat.card (charEval σ).ker := by
    intro c hc
    rw [MonoidHom.card_fiber_eq_of_mem_range evC hc (⟨1, map_one _⟩ : (1 : ℂ) ∈ Set.range evC),
      hfib1]
  set t : Finset ℂ := Polynomial.nthRootsFinset f (1 : ℂ) with ht
  have hmaps : ∀ χ ∈ (Finset.univ : Finset (G →* ℂˣ)), evC χ ∈ t := by
    intro χ _
    rw [ht, Polynomial.mem_nthRootsFinset hfpos, hevC_apply,
      ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  have hsub : Finset.univ.image evC ⊆ t := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨χ, _, rfl⟩ := hc
    exact hmaps χ (Finset.mem_univ χ)
  have hcardG : Nat.card G = (Finset.univ.image evC).card * Nat.card (charEval σ).ker := by
    have hsum := Finset.card_eq_sum_card_image evC (Finset.univ : Finset (G →* ℂˣ))
    rw [show (Finset.univ : Finset (G →* ℂˣ)).card = Nat.card (G →* ℂˣ) by
      rw [Nat.card_eq_fintype_card, Finset.card_univ],
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity] at hsum
    rw [hsum, Finset.sum_congr rfl (fun c hc ↦ huniform c ?_), Finset.sum_const, smul_eq_mul]
    rw [Finset.mem_image] at hc
    obtain ⟨χ, _, rfl⟩ := hc
    exact Set.mem_range_self χ
  have himgcard : (Finset.univ.image evC).card = f := by
    have hdvd : f ∣ Nat.card G := orderOf_dvd_natCard σ
    have hkereq : Nat.card (charEval σ).ker = Nat.card G / f := charEval_ker_card σ
    rw [hkereq] at hcardG
    exact Nat.eq_of_mul_eq_mul_right (hkereq ▸ Nat.card_pos)
      (by rw [← hcardG, Nat.mul_div_cancel' hdvd])
  have himg : Finset.univ.image evC = t :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [himgcard, ht, (Complex.isPrimitiveRoot_exp f hfpos.ne').card_nthRootsFinset])
  have hfiber := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (G →* ℂˣ)))
    (t := t) (g := evC) (f := fun c : ℂ ↦ 1 - c * Y) hmaps
  have hLHS : ∏ χ : G →* ℂˣ, (1 - ((χ σ : ℂˣ) : ℂ) * Y)
      = ∏ χ : G →* ℂˣ, (1 - evC χ * Y) :=
    Finset.prod_congr rfl fun χ _ ↦ by rw [hevC_apply]
  rw [hLHS, ← hfiber]
  have hinner : ∀ c ∈ t, (∏ _χ ∈ {χ ∈ (Finset.univ : Finset (G →* ℂˣ)) | evC χ = c},
      (1 - c * Y)) = (1 - c * Y) ^ Nat.card (charEval σ).ker := by
    intro c hc
    have hrange : c ∈ Set.range evC := by
      rw [← himg, Finset.mem_image] at hc
      obtain ⟨χ, _, rfl⟩ := hc
      exact Set.mem_range_self χ
    rw [Finset.prod_const, huniform c hrange]
  rw [Finset.prod_congr rfl hinner, charEval_ker_card σ, Finset.prod_pow, ht,
    prod_one_sub_nthRoots f hfpos Y]

/-- Planning source: ZetaProduct.lean:348; source-local planning contract. -/
theorem cpow_neg_absNorm_eq_pow {a b : ℕ} (f : ℕ) (s : ℂ)
    (h : b = a ^ f) : ((b : ℂ)) ^ (-s) = ((a : ℂ) ^ (-s)) ^ f := by
  rw [h, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-- Planning source: ZetaProduct.lean:357; source-local planning contract. -/
theorem dedekindZeta_local_factor_eq_product_artin_local
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (_hunr : UnramifiedIn K L 𝔭) (s : ℂ) (_hs : 1 < s.re) :
    ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥},
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹
      = ∏' χ : galoisCharacter K L,
        (1 - (χ (frobeniusClass K L 𝔭).out : ℂ) * (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  classical
  open scoped IsMulCommutative in
  letI : CommGroup Gal(L/K) := inferInstance
  set σ : Gal(L/K) := (frobeniusClass K L 𝔭).out
  set Y : ℂ := (Ideal.absNorm 𝔭 : ℂ) ^ (-s) with hY
  set f : ℕ := orderOf σ with hf
  haveI : Fintype Gal(L/K) := Fintype.ofFinite _
  haveI : Fintype (Gal(L/K) →* ℂˣ) := Fintype.ofFinite _
  have hfpos : 0 < f := hf ▸ orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  have hcount : Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}
      = Nat.card Gal(L/K) / f := by
    have hmul := card_primesAbove_mul_orderOf_eq K L σ (frobeniusClass K L 𝔭)
      (Quotient.out_eq _) 𝔭 _hunr rfl
    rw [← hf] at hmul
    exact (Nat.div_eq_of_eq_mul_left hfpos hmul.symm).symm
  have hRHS : (∏' χ : galoisCharacter K L,
        (1 - ((χ σ : ℂˣ) : ℂ) * Y)⁻¹)
      = ((1 - Y ^ f) ^ (Nat.card Gal(L/K) / f))⁻¹ := by
    rw [tprod_fintype, Finset.prod_inv_distrib, prod_galoisCharacter_one_sub σ Y, hf]
  have hpbot : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L _hunr
  haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal hpbot
  haveI : Finite (𝔭.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite 𝔭 (𝓞 L)).to_subtype
  haveI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} :=
    Finite.of_injective
      (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} ↦
        (⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩ : 𝔭.primesOver (𝓞 L)))
      fun _ _ hab ↦ Subtype.ext (by simpa using hab)
  haveI : Fintype {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} := Fintype.ofFinite _
  have hterm : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥},
      (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ = (1 - Y ^ f)⁻¹ := by
    intro 𝔓
    haveI := 𝔓.2.1
    haveI hlo : 𝔓.1.LiesOver 𝔭 := 𝔓.2.2.1
    have hdeg : (𝔓.1.under (𝓞 K)).inertiaDeg 𝔓.1 = f := by
      rw [Ideal.inertiaDeg_algebraMap, hf]
      exact finrank_residue_eq_orderOf K L σ (frobeniusClass K L 𝔭) (Quotient.out_eq _)
        𝔭 _hunr rfl 𝔓.1 hlo
    haveI : 𝔓.1.LiesOver (𝔓.1.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓.1)
    have hpubot : 𝔓.1.under (𝓞 K) ≠ ⊥ := hlo.over ▸ hpbot
    haveI : (𝔓.1.under (𝓞 K)).IsPrime := hlo.over ▸ ‹𝔭.IsPrime›
    have hnorm : Ideal.absNorm 𝔓.1 = Ideal.absNorm 𝔭 ^ f := by
      rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.1 (𝔓.1.under (𝓞 K)) inferInstance hpubot,
        hdeg, ← hlo.over]
    rw [cpow_neg_absNorm_eq_pow f s hnorm, hY]
  rw [tprod_congr hterm, tprod_fintype, Finset.prod_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hcount, hRHS, Nat.card_eq_fintype_card, inv_pow]

/-- The unramified `K`-prime below an unramified-below `L`-prime
(AINTLIB ZetaProduct.lean:2579). -/
def underUP
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))}) :
    {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} :=
  ⟨𝔓.1.under (𝓞 K), by haveI := 𝔓.2.1; exact inferInstance, 𝔓.2.2.2⟩

@[simp] theorem underUP_val
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))}) :
    (underUP K L 𝔓).1 = 𝔓.1.under (𝓞 K) := rfl

/-- The fibre of `underUP` over `c` is the set of primes lying over `c`
(AINTLIB ZetaProduct.lean:2593). -/
def fiberUnderEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}) :
    {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))} //
        underUP K L 𝔓 = c} ≃
      {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} where
  toFun 𝔓 := ⟨𝔓.1.1, 𝔓.1.2.1, ⟨by
    have h := congrArg Subtype.val 𝔓.2; rw [underUP_val] at h; rw [← h]⟩, 𝔓.1.2.2.1⟩
  invFun 𝔔 := ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.2, by
      haveI := 𝔔.2.1; haveI := 𝔔.2.2.1; rw [← 𝔔.2.2.1.over]; exact c.2.2⟩, by
    haveI := 𝔔.2.1; haveI := 𝔔.2.2.1
    exact Subtype.ext (by rw [underUP_val]; exact 𝔔.2.2.1.over.symm)⟩
  left_inv 𝔓 := by ext; rfl
  right_inv 𝔔 := by ext; rfl

/-- Flatten the nested unramified-below prime subtype (AINTLIB ZetaProduct.lean:2612). -/
def unramifiedFlattenEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // UnramifiedIn K L (𝔓.1.under (𝓞 K))} ≃
      {𝔔 : Ideal (𝓞 L) // 𝔔.IsPrime ∧ 𝔔 ≠ ⊥ ∧ UnramifiedIn K L (𝔔.under (𝓞 K))} where
  toFun 𝔓 := ⟨𝔓.1.1, 𝔓.1.2.1, 𝔓.1.2.2, 𝔓.2⟩
  invFun 𝔔 := ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.1⟩, 𝔔.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Flatten the nested ramified-below prime subtype (AINTLIB ZetaProduct.lean:2625). -/
def ramifiedFlattenEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K))} ≃
      {𝔔 : Ideal (𝓞 L) // 𝔔.IsPrime ∧ 𝔔 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔔.under (𝓞 K))} where
  toFun 𝔓 := ⟨𝔓.1.1, 𝔓.1.2.1, 𝔓.1.2.2, 𝔓.2⟩
  invFun 𝔔 := ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.1⟩, 𝔔.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Planning source: ZetaProduct.lean:2641; source-local planning contract. -/
theorem tprod_unramified_eq_prod_artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {s : ℂ} (hs : 1 < s.re) :
    (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))},
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹)
      = ∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s := by
  classical
  set F : Ideal (𝓞 L) → ℂ := fun 𝔭 ↦ (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ with hF
  set G : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℂ :=
    fun c ↦ ∏' χ : galoisCharacter K L,
      (1 - (χ (frobeniusClass K L c.1).out : ℂ) * (Ideal.absNorm c.1 : ℂ) ^ (-s))⁻¹ with hG
  -- `Multipliable.subtype` is avoided: it whnf-explodes on the `Ideal (𝓞 L)` prime subtype.
  -- Restrict the *summable* norm via `Summable.subtype`, then rebuild multipliability.
  have hmulU : Multipliable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      UnramifiedIn K L (𝔓.under (𝓞 K))} ↦ F 𝔓.1 := by
    have hsumU : Summable ((fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} ↦
        ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖) ∘ (↑) :
        {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          UnramifiedIn K L (x.1.under (𝓞 K))} → ℝ) :=
      (summable_norm_primeIdeal_factor_sub_one L hs).subtype
        (fun 𝔓 ↦ UnramifiedIn K L (𝔓.1.under (𝓞 K)))
    have hmul1 : Multipliable fun 𝔓 : {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
        UnramifiedIn K L (x.1.under (𝓞 K))} ↦ F 𝔓.1.1 := by
      simpa [hF] using multipliable_one_add_of_summable
        (f := fun 𝔓 : {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
            UnramifiedIn K L (x.1.under (𝓞 K))} ↦
          (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ - 1) hsumU
    exact (Equiv.multipliable_iff (unramifiedFlattenEquiv K L).symm).mpr hmul1
  have hfibHasProd : ∀ c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      HasProd (fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP K L 𝔓 = c} ↦ F 𝔓.1.1) (G c) := by
    intro c
    haveI : c.1.IsPrime := c.2.1
    haveI : c.1.IsMaximal := c.2.1.isMaximal (UnramifiedIn.ne_bot K L c.2.2)
    haveI : Finite (c.1.primesOver (𝓞 L)) :=
      (IsDedekindDomain.primesOver_finite c.1 (𝓞 L)).to_subtype
    haveI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} :=
      Finite.of_injective
        (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} ↦
          (⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩ : c.1.primesOver (𝓞 L)))
        (fun _ _ hab ↦ Subtype.ext (by simpa using hab))
    haveI : Finite {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
        UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP K L 𝔓 = c} :=
      Finite.of_equiv _ (fiberUnderEquiv K L c).symm
    have hval : (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP K L 𝔓 = c}, F 𝔓.1.1) = G c := by
      simp only [hG]
      rw [← dedekindZeta_local_factor_eq_product_artin_local K L c.1 c.2.2 s hs,
        ← (fiberUnderEquiv K L c).tprod_eq
          (fun 𝔔 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} ↦ F 𝔔.1)]
      rfl
    rw [← hval]
    exact (Multipliable.of_finite).hasProd
  have hsig : HasProd G (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      UnramifiedIn K L (𝔓.under (𝓞 K))}, F 𝔓.1) :=
    ((Equiv.sigmaFiberEquiv (underUP K L)).hasProd_iff.mpr hmulU.hasProd).sigma hfibHasProd
  rw [← hsig.tprod_eq]
  simp only [hG]
  haveI : Fintype (galoisCharacter K L) := Fintype.ofFinite _
  simp_rw [tprod_fintype]
  rw [Multipliable.tprod_finsetProd (s := (Finset.univ : Finset (galoisCharacter K L)))
    (f := fun χ : galoisCharacter K L ↦
      fun c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
        (1 - (χ (frobeniusClass K L c.1).out : ℂ) * (Ideal.absNorm c.1 : ℂ) ^ (-s))⁻¹)
    (fun χ _ ↦ multipliable_artinLocalFactor K L χ hs)]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [artinDirichletSeries, ← exists_artinLSeries_eulerProduct_abelian K L χ s hs]

/-- Planning source: ZetaProduct.lean:2739; source-local planning contract. -/
theorem tprod_unramifiedNested_eq_prod_artin
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {s : ℂ} (hs : 1 < s.re) :
    (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
        UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹)
      = ∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s := by
  rw [← tprod_unramified_eq_prod_artinDirichletSeries K L hs]
  exact Equiv.tprod_eq (unramifiedFlattenEquiv K L)
    (fun 𝔔 ↦ (1 - (Ideal.absNorm 𝔔.1 : ℂ) ^ (-s))⁻¹)

/-- Planning source: ZetaProduct.lean:2752; source-local planning contract. -/
theorem tprod_ramifiedNested_eq_ramified
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {s : ℂ} :
    (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
        ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹)
      = ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
            ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ :=
  Equiv.tprod_eq (ramifiedFlattenEquiv K L) fun 𝔔 ↦ (1 - (Ideal.absNorm 𝔔.1 : ℂ) ^ (-s))⁻¹

/-- Planning source: ZetaProduct.lean:2771; source-local planning contract. -/
theorem dedekindZeta_eq_prod_artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      (∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s) *
        ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
            ¬ UnramifiedIn K L (𝔓.under (𝓞 K))},
          (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ := by
  rw [dedekindZeta_eq_unramifiedNested_mul_ramifiedNested K L hs,
    tprod_unramifiedNested_eq_prod_artin K L hs, tprod_ramifiedNested_eq_ramified K L]

/-- Exactly one nonzero ideal has norm one (AINTLIB NumberFieldEulerProduct.lean:55). -/
theorem idealNormMultiplicity_one (L : Type*) [Field L] [NumberField L] :
    idealNormMultiplicity L 1 = 1 := by
  unfold idealNormMultiplicity
  have : Unique {I : NonzeroIdeal L // Ideal.absNorm I.1 = 1} :=
    { default := ⟨⟨⊤, by simp⟩, Ideal.absNorm_top⟩
      uniq := fun ⟨⟨I, hI⟩, hnorm⟩ ↦
        Subtype.ext (Subtype.ext (Ideal.absNorm_eq_one_iff.mp hnorm)) }
  exact Nat.card_unique

/-- Planning source: NumberFieldEulerProduct.lean:817; source-local planning contract. -/
theorem dedekindZeta_re_pos_of_one_lt (L : Type*) [Field L] [NumberField L] (s : ℝ) (hs : 1 < s) :
    0 < (NumberField.dedekindZeta L (s : ℂ)).re := by
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  set g : ℕ → ℝ := fun n ↦ (idealNormMultiplicity L n : ℝ) * (n : ℝ) ^ (-s) with hg
  have key : ∀ n : ℕ,
      (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) = ((g n : ℝ) : ℂ) := by
    intro n
    have hcast : ((n : ℝ) ^ (-s) : ℝ) = ((n : ℂ) ^ (-(s : ℂ))) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)]
      norm_cast
    rw [hg]
    push_cast [hcast]
    ring
  have hsumC : Summable
      fun n : ℕ ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
    (summable_idealNormMultiplicity_mul_cpow_neg L hs').of_norm
  have hsumR : Summable g := Complex.summable_ofReal.mp (by simpa only [key] using hsumC)
  have hre : (NumberField.dedekindZeta L (s : ℂ)).re = ∑' n : ℕ, g n := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs']
    simp_rw [key]
    rw [Complex.re_tsum (by simpa only [key] using hsumC)]
    simp
  rw [hre]
  refine hsumR.tsum_pos (fun n ↦ ?_) 1 ?_
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · rw [hg]
    simp [idealNormMultiplicity_one]

/-- Planning source: ZetaProduct.lean:3083; source-local planning contract. -/
theorem artinDirichletSeries_ne_zero_of_one_lt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L) {s : ℝ}
    (hs : 1 < s) : artinDirichletSeries K L χ (s : ℂ) ≠ 0 := by
  haveI : Fintype (galoisCharacter K L) := Fintype.ofFinite _
  intro hzero
  have hpos : 0 < (NumberField.dedekindZeta L (s : ℂ)).re := dedekindZeta_re_pos_of_one_lt L s hs
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  rw [show NumberField.dedekindZeta L (s : ℂ) = 0 by
    rw [dedekindZeta_eq_prod_artinDirichletSeries K L hs', tprod_fintype,
      Finset.prod_eq_zero (Finset.mem_univ χ) hzero, zero_mul], Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- Planning source: ZetaProduct.lean:2380; source-local planning contract. -/
theorem analytic_log_norm_le_of_apply_eq_zero {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 1) (hf0 : f 1 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (1 : ℂ), f z = 0) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖f (s : ℂ)‖ ≤ -Real.log (1 / (s - 1)) + C := by
  obtain ⟨n, g, hg_an, hg_ne, hg_eq⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hf).mpr hne
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · refine absurd ?_ hg_ne
      have := hg_eq.self_of_nhds
      rw [pow_zero, one_smul] at this
      rw [← this, hf0]
    · exact h
  have hg_cont : ContinuousAt g 1 := hg_an.continuousAt
  have hCg : ∀ᶠ z in 𝓝 (1 : ℂ), ‖g z‖ ≤ ‖g 1‖ + 1 := by
    filter_upwards [hg_cont.norm.eventually (Metric.ball_mem_nhds ‖g 1‖ one_pos)] with z hz
    rw [Real.dist_eq] at hz
    linarith [(abs_lt.mp hz).2]
  have hg0 : ∀ᶠ z in 𝓝 (1 : ℂ), g z ≠ 0 := hg_cont.eventually_ne hg_ne
  refine ⟨‖g 1‖ + 1, ?_⟩
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
  have hIoo : Set.Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hmap.eventually hg_eq, hmap.eventually hCg, hmap.eventually hg0, hIoo]
    with s hfeq hgle hgne hsmem
  obtain ⟨hs1, hs2⟩ := hsmem
  have hpos : (0 : ℝ) < s - 1 := by linarith
  have hlt1 : s - 1 < 1 := by linarith
  have hgpos : (0 : ℝ) < ‖g (s : ℂ)‖ := norm_pos_iff.mpr hgne
  have hnorm : ‖f (s : ℂ)‖ = (s - 1) ^ n * ‖g (s : ℂ)‖ := by
    rw [hfeq, norm_smul, norm_pow]
    congr 2
    rw [show ((s : ℂ) - 1) = (((s - 1 : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg hpos.le]
  rw [hnorm, Real.log_mul (by positivity) hgpos.ne', Real.log_pow]
  have hlog_neg : Real.log (s - 1) < 0 := Real.log_neg hpos hlt1
  have hn_ge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn_step : (n : ℝ) * Real.log (s - 1) ≤ Real.log (s - 1) := by
    nlinarith [hn_ge, hlog_neg]
  have hloginv : -Real.log (1 / (s - 1)) = Real.log (s - 1) := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [hloginv]
  have hgle' : Real.log ‖g (s : ℂ)‖ ≤ ‖g 1‖ + 1 := by
    calc Real.log ‖g (s : ℂ)‖ ≤ Real.log (‖g 1‖ + 1) :=
          Real.log_le_log hgpos hgle
      _ ≤ ‖g 1‖ + 1 := Real.log_le_self (by positivity)
  linarith

/-- Planning source: ZetaProduct.lean:2973; source-local planning contract. -/
theorem log_norm_artinDirichletSeries_one_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [_hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C, hC⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hCs hs1
  simp only [mem_Ioi] at hs1
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs1
  have hζ := hasSum_nonzeroIdeal_absNorm_cpow K hs'
  have hnorm_eq : ∀ 𝔞 : NonzeroIdeal K,
      ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ = ((Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))).re := by
    intro 𝔞
    have hpos : 0 < Ideal.absNorm 𝔞.1 :=
      Nat.pos_of_ne_zero fun h ↦ 𝔞.2 (Ideal.absNorm_eq_zero_iff.mp h)
    have hcast : (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ)) =
        (((Ideal.absNorm 𝔞.1 : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast]; norm_cast
    rw [hcast, Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg (by positivity)]
  have hsum_norm : Summable fun 𝔞 : NonzeroIdeal K ↦ ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ :=
    hζ.summable.norm
  have hsum_norm_eq : (∑' 𝔞 : NonzeroIdeal K, ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖)
      = (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [tsum_congr hnorm_eq, ← Complex.re_tsum hζ.summable, hζ.tsum_eq]
  have hterm : ∀ 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
      ‖galoisCharacterOnIdeal K L 1 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ ≤
        ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := by
    intro 𝔞
    rw [norm_mul]
    calc ‖galoisCharacterOnIdeal K L 1 𝔞.1‖ * ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖
        ≤ 1 * ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := by
          gcongr; exact norm_galoisCharacterOnIdeal_le_one K L 1 𝔞.1
      _ = ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := one_mul _
  have hsum_term : Summable fun 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥} ↦
      ‖galoisCharacterOnIdeal K L 1 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ :=
    hsum_norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
  have hL1_le : ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤ (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [artinDirichletSeries]
    refine (norm_tsum_le_tsum_norm hsum_term).trans ?_
    rw [← hsum_norm_eq]
    exact Summable.tsum_le_tsum hterm hsum_term hsum_norm
  have hζ_ge1 : (1 : ℝ) ≤ (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [← hsum_norm_eq]
    refine le_trans ?_ (hsum_norm.le_tsum (⟨⊤, by simp⟩ : NonzeroIdeal K) fun 𝔞 _ ↦ norm_nonneg _)
    rw [Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow, norm_one]
  have hlog_le : Real.log ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤
      Real.log (NumberField.dedekindZeta K (s : ℂ)).re := by
    rcases eq_or_lt_of_le (norm_nonneg (artinDirichletSeries K L 1 (s : ℂ))) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg hζ_ge1
    · exact Real.log_le_log h0 hL1_le
  exact hlog_le.trans (by linarith [abs_le.mp hCs])

/-- Planning source: ZetaProduct.lean:2942; source-local planning contract. -/
theorem artinDirichletSeries_norm_le_of_ne_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ' : galoisCharacter K L) (hχ' : χ' ≠ 1) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤ C := by
  obtain ⟨Lf', hLf'_an, hLf'_eq⟩ := artinLSeries_analytic_extension K L m hm χ' hχ'
  have hcont : ContinuousAt Lf' 1 :=
    (analyticAt_one_of_analyticOn_finrankDomain K hLf'_an).continuousAt
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
  have hbdd : ∀ᶠ z in 𝓝 (1 : ℂ), ‖Lf' z‖ ≤ ‖Lf' 1‖ + 1 := by
    filter_upwards [hcont.norm.eventually (Metric.ball_mem_nhds ‖Lf' 1‖ one_pos)] with z hz
    rw [Real.dist_eq] at hz
    linarith [(abs_lt.mp hz).2]
  refine ⟨‖Lf' 1‖ + 1, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hmap.eventually hbdd] with s hs1 hbdd_s
  simp only [mem_Ioi] at hs1
  have heq : artinDirichletSeries K L χ' (s : ℂ) = Lf' (s : ℂ) := by
    rw [artinDirichletSeries, ← hLf'_eq (s : ℂ) (by simpa using hs1)]
  rwa [heq]

open scoped Classical in
/-- Planning source: ZetaProduct.lean:3049; source-local planning contract. -/
theorem log_norm_artinDirichletSeries_le_pole_zero_ite
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) {χ : galoisCharacter K L} {Cχ : ℝ}
    (hCχ : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖ ≤ -Real.log (1 / (s - 1)) + Cχ)
    (χ' : galoisCharacter K L) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤
        (if χ' = 1 then Real.log (1 / (s - 1)) else
          if χ' = χ then -Real.log (1 / (s - 1)) else 0) + C := by
  by_cases h1 : χ' = 1
  · subst h1
    obtain ⟨C1, hC1⟩ := log_norm_artinDirichletSeries_one_le K L
    exact ⟨C1, by filter_upwards [hC1] with s hs; rwa [if_pos rfl]⟩
  · by_cases hc : χ' = χ
    · subst hc
      exact ⟨Cχ, by filter_upwards [hCχ] with s hs; rwa [if_neg h1, if_pos rfl]⟩
    · obtain ⟨C, hC⟩ := artinDirichletSeries_norm_le_of_ne_one K L m hm χ' h1
      refine ⟨Real.log (max C 1), ?_⟩
      filter_upwards [hC] with s hs
      simp only [if_neg h1, if_neg hc, zero_add]
      have hmax1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
      rcases le_total ‖artinDirichletSeries K L χ' (s : ℂ)‖ 0 with h0 | h0
      · have hz : ‖artinDirichletSeries K L χ' (s : ℂ)‖ = 0 := le_antisymm h0 (norm_nonneg _)
        rw [hz, Real.log_zero]
        exact Real.log_nonneg hmax1
      · rcases eq_or_lt_of_le h0 with h0' | h0'
        · rw [← h0', Real.log_zero]; exact Real.log_nonneg hmax1
        · exact Real.log_le_log h0' (le_trans hs (le_max_left _ _))

/-- Planning source: ZetaProduct.lean:2784; source-local planning contract. -/
theorem finite_ramifiedAbove
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} := by
  classical
  haveI : Finite {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭} :=
    (finite_ramifiedIn K L).to_subtype
  haveI : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭},
      Finite (𝔭.1.primesOver (𝓞 L)) := fun 𝔭 ↦ by
    haveI : 𝔭.1.IsPrime := 𝔭.2.1
    haveI : 𝔭.1.IsMaximal := 𝔭.2.1.isMaximal 𝔭.2.2.1
    exact (IsDedekindDomain.primesOver_finite 𝔭.1 (𝓞 L)).to_subtype
  refine Finite.of_injective
    (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} ↦
      (show Σ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭},
          𝔭.1.primesOver (𝓞 L) by
        haveI := 𝔓.2.1
        exact ⟨⟨𝔓.1.under (𝓞 K), inferInstance, Ideal.under_ne_bot (A := 𝓞 K) 𝔓.2.2.1, 𝔓.2.2.2⟩,
          ⟨𝔓.1, 𝔓.2.1, Ideal.over_under (A := 𝓞 K) (P := 𝔓.1)⟩⟩))
    (fun a b hab ↦ Subtype.ext (by simpa using congrArg (fun x ↦ (x.2 : Ideal (𝓞 L))) hab))

/-- Planning source: ZetaProduct.lean:2828; source-local planning contract. -/
theorem log_norm_ramified_factor_bounded
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [_hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log ‖∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹‖| ≤
        C := by
  classical
  haveI : Fintype {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} :=
    haveI := finite_ramifiedAbove K L
    Fintype.ofFinite _
  set R : ℝ → ℂ := fun s ↦ ∏ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹ with hR
  have hbase : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (Ideal.absNorm 𝔓.1 : ℂ) ≠ 0 := fun 𝔓 ↦ by
    have hne0 : Ideal.absNorm 𝔓.1 ≠ 0 := fun h ↦ 𝔓.2.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast hne0
  have hden1 : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(1 : ℂ))) ≠ 0 :=
    fun 𝔓 ↦ by
    have h2 : 2 ≤ Ideal.absNorm 𝔓.1 := two_le_absNorm 𝔓.2.1 𝔓.2.2.1
    have hlt : ‖(Ideal.absNorm 𝔓.1 : ℂ) ^ (-(1 : ℂ))‖ < 1 := by
      rw [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < Ideal.absNorm 𝔓.1))
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hcont : ContinuousAt R 1 := by
    rw [ContinuousAt, hR]
    refine tendsto_finsetProd _ fun 𝔓 _ ↦ ?_
    have hcpow : ContinuousAt (fun s : ℝ ↦ (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ))) 1 :=
      (continuousAt_const_cpow (hbase 𝔓)).comp Complex.continuous_ofReal.continuousAt.neg
    exact (continuousAt_const.sub hcpow).inv₀ (by simpa using hden1 𝔓)
  have hR1_ne : R 1 ≠ 0 :=
    hR ▸ Finset.prod_ne_zero_iff.mpr fun 𝔓 _ ↦ inv_ne_zero (by simpa using hden1 𝔓)
  have hlogcont : ContinuousAt (fun s : ℝ ↦ Real.log ‖R s‖) 1 :=
    hcont.norm.log (norm_ne_zero_iff.mpr hR1_ne)
  refine ⟨|Real.log ‖R 1‖| + 1, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝 (1 : ℝ),
      |Real.log ‖R s‖ - Real.log ‖R 1‖| ≤ 1 := by
    filter_upwards [hlogcont (Metric.closedBall_mem_nhds (Real.log ‖R 1‖) one_pos)] with s hs
    simpa only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq] using hs
  filter_upwards [nhdsWithin_le_nhds hev] with s hs
  rw [show (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹) = R s
    by rw [hR]; exact tprod_fintype _]
  have htri : |Real.log ‖R s‖| ≤ |Real.log ‖R s‖ - Real.log ‖R 1‖| + |Real.log ‖R 1‖| := by
    simpa using abs_add_le (Real.log ‖R s‖ - Real.log ‖R 1‖) (Real.log ‖R 1‖)
  linarith

/-- Planning source: ZetaProduct.lean:2807; source-local planning contract. -/
theorem dedekindZeta_eq_ofReal_re
    (L : Type*) [Field L] [NumberField L] {s : ℝ} (hs : 1 < s) :
    NumberField.dedekindZeta L (s : ℂ) = ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) := by
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  set g : ℕ → ℝ := fun n ↦ (idealNormMultiplicity L n : ℝ) * (n : ℝ) ^ (-s) with hg
  have key : ∀ n : ℕ,
      (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) = ((g n : ℝ) : ℂ) := by
    intro n
    have hcast : ((n : ℝ) ^ (-s) : ℝ) = ((n : ℂ) ^ (-(s : ℂ))) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)]; norm_cast
    rw [hg]; push_cast [hcast]; ring
  have hval : NumberField.dedekindZeta L (s : ℂ) = ((∑' n, g n : ℝ) : ℂ) := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs', Complex.ofReal_tsum]
    exact tsum_congr key
  rw [hval, Complex.ofReal_re]

/-- Planning source: ZetaProduct.lean:2885; source-local planning contract. -/
theorem log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [Fintype (galoisCharacter K L)] [hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log (NumberField.dedekindZeta L (s : ℂ)).re -
        ∑ χ : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖| ≤ C := by
  obtain ⟨C, hC⟩ := log_norm_ramified_factor_bounded K L
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hCs hs1
  simp only [mem_Ioi] at hs1
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs1
  have hpos : 0 < (NumberField.dedekindZeta L (s : ℂ)).re :=
    dedekindZeta_re_pos_of_one_lt L s hs1
  have hfact : NumberField.dedekindZeta L (s : ℂ) =
      (∏ χ : galoisCharacter K L, artinDirichletSeries K L χ (s : ℂ)) *
        ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
            ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹ := by
    rw [dedekindZeta_eq_prod_artinDirichletSeries K L hs', tprod_fintype]
  have hnorm : ‖NumberField.dedekindZeta L (s : ℂ)‖ = (NumberField.dedekindZeta L (s : ℂ)).re := by
    rw [dedekindZeta_eq_ofReal_re L hs1, Complex.norm_real, Real.norm_of_nonneg hpos.le,
      Complex.ofReal_re]
  have hprodχ_ne : (∏ χ : galoisCharacter K L, artinDirichletSeries K L χ (s : ℂ)) ≠ 0 := fun h0 ↦
    hpos.ne' (by rw [hfact, h0, zero_mul, Complex.zero_re])
  have hR_ne : (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹) ≠ 0 :=
    fun h0 ↦ hpos.ne' (by rw [hfact, h0, mul_zero, Complex.zero_re])
  have hχ_ne : ∀ χ ∈ (Finset.univ : Finset (galoisCharacter K L)),
      ‖artinDirichletSeries K L χ (s : ℂ)‖ ≠ 0 := fun χ _ ↦
    norm_ne_zero_iff.mpr fun hχ0 ↦ hprodχ_ne (Finset.prod_eq_zero (Finset.mem_univ χ) hχ0)
  have hsplit : Real.log (NumberField.dedekindZeta L (s : ℂ)).re =
      (∑ χ : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖) +
        Real.log ‖∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹‖ := by
    rw [← hnorm, hfact, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hprodχ_ne) (norm_ne_zero_iff.mpr hR_ne),
      norm_prod, Real.log_prod hχ_ne]
  rw [hsplit]
  simpa using hCs

open scoped Classical in
/-- Planning source: ZetaProduct.lean:3028; source-local planning contract. -/
theorem sum_ite_pole_zero_cancel
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [Fintype (galoisCharacter K L)] {χ : galoisCharacter K L}
    (hχ : χ ≠ 1) (a : ℝ) :
    ∑ χ' : galoisCharacter K L, (if χ' = 1 then a else if χ' = χ then -a else 0) = 0 := by
  have hsplit : ∀ χ' : galoisCharacter K L,
      (if χ' = 1 then a else if χ' = χ then -a else 0) =
        (if χ' = 1 then a else 0) + (if χ' = χ then -a else 0) := fun χ' ↦ by
    by_cases h1 : χ' = 1
    · rw [if_pos h1, if_pos h1, if_neg (h1 ▸ Ne.symm hχ), add_zero]
    · rw [if_neg h1, if_neg h1]; by_cases hc : χ' = χ <;> simp [hc]
  rw [Finset.sum_congr rfl fun χ' _ ↦ hsplit χ', Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (1 : galoisCharacter K L), Finset.sum_ite_eq' Finset.univ χ]
  simp

/-- Planning source: ZetaProduct.lean:2362; source-local planning contract. -/
theorem logDedekindZeta_re_tendsto_atTop
    (L : Type*) [Field L] [NumberField L] :
    Tendsto (fun s : ℝ ↦ Real.log (NumberField.dedekindZeta L (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) atTop := by
  obtain ⟨C, hC⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded L
  have hlog : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1)) + -C) (𝓝[>] (1 : ℝ)) atTop :=
    tendsto_log_one_div_sub_one_atTop.atTop_add tendsto_const_nhds
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [hC] with s hs
  linarith [(abs_le.mp hs).1]

open scoped Classical in
/-- Planning source: ZetaProduct.lean:3101; source-local planning contract. -/
theorem false_of_eventually_log_norm_le_pole_zero_ite
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)]
    {χ : galoisCharacter K L} (hχ : χ ≠ 1)
    {C : galoisCharacter K L → ℝ} (hC : ∀ χ' : galoisCharacter K L, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤
        (if χ' = 1 then Real.log (1 / (s - 1)) else
          if χ' = χ then -Real.log (1 / (s - 1)) else 0) + C χ') : False := by
  haveI : Fintype (galoisCharacter K L) := Fintype.ofFinite _
  obtain ⟨CR, hCR⟩ := log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded K L
  have hbound : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log (NumberField.dedekindZeta L (s : ℂ)).re ≤ (∑ χ', C χ') + CR := by
    filter_upwards [Filter.eventually_all.2 hC, hCR] with s hs_all hCRs
    have hsumle : ∑ χ' : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖
        ≤ ∑ χ', C χ' := by
      calc ∑ χ' : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖
          ≤ ∑ χ' : galoisCharacter K L,
              ((if χ' = 1 then Real.log (1 / (s - 1)) else
                if χ' = χ then -Real.log (1 / (s - 1)) else 0) + C χ') :=
            Finset.sum_le_sum fun χ' _ ↦ hs_all χ'
        _ = ∑ χ' : galoisCharacter K L, C χ' := by
            rw [Finset.sum_add_distrib, sum_ite_pole_zero_cancel K L hχ (Real.log (1 / (s - 1))),
              zero_add]
    have := abs_le.mp hCRs
    linarith [this.1, this.2]
  obtain ⟨s, hge, hle⟩ :=
    (((logDedekindZeta_re_tendsto_atTop L).eventually_ge_atTop ((∑ χ', C χ') + CR + 1)).and
      hbound).exists
  linarith

/-- Planning source: ZetaProduct.lean:3143; source-local planning contract. -/
theorem artinLSeries_one_ne_zero
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∀ Lf : ℂ → ℂ,
      AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} →
      (∀ s : ℂ, 1 < s.re →
        Lf s = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
          galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) →
      Lf 1 ≠ 0 := by
  classical
  intro Lf hLf_an hLf_eq hLf0
  have hLf_eq' : ∀ s : ℂ, 1 < s.re → Lf s = artinDirichletSeries K L χ s :=
    fun s hs ↦ by rw [hLf_eq s hs, artinDirichletSeries]
  have hLf_at : AnalyticAt ℂ Lf 1 := analyticAt_one_of_analyticOn_finrankDomain K hLf_an
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
  have hLf_ne : ¬ ∀ᶠ z in 𝓝 (1 : ℂ), Lf z = 0 := by
    intro hloc
    obtain ⟨s, hs0, hs1⟩ : ∃ s : ℝ, Lf (s : ℂ) = 0 ∧ 1 < s :=
      ((hmap.eventually hloc).and self_mem_nhdsWithin).exists
    exact artinDirichletSeries_ne_zero_of_one_lt K L χ hs1
      (by rw [← hLf_eq' _ (by simpa using hs1), hs0])
  obtain ⟨Cχ, hCχ⟩ := analytic_log_norm_le_of_apply_eq_zero hLf_at hLf0 hLf_ne
  have hCχ' : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖ ≤ -Real.log (1 / (s - 1)) + Cχ := by
    filter_upwards [hCχ, self_mem_nhdsWithin] with s hs hs1
    simp only [mem_Ioi] at hs1
    rwa [← hLf_eq' (s : ℂ) (by simpa using hs1)]
  choose C hC using log_norm_artinDirichletSeries_le_pole_zero_ite K L m hm hCχ'
  exact false_of_eventually_log_norm_le_pole_zero_ite K L _hχ hC

end Cox.Chebotarev
