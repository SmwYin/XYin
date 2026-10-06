/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.Cox.Theorem11_1.ClassFieldDescent
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclicQuotients
import XYin.PhD.Cox.Theorem11_1.ClassFieldSUnitIndices
import XYin.PhD.Cox.Theorem11_1.ClassFieldPairedDefs
import XYin.PhD.Cox.Theorem11_1.ClassFieldPairedProjection
import XYin.PhD.Cox.Theorem11_1.ClassFieldRadicalSplitting
import XYin.PhD.Cox.Theorem11_1.ClassFieldSupportedRadicalUnramified
import XYin.PhD.Cox.Theorem11_1.ClassFieldCyclotomicCapture

/-!
# Janusz's paired construction and the existence theorem

Janusz, *Algebraic Number Fields*, V.9. For disjoint supports `S`, `T` covering the primes
above `n` and representatives of the ideal classes, the paired radical fields are class
fields to the paired subgroups once both moduli are deep enough (V.9.1): each subgroup lies
in its Artin kernel, and the paired index identity with the local power-index product forces
equality. With the opposite support empty this gives existence when `K` contains the `n`th
roots of unity; cyclotomic base change and repeated cyclic descent (V.7) remove that
hypothesis. The conductor of an ideal group is itself a defining modulus (V.6.2).
-/

open NumberField IsDedekindDomain
open NumberField.InfinitePlace
open scoped nonZeroDivisors

noncomputable section

namespace Cox.ClassFieldTheory

variable (K : Type*) [Field K] [NumberField K]

/-- The radical quotient in the paired construction is finite. -/
theorem pairedRadicands_finiteQuotient (n : ℕ) (hn : 0 < n)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (m : Ideal (𝓞 K)) :
    Finite ((pairedRadicands K n S m) ⧸
      (nthPowers K n).subgroupOf (pairedRadicands K n S m)) := by
  haveI := sUnits_finiteQuotient K S n hn
  have h1 : (nthPowers K n).relIndex (sUnits K S) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : (nthPowers K n).relIndex (sUnits K S ⊔ nthPowers K n) ≠ 0 := by
    rw [sup_comm, Subgroup.relIndex_sup_left]
    exact h1
  have h3 : (nthPowers K n).relIndex (pairedRadicands K n S m) ≠ 0 := by
    have h := Subgroup.relIndex_inter_ne_zero h2 (rayElements K m)
    have he : (nthPowers K n ⊓ rayElements K m).subgroupOf (pairedRadicands K n S m) =
        (nthPowers K n).subgroupOf (pairedRadicands K n S m) := by
      ext x
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2.2⟩⟩
    rw [Subgroup.relIndex, ← he]
    exact h
  haveI : ((nthPowers K n).subgroupOf (pairedRadicands K n S m)).FiniteIndex := ⟨h3⟩
  infer_instance

/-- Janusz V.9.2: a deep opposite congruence makes those primes split in the radical field. -/
theorem pairedRadicalField_splits_opposite (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ v ∈ T,
      v.asIdeal ∈ splittingIdeals K
        (radicalField K n (pairedRadicands K n S (supportModulus K T t))) := by
  obtain ⟨t₀, ht₀⟩ := eventually_ray_local_nthPowers K n hn T
  refine ⟨t₀, fun t ht v hv => ?_⟩
  haveI := pairedRadicands_finiteQuotient K n hn S (supportModulus K T t)
  exact radicalField_splits_of_local_nthPowers K n hn ζ hζ _ v fun a ha => ht₀ t ht v hv a ha.2

/-- Janusz V.9.3: separable residue radical polynomials and opposite splitting confine
ramification to the chosen support. -/
theorem pairedRadicalField_unramified (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (hcover : CoversNthPrimes K n (S.disjUnion T hdisj)) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀,
      IsUnramifiedAway K (supportModulus K S 1)
        (radicalField K n
          (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t))) := by
  obtain ⟨t₀, ht₀⟩ := pairedRadicalField_splits_opposite K n hn ζ hζ (S.disjUnion T hdisj) T
  refine ⟨t₀, fun t ht q hq hq0 hqm P hP => ?_⟩
  let v : HeightOneSpectrum (𝓞 K) := ⟨q, hq, hq0⟩
  have hvS : v ∉ S := by
    intro hvS
    have hle : supportModulus K S 1 ≤ q := (supportModulus_le_prime_iff K S 1 one_pos v).mpr hvS
    rw [sup_eq_left.mpr hle] at hqm
    exact hq.ne_top hqm
  by_cases hvT : v ∈ T
  · exact ((ht₀ t ht v hvT).2.2 P hP).1
  · haveI := pairedRadicands_finiteQuotient K n hn (S.disjUnion T hdisj) (supportModulus K T t)
    haveI := radicalField_finiteDimensional K n hn
      (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t))
    haveI : NumberField (radicalField K n
      (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t))) :=
      NumberField.of_module_finite K _
    obtain ⟨hPp, hPo⟩ := hP
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq0 P
    let w : HeightOneSpectrum (𝓞 (radicalField K n
      (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t)))) := ⟨P, hPp, hP0⟩
    haveI : w.asIdeal.LiesOver v.asIdeal := hPo
    have hv : v ∉ S.disjUnion T hdisj := by
      rw [Finset.mem_disjUnion]
      exact fun h => h.elim hvS hvT
    exact supported_radicalField_ramificationIdx_eq_one K (S.disjUnion T hdisj) n hcover
      (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t)) inf_le_left v hv w

/-- Janusz V.5.7 with its specified support: sufficiently high powers of any support
containing the ramified primes suffice for reciprocity. -/
theorem artin_reciprocity_supported [IsTotallyComplex K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hU : IsUnramifiedAway K (supportModulus K S 1) L) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, IsReciprocityLaw K (supportModulus K S t) L := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  obtain ⟨ι, hι, E, hcyc, hbot⟩ := exists_cyclic_subfields_iInf_fixing_eq_bot K L
  haveI : ∀ i, IsAbelianGalois K (E i) := fun i => IsAbelianGalois.tower_bot K (E i) L
  have hthr : ∀ i, ∃ c : ℕ, ∀ t ≥ c,
      (normRaySubgroup K (supportModulus K S t) (E i)).index = Module.finrank K (E i) := by
    intro i
    haveI := hcyc i
    exact cyclic_norm_index_supported K (E i) S (isUnramifiedAway_subfield K _ L (E i) hU)
  choose c hc using hthr
  refine ⟨max 1 (Finset.univ.sup c), fun t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have hm : supportModulus K S t ≠ ⊥ := supportModulus_ne_bot K S t
  have hUm : IsUnramifiedAway K (supportModulus K S t) L := fun q hq hq0 hqm =>
    hU q hq hq0 (eq_top_mono (sup_le_sup_left (supportModulus_antitone K S ht1) q) hqm)
  obtain ⟨φ, hφ, hsurj⟩ := exists_artinMap K _ L hm hUm
  refine ⟨φ, hφ, hsurj, fun u hu => ?_⟩
  rw [MonoidHom.mem_ker]
  have hall : φ u ∈ ⨅ i, (E i).fixingSubgroup := by
    rw [Subgroup.mem_iInf]
    intro i
    haveI := hcyc i
    have hUEi := isUnramifiedAway_subfield K _ L (E i) hUm
    have hidx := hc i t
      (le_trans (Finset.le_sup (Finset.mem_univ i)) (le_trans (le_max_right _ _) ht))
    obtain ⟨ψ, hψ, -, hψray⟩ := cyclic_reciprocity_of_index_eq K _ (E i) hm hUEi hidx
    have hres := isArtinMap_restrict K _ L (E i) φ hφ
    have heq := isArtinMap_unique K _ (E i) hUEi hψ hres
    have h1 : ψ u = 1 := hψray hu
    rw [heq, MonoidHom.comp_apply] at h1
    rw [← IntermediateField.restrictNormalHom_ker]
    exact h1
  rw [hbot] at hall
  exact Subgroup.mem_bot.mp hall

/-- Both radical fields lie in one fixed finite Kummer extension, so reciprocity depths
can be chosen uniformly over its finitely many intermediate fields. This avoids a
circular choice of the two opposite moduli. -/
theorem paired_uniform_reciprocity [IsTotallyComplex K]
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (hcover : CoversNthPrimes K n (S.disjUnion T hdisj)) :
    ∃ t₀ : ℕ, ∀ s ≥ t₀, ∀ t ≥ t₀,
      IsReciprocityLaw K (supportModulus K S s)
        (radicalField K n
          (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t))) := by
  classical
  haveI := sUnits_finiteQuotient K (S.disjUnion T hdisj) n hn
  haveI : FiniteDimensional K (radicalField K n (sUnits K (S.disjUnion T hdisj))) :=
    radicalField_finiteDimensional K n hn _
  haveI : IsAbelianGalois K (radicalField K n (sUnits K (S.disjUnion T hdisj))) :=
    radicalField_isAbelianGalois K n hn ζ hζ _
  haveI : Algebra.IsSeparable K (radicalField K n (sUnits K (S.disjUnion T hdisj))) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Finite (IntermediateField K (radicalField K n (sUnits K (S.disjUnion T hdisj)))) :=
    CyclotomicCapture.finite_intermediateFields_of_finite_separable K _
  have hfin := CyclotomicCapture.finite_subfields_le
    (radicalField K n (sUnits K (S.disjUnion T hdisj)))
  haveI : Fintype {F : IntermediateField K (AlgebraicClosure K) //
      F ≤ radicalField K n (sUnits K (S.disjUnion T hdisj))} := hfin.fintype
  have hc : ∀ F : {F : IntermediateField K (AlgebraicClosure K) //
      F ≤ radicalField K n (sUnits K (S.disjUnion T hdisj))}, ∃ c : ℕ,
        IsUnramifiedAway K (supportModulus K S 1) F.1 →
          ∀ s ≥ c, IsReciprocityLaw K (supportModulus K S s) F.1 := by
    intro F
    by_cases hU : IsUnramifiedAway K (supportModulus K S 1) F.1
    · haveI : FiniteDimensional K F.1 :=
        FiniteDimensional.of_injective (IntermediateField.inclusion F.2).toLinearMap
          (IntermediateField.inclusion F.2).injective
      haveI : NumberField F.1 := NumberField.of_module_finite K F.1
      haveI : IsAbelianGalois K F.1 := IsAbelianGalois.of_algHom (IntermediateField.inclusion F.2)
      obtain ⟨c, hc⟩ := artin_reciprocity_supported K F.1 S hU
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hU⟩
  choose c hc using hc
  obtain ⟨d, hd⟩ := pairedRadicalField_unramified K n hn ζ hζ S T hdisj hcover
  refine ⟨max (max 1 d) (Finset.univ.sup c), fun s hs t ht => ?_⟩
  have hFE : radicalField K n (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t)) ≤
      radicalField K n (sUnits K (S.disjUnion T hdisj)) :=
    radicalField_le_of_le_sup_nthPowers K n inf_le_left
  exact hc ⟨_, hFE⟩ (hd t (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht)) s
    (le_trans (Finset.le_sup (Finset.mem_univ _)) (le_trans (le_max_right _ _) hs))

/-- Janusz V.(9.6): ray principals, nth powers and completely split opposite primes
all lie in the Artin kernel. -/
theorem pairedSubgroup_le_artin_ker
    (m : Ideal (𝓞 K)) (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (n : ℕ) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : coprimeIdeals K m →* (L ≃ₐ[K] L)) (hφ : IsArtinMap K m L φ)
    (hU : IsUnramifiedAway K m L) (hray : raySubgroup K m ≤ φ.ker)
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1)
    (hgood : ∀ v ∈ T, v.asIdeal ⊔ m = ⊤)
    (hsplit : ∀ v ∈ T, v.asIdeal ∈ splittingIdeals K L) :
    pairedSubgroup K n m T ≤ φ.ker := by
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  have hN := normImage_le_artin_ker K m L hU φ hφ
  refine sup_le (sup_le hray ?_) ?_
  · rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hexp]
  · have hT : supportedIdeals K T ≤ φ.ker.map (coprimeIdeals K m).subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro g ⟨v, hv, hgv⟩
      have hgm : g ∈ coprimeIdeals K m :=
        Subgroup.subset_closure ⟨v.asIdeal, v.ne_bot, hgood v hv, hgv⟩
      exact ⟨⟨g, hgm⟩, hN (mem_normImage_of_splits K m L (hsplit v hv) (hgood v hv) ⟨g, hgm⟩ hgv),
        rfl⟩
    intro u hu
    obtain ⟨k, hk, hku⟩ := hT hu
    have hk' : k = u := Subtype.ext hku
    rw [← hk']
    exact hk

-- The unused hypotheses are kept: the planned signature includes them.
set_option linter.unusedVariables false in
/-- Janusz V.9.8: pass to ideals avoiding both finite supports by change of modulus. -/
theorem paired_quotient_restrict (n : ℕ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    let m := supportModulus K S s
    let m' := m * supportModulus K T t
    Nonempty ((coprimeIdeals K m ⧸ pairedSubgroup K n m T) ≃*
      (coprimeIdeals K m' ⧸
        ((pairedSubgroup K n m T).map (coprimeIdeals K m).subtype).comap
          (coprimeIdeals K m').subtype)) := by
  intro m m'
  have hm0 : m ≠ ⊥ := supportModulus_ne_bot K S s
  have hm'0 : m' ≠ ⊥ := mul_ne_zero hm0 (supportModulus_ne_bot K T t)
  have hle : m' ≤ m := Ideal.mul_le_right
  have hray : raySubgroup K m' ≤ ((pairedSubgroup K n m T).map
      (coprimeIdeals K m).subtype).comap (coprimeIdeals K m').subtype := by
    intro u hu
    have hu' : (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ Subgroup.closure (rayGenerators K m) :=
      Subgroup.closure_mono (rayGenerators_mono K hle) hu
    have huI : (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ coprimeIdeals K m :=
      (Subgroup.closure_le _).mpr (rayGenerators_mem_coprimeIdeals K m) hu'
    have hle' : raySubgroup K m ≤ pairedSubgroup K n m T := le_sup_left.trans le_sup_left
    exact ⟨⟨u, huI⟩, hle' (show (⟨u, huI⟩ : coprimeIdeals K m) ∈ raySubgroup K m from hu'), rfl⟩
  let J : CongruenceSubgroup K :=
    ⟨m, hm0, pairedSubgroup K n m T, le_sup_left.trans le_sup_left⟩
  let H' : CongruenceSubgroup K :=
    ⟨m', hm'0, ((pairedSubgroup K n m T).map (coprimeIdeals K m).subtype).comap
      (coprimeIdeals K m').subtype, hray⟩
  have hres : H'.ambient = J.ambient ⊓ coprimeIdeals K H'.modulus := by
    change (((pairedSubgroup K n m T).map (coprimeIdeals K m).subtype).comap
      (coprimeIdeals K m').subtype).map (coprimeIdeals K m').subtype =
        (pairedSubgroup K n m T).map (coprimeIdeals K m).subtype ⊓ coprimeIdeals K m'
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  obtain ⟨e⟩ := congruence_quotient_equiv K H' J hle hres
  exact ⟨e.symm⟩

/-- Janusz V.9.9: principal ideals after erasing supported factors identify the field-unit
power/congruence quotient with the restricted ideal quotient. -/
theorem principal_quotient_equiv_awayIdeals (n : ℕ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (hreps : SupportsClassRepresentatives K (S.disjUnion T hdisj))
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    let m := supportModulus K S s
    let m' := m * supportModulus K T t
    Nonempty ((Kˣ ⧸ (nthPowers K n ⊔ sUnits K (S.disjUnion T hdisj) ⊔ rayElements K m)) ≃*
      (coprimeIdeals K m' ⧸
        ((pairedSubgroup K n m T).map (coprimeIdeals K m).subtype).comap
          (coprimeIdeals K m').subtype)) := by
  intro m m'
  have hf : Function.Surjective ((eraseModulusFactors K m').comp (toPrincipalIdeal (𝓞 K) K)) :=
    erasePrincipal_surjective_of_classRepresentatives K (S.disjUnion T hdisj) hreps m'
      (modulusSupported_paired K S T hdisj s t hs ht)
  obtain ⟨e⟩ := quotientComapEquiv_of_surjective _ hf
    (((pairedSubgroup K n m T).map (coprimeIdeals K m).subtype).comap (coprimeIdeals K m').subtype)
  have hN : (((pairedSubgroup K n m T).map (coprimeIdeals K m).subtype).comap
      (coprimeIdeals K m').subtype).comap
        ((eraseModulusFactors K m').comp (toPrincipalIdeal (𝓞 K) K)) =
      nthPowers K n ⊔ sUnits K (S.disjUnion T hdisj) ⊔ rayElements K m := by
    apply le_antisymm
    · intro a ha
      exact erased_principal_preimage_le K n S T hdisj hreps s t hs ht a ha
    · exact le_erased_principal_preimage K n S T hdisj s t hs ht
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hN.symm).trans e⟩

/-- The two actual quotient equivalences identify the paired ideal index. -/
theorem pairedSubgroup_index_eq_fieldUnitIndex (n : ℕ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (hreps : SupportsClassRepresentatives K (S.disjUnion T hdisj))
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    (pairedSubgroup K n (supportModulus K S s) T).index =
      (nthPowers K n ⊔ sUnits K (S.disjUnion T hdisj) ⊔
        rayElements K (supportModulus K S s)).index := by
  obtain ⟨e₁⟩ := paired_quotient_restrict K n S T hdisj s t hs ht
  obtain ⟨e₂⟩ := principal_quotient_equiv_awayIdeals K n S T hdisj hreps s t hs ht
  exact (Nat.card_congr e₁.toEquiv).trans (Nat.card_congr e₂.toEquiv.symm)

/-- Janusz V.(9.11), with denominators cleared: the paired subgroup indices reduce
to the two local power-congruence indices. -/
theorem paired_index_identity [IsTotallyComplex K]
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (hreps : SupportsClassRepresentatives K (S.disjUnion T hdisj))
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    (pairedSubgroup K n (supportModulus K S s) T).index *
        (pairedSubgroup K n (supportModulus K T t) S).index *
        n ^ (2 * ((S.disjUnion T hdisj).card + nrComplexPlaces K)) =
      ((nthPowers K n).subgroupOf
        (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t))).index *
      ((nthPowers K n).subgroupOf
        (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K S s))).index *
      powerCongruenceIndex K n (supportModulus K S s) *
      powerCongruenceIndex K n (supportModulus K T t) := by
  have hidentity := power_ray_sUnit_index_identity K (S.disjUnion T hdisj) n hn ζ hζ
  have hTS : T.disjUnion S hdisj.symm = S.disjUnion T hdisj := by
    ext v
    simp only [Finset.mem_disjUnion, or_comm]
  have hiS := pairedSubgroup_index_eq_fieldUnitIndex K n S T hdisj hreps s t hs ht
  have hiT := pairedSubgroup_index_eq_fieldUnitIndex K n T S hdisj.symm
    (hTS.symm ▸ hreps) t s ht hs
  rw [hTS] at hiT
  have hS := hidentity (supportModulus K S s)
  have hT := hidentity (supportModulus K T t)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero K, add_zero, ← hiS] at hS
  rw [IsTotallyComplex.nrRealPlaces_eq_zero K, add_zero, ← hiT] at hT
  dsimp only [pairedRadicands]
  calc
    _ = ((pairedSubgroup K n (supportModulus K S s) T).index *
        n ^ ((S.disjUnion T hdisj).card + nrComplexPlaces K)) *
        ((pairedSubgroup K n (supportModulus K T t) S).index *
        n ^ ((S.disjUnion T hdisj).card + nrComplexPlaces K)) := by
      rw [two_mul, pow_add]
      ring
    _ = _ := by rw [hS, hT]; ac_rfl

/-- Equal products of finite indices force equality in each of two subgroup inclusions;
this is the final group-theoretic step of Janusz V.9.1. -/
theorem eq_of_le_of_index_mul_eq {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (H₁ J₁ : Subgroup G₁) (H₂ J₂ : Subgroup G₂)
    [H₁.FiniteIndex] [H₂.FiniteIndex] (h₁ : H₁ ≤ J₁) (h₂ : H₂ ≤ J₂)
    (hprod : H₁.index * H₂.index = J₁.index * J₂.index) : H₁ = J₁ := by
  haveI := Subgroup.finiteIndex_of_le h₁
  haveI := Subgroup.finiteIndex_of_le h₂
  have e₁ := Subgroup.relIndex_mul_index h₁
  have e₂ := Subgroup.relIndex_mul_index h₂
  have hJ : 0 < J₁.index * J₂.index :=
    Nat.pos_of_ne_zero (mul_ne_zero Subgroup.FiniteIndex.index_ne_zero
      Subgroup.FiniteIndex.index_ne_zero)
  rw [← e₁, ← e₂] at hprod
  have hab : H₁.relIndex J₁ * H₂.relIndex J₂ * (J₁.index * J₂.index) =
      1 * (J₁.index * J₂.index) := by
    calc _ = H₁.relIndex J₁ * J₁.index * (H₂.relIndex J₂ * J₂.index) := by ring
      _ = _ := by rw [hprod, one_mul]
  exact le_antisymm h₁ (Subgroup.relIndex_eq_one.mp
    (Nat.eq_one_of_mul_eq_one_right (Nat.eq_of_mul_eq_mul_right hJ hab)))

/-- Janusz V.9.1: the explicit paired radical field realizes its independently defined
congruence subgroup as Artin kernel, once both moduli are sufficiently deep. -/
theorem paired_hasArtinKernel [IsTotallyComplex K]
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hdisj : Disjoint S T)
    (hcover : CoversNthPrimes K n (S.disjUnion T hdisj))
    (hreps : SupportsClassRepresentatives K (S.disjUnion T hdisj)) :
    ∃ t₀ : ℕ, ∀ s ≥ t₀, ∀ t ≥ t₀,
      HasArtinKernel K (supportModulus K S s)
        (radicalField K n
          (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t)))
        (pairedSubgroup K n (supportModulus K S s) T) := by
  have hTS : T.disjUnion S hdisj.symm = S.disjUnion T hdisj := by
    ext v
    simp only [Finset.mem_disjUnion, or_comm]
  have hcover' : CoversNthPrimes K n (T.disjUnion S hdisj.symm) := hTS ▸ hcover
  have hgood : ∀ (A B : Finset (HeightOneSpectrum (𝓞 K))) (a : ℕ), 0 < a → Disjoint A B →
      ∀ v ∈ B, v.asIdeal ⊔ supportModulus K A a = ⊤ := by
    intro A B a ha hAB v hv
    by_contra h
    have hmax := v.isPrime.isMaximal v.ne_bot
    have hle : supportModulus K A a ≤ v.asIdeal :=
      le_sup_right.trans (hmax.eq_of_le h le_sup_left).symm.le
    exact Finset.disjoint_left.mp hAB ((supportModulus_le_prime_iff K A a ha v).mp hle) hv
  obtain ⟨a₁, ha₁⟩ := paired_uniform_reciprocity K n hn ζ hζ S T hdisj hcover
  obtain ⟨a₂, ha₂⟩ := paired_uniform_reciprocity K n hn ζ hζ T S hdisj.symm hcover'
  obtain ⟨b₁, hb₁⟩ := pairedRadicalField_unramified K n hn ζ hζ S T hdisj hcover
  obtain ⟨b₂, hb₂⟩ := pairedRadicalField_unramified K n hn ζ hζ T S hdisj.symm hcover'
  obtain ⟨c₁, hc₁⟩ := pairedRadicalField_splits_opposite K n hn ζ hζ (S.disjUnion T hdisj) T
  obtain ⟨c₂, hc₂⟩ := pairedRadicalField_splits_opposite K n hn ζ hζ (S.disjUnion T hdisj) S
  obtain ⟨d, hd⟩ := powerCongruenceIndex_pair_product K S T hdisj n hn ζ hζ hcover
  refine ⟨max 1 (max (max a₁ a₂) (max (max b₁ b₂) (max (max c₁ c₂) d))),
    fun s hs t ht => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hs ht
  obtain ⟨hs1, ⟨hsa₁, hsa₂⟩, ⟨hsb₁, hsb₂⟩, ⟨hsc₁, hsc₂⟩, hsd⟩ := hs
  obtain ⟨ht1, ⟨hta₁, hta₂⟩, ⟨htb₁, htb₂⟩, ⟨htc₁, htc₂⟩, htd⟩ := ht
  haveI := pairedRadicands_finiteQuotient K n hn (S.disjUnion T hdisj) (supportModulus K T t)
  haveI := pairedRadicands_finiteQuotient K n hn (S.disjUnion T hdisj) (supportModulus K S s)
  haveI := radicalField_finiteDimensional K n hn
    (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t))
  haveI := radicalField_finiteDimensional K n hn
    (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K S s))
  haveI := radicalField_isAbelianGalois K n hn ζ hζ
    (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t))
  haveI := radicalField_isAbelianGalois K n hn ζ hζ
    (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K S s))
  haveI : NumberField (radicalField K n
      (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t))) :=
    NumberField.of_module_finite K _
  haveI : NumberField (radicalField K n
      (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K S s))) :=
    NumberField.of_module_finite K _
  obtain ⟨φ₁, hφ₁, hsurj₁, hray₁⟩ := ha₁ s hsa₁ t hta₁
  have r₂ := ha₂ t hta₂ s hsa₂
  rw [hTS] at r₂
  obtain ⟨φ₂, hφ₂, hsurj₂, hray₂⟩ := r₂
  have hU₁ : IsUnramifiedAway K (supportModulus K S s) (radicalField K n
      (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t))) :=
    fun q hq hq0 hqm => hb₁ t htb₁ q hq hq0
      (eq_top_mono (sup_le_sup_left (supportModulus_antitone K S hs1) q) hqm)
  have u₂ := hb₂ s hsb₂
  rw [hTS] at u₂
  have hU₂ : IsUnramifiedAway K (supportModulus K T t) (radicalField K n
      (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K S s))) :=
    fun q hq hq0 hqm => u₂ q hq hq0
      (eq_top_mono (sup_le_sup_left (supportModulus_antitone K T ht1) q) hqm)
  have hle₁ := pairedSubgroup_le_artin_ker K (supportModulus K S s) _ n T φ₁ hφ₁ hU₁ hray₁
    (Kummer.radicalField_aut_pow K n hn ζ hζ _) (hgood S T s hs1 hdisj) (hc₁ t htc₁)
  have hle₂ := pairedSubgroup_le_artin_ker K (supportModulus K T t) _ n S φ₂ hφ₂ hU₂ hray₂
    (Kummer.radicalField_aut_pow K n hn ζ hζ _) (hgood T S t ht1 hdisj.symm) (hc₂ s hsc₂)
  have hk₁ : φ₁.ker.index = ((nthPowers K n).subgroupOf
      (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K T t))).index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective φ₁ hsurj₁, Subgroup.card_top,
      IsGalois.card_aut_eq_finrank, radicalField_finrank K n hn ζ hζ]
  have hk₂ : φ₂.ker.index = ((nthPowers K n).subgroupOf
      (pairedRadicands K n (S.disjUnion T hdisj) (supportModulus K S s))).index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective φ₂ hsurj₂, Subgroup.card_top,
      IsGalois.card_aut_eq_finrank, radicalField_finrank K n hn ζ hζ]
  have hidx := paired_index_identity K n hn ζ hζ S T hdisj hreps s t hs1 ht1
  rw [mul_assoc _ (powerCongruenceIndex K n (supportModulus K S s)), hd s hsd t htd] at hidx
  have hprod : (pairedSubgroup K n (supportModulus K S s) T).index *
      (pairedSubgroup K n (supportModulus K T t) S).index = φ₁.ker.index * φ₂.ker.index := by
    rw [hk₁, hk₂]
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hn _) hidx
  haveI := raySubgroup_finiteIndex K (supportModulus K S s) (supportModulus_ne_bot K S s)
  haveI := raySubgroup_finiteIndex K (supportModulus K T t) (supportModulus_ne_bot K T t)
  haveI : (pairedSubgroup K n (supportModulus K S s) T).FiniteIndex :=
    Subgroup.finiteIndex_of_le (show raySubgroup K (supportModulus K S s) ≤
      pairedSubgroup K n (supportModulus K S s) T from le_sup_left.trans le_sup_left)
  haveI : (pairedSubgroup K n (supportModulus K T t) S).FiniteIndex :=
    Subgroup.finiteIndex_of_le (show raySubgroup K (supportModulus K T t) ≤
      pairedSubgroup K n (supportModulus K T t) S from le_sup_left.trans le_sup_left)
  have heq := eq_of_le_of_index_mul_eq _ _ _ _ hle₁ hle₂ hprod
  exact ⟨inferInstance, inferInstance, inferInstance, hU₁, φ₁, hφ₁, hsurj₁, heq.symm⟩



/-- Sufficiently deep support moduli refine a nonzero ideal whose primes lie in the support. -/
theorem exists_supportModulus_le (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), m ≤ v.asIdeal → v ∈ S) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, supportModulus K S t ≤ m := by
  classical
  obtain ⟨S', e, he, hm'⟩ := exists_modulus_prime_powers K m hm
  refine ⟨Finset.univ.sup e, fun t ht => ?_⟩
  have hsub : S' ⊆ S := fun v hv => hS v (by
    rw [hm']
    exact (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ ⟨v, hv⟩))).trans
      (Ideal.pow_le_self (he ⟨v, hv⟩).ne'))
  rw [← Ideal.dvd_iff_le, hm', supportModulus]
  calc ∏ v : S', v.1.asIdeal ^ e v ∣ ∏ v : S', v.1.asIdeal ^ t :=
        Finset.prod_dvd_prod_of_dvd _ _ fun v _ =>
          pow_dvd_pow _ (le_trans (Finset.le_sup (Finset.mem_univ v)) ht)
    _ = ∏ v ∈ S', v.asIdeal ^ t := Finset.prod_coe_sort S' (fun v => v.asIdeal ^ t)
    _ ∣ ∏ v ∈ S, v.asIdeal ^ t := Finset.prod_dvd_prod_of_subset _ _ _ hsub

/-- Janusz V.9.16 after the V.7 reduction: the paired construction proves existence
when the base already contains roots of unity for an exponent of the class quotient. -/
theorem exists_classField_of_primitiveRoot [IsTotallyComplex K]
    (H : CongruenceSubgroup K) (n : ℕ) (hn : 0 < n) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n)
    (hexp : ∀ c : coprimeIdeals K H.modulus ⧸ H.subgroup, c ^ n = 1) :
    HasClassField K H := by
  classical
  obtain ⟨S₀, hreps₀, hcover₀⟩ := exists_suitable_support K n hn
  have hfinm := Ideal.finite_factors H.modulus_ne_bot
  have hSm : ∀ v : HeightOneSpectrum (𝓞 K), H.modulus ≤ v.asIdeal → v ∈ S₀ ∪ hfinm.toFinset :=
    fun v hv => Finset.mem_union_right _ (hfinm.mem_toFinset.mpr (Ideal.dvd_iff_le.mpr hv))
  have hdisj : Disjoint (S₀ ∪ hfinm.toFinset) (∅ : Finset (HeightOneSpectrum (𝓞 K))) :=
    Finset.disjoint_empty_right _
  have hU : (S₀ ∪ hfinm.toFinset).disjUnion ∅ hdisj = S₀ ∪ hfinm.toFinset :=
    Finset.disjUnion_empty _ hdisj
  have hreps : SupportsClassRepresentatives K ((S₀ ∪ hfinm.toFinset).disjUnion ∅ hdisj) := by
    rw [hU]
    intro c
    obtain ⟨u, hu, huc⟩ := hreps₀ c
    refine ⟨u, Subgroup.closure_mono ?_ hu, huc⟩
    rintro x ⟨v, hv, hx⟩
    exact ⟨v, Finset.mem_union_left _ hv, hx⟩
  have hcover : CoversNthPrimes K n ((S₀ ∪ hfinm.toFinset).disjUnion ∅ hdisj) := by
    rw [hU]
    exact fun v hv => Finset.mem_union_left _ (hcover₀ v hv)
  obtain ⟨t₀, ht₀⟩ := paired_hasArtinKernel K n hn ζ hζ _ ∅ hdisj hcover hreps
  obtain ⟨t₁, ht₁⟩ := exists_supportModulus_le K H.modulus H.modulus_ne_bot _ hSm
  have hle : supportModulus K (S₀ ∪ hfinm.toFinset) (max t₀ t₁) ≤ H.modulus :=
    ht₁ _ (le_max_right _ _)
  have hm0 : supportModulus K (S₀ ∪ hfinm.toFinset) (max t₀ t₁) ≠ ⊥ := supportModulus_ne_bot K _ _
  obtain ⟨hfin, hgal, hcomm, hUnr, φ, hφ, hsurj, hφk⟩ := ht₀ _ (le_max_left _ _) t₀ le_rfl
  haveI := hfin
  haveI := hgal
  haveI := hcomm
  haveI : IsAbelianGalois K (radicalField K n (pairedRadicands K n
    ((S₀ ∪ hfinm.toFinset).disjUnion ∅ hdisj) (supportModulus K ∅ t₀))) := ⟨⟩
  haveI : NumberField (radicalField K n (pairedRadicands K n
    ((S₀ ∪ hfinm.toFinset).disjUnion ∅ hdisj) (supportModulus K ∅ t₀))) :=
    NumberField.of_module_finite K _
  have hbot : supportedIdeals K (∅ : Finset (HeightOneSpectrum (𝓞 K))) = ⊥ := by
    rw [supportedIdeals, eq_bot_iff, Subgroup.closure_le]
    rintro x ⟨v, hv, -⟩
    simp at hv
  have hker : φ.ker ≤ H.subgroup.comap (Subgroup.inclusion (coprimeIdeals_mono K hle)) := by
    rw [hφk]
    refine sup_le (sup_le (raySubgroup_le_restrict K H _ hle) ?_) ?_
    · rintro _ ⟨y, rfl⟩
      rw [Subgroup.mem_comap, powMonoidHom_apply, map_pow]
      have h := hexp (QuotientGroup.mk (Subgroup.inclusion (coprimeIdeals_mono K hle) y))
      rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
    · intro u hu
      have hu' : (u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ supportedIdeals K ∅ := hu
      rw [hbot, Subgroup.mem_bot] at hu'
      have hu1 : u = 1 := Subtype.ext hu'
      rw [hu1]
      exact one_mem _
  exact hasClassField_of_isClassFieldFor K H _
    ⟨restrictCongruence K H _ hm0 hle, restrictCongruence_equivalent K H _ hm0 hle,
      hasArtinKernel_fixedField K _ _ hUnr φ hφ hsurj _ hker⟩

/-- The norm-preimage quotient inherits every exponent of the base quotient. -/
theorem normPreimage_pow_mem (E : Type*) [Field E] [NumberField E] [Algebra K E]
    [Module.Finite (𝓞 K) (𝓞 E)] (H : CongruenceSubgroup K) (n : ℕ)
    (hexp : ∀ c : coprimeIdeals K H.modulus ⧸ H.subgroup, c ^ n = 1)
    (u : coprimeIdeals E (H.modulus.map (algebraMap (𝓞 K) (𝓞 E)))) :
    u ^ n ∈ normPreimage K E H := by
  obtain ⟨A, B, hA, hB, hAm, hBm, huAB⟩ := exists_coprime_ideal_quotient E _ u
  have hNA : Ideal.relNorm (𝓞 K) A ≠ ⊥ := Ideal.relNorm_eq_bot_iff.not.mpr hA
  have hNB : Ideal.relNorm (𝓞 K) B ≠ ⊥ := Ideal.relNorm_eq_bot_iff.not.mpr hB
  have hNAne : (Ideal.relNorm (𝓞 K) A : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hNA
  have hNBne : (Ideal.relNorm (𝓞 K) B : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hNB
  have ha : Units.mk0 _ hNAne ∈ coprimeIdeals K H.modulus :=
    Subgroup.subset_closure ⟨_, hNA, relNorm_coprime K E _ A hAm, rfl⟩
  have hb : Units.mk0 _ hNBne ∈ coprimeIdeals K H.modulus :=
    Subgroup.subset_closure ⟨_, hNB, relNorm_coprime K E _ B hBm, rfl⟩
  have hv : (⟨_, div_mem ha hb⟩ : coprimeIdeals K H.modulus) ^ n ∈ H.subgroup := by
    have h := hexp (QuotientGroup.mk ⟨_, div_mem ha hb⟩)
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
  rw [mem_normPreimage_iff]
  refine ⟨A ^ n, B ^ n, pow_ne_zero _ hA, pow_ne_zero _ hB, Ideal.pow_sup_eq_top hAm,
    Ideal.pow_sup_eq_top hBm, ?_, _, hv, ?_⟩
  · rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, FractionalIdeal.coeIdeal_pow,
      FractionalIdeal.coeIdeal_pow, ← mul_pow, huAB]
  · change (((Units.mk0 _ hNAne / Units.mk0 _ hNBne) ^ n : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) * _ = _
    rw [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, map_pow,
      map_pow, FractionalIdeal.coeIdeal_pow, FractionalIdeal.coeIdeal_pow, div_pow,
      div_mul_cancel₀ _ (pow_ne_zero _ hNBne)]

section TowerNorm

variable (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
  [Module.Finite (𝓞 K) (𝓞 F)] [Module.Finite (𝓞 F) (𝓞 L)] [Module.Finite (𝓞 K) (𝓞 L)]

/-- Norm preimages compose along a tower of number fields (relative-norm transitivity). -/
theorem normPreimageCongruence_tower (H : CongruenceSubgroup K) :
    CongruenceEquivalent L (normPreimageCongruence F L (normPreimageCongruence K F H))
      (normPreimageCongruence K L H) := by
  have hM : (H.modulus.map (algebraMap (𝓞 K) (𝓞 F))).map (algebraMap (𝓞 F) (𝓞 L)) =
      H.modulus.map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine ⟨H.modulus.map (algebraMap (𝓞 K) (𝓞 L)),
    modulus_map_ne_bot K L H.modulus H.modulus_ne_bot, hM.ge, le_rfl, ?_⟩
  congr 1
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨A, B, hA, hB, hAm, hBm, huAB, w, hw, hwN⟩ :=
      (mem_normPreimage_iff F L (normPreimageCongruence K F H) u).mp hu
    obtain ⟨A', B', -, hB', -, -, hwAB', v, hv, hvn⟩ := (mem_normPreimage_iff K F H w).mp hw
    have hu2 : (u : (FractionalIdeal (𝓞 L)⁰ L)ˣ) ∈
        coprimeIdeals L (H.modulus.map (algebraMap (𝓞 K) (𝓞 L))) := by
      rw [← hM]
      exact u.2
    have hAm2 : A ⊔ H.modulus.map (algebraMap (𝓞 K) (𝓞 L)) = ⊤ := by
      rw [← hM]
      exact hAm
    have hBm2 : B ⊔ H.modulus.map (algebraMap (𝓞 K) (𝓞 L)) = ⊤ := by
      rw [← hM]
      exact hBm
    have hNB'ne : (Ideal.relNorm (𝓞 K) B' : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (Ideal.relNorm_eq_bot_iff.not.mpr hB')
    have hcross : (Ideal.relNorm (𝓞 F) A : FractionalIdeal (𝓞 F)⁰ F) * B' =
        A' * Ideal.relNorm (𝓞 F) B := by
      rw [← hwN, ← hwAB']
      ring
    have hN := relNorm_cross_mul K F _ _ A' B' hcross
    rw [Ideal.relNorm_relNorm (𝓞 K) (𝓞 F) A, Ideal.relNorm_relNorm (𝓞 K) (𝓞 F) B] at hN
    refine ⟨⟨u, hu2⟩, (mem_normPreimage_iff K L H ⟨u, hu2⟩).mpr
      ⟨A, B, hA, hB, hAm2, hBm2, huAB, v, hv, ?_⟩, rfl⟩
    apply mul_right_cancel₀ hNB'ne
    calc _ = ((v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) *
          (Ideal.relNorm (𝓞 K) B' : FractionalIdeal (𝓞 K)⁰ K) *
          (Ideal.relNorm (𝓞 K) B : FractionalIdeal (𝓞 K)⁰ K) := by ring
      _ = ((Ideal.relNorm (𝓞 K) A' * Ideal.relNorm (𝓞 K) B : Ideal (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K) := by rw [hvn, FractionalIdeal.coeIdeal_mul]
      _ = _ := by rw [← hN, FractionalIdeal.coeIdeal_mul]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨A, B, hA, hB, hAm, hBm, huAB, v, hv, hvn⟩ := (mem_normPreimage_iff K L H u).mp hu
    have hAm' : A ⊔ (H.modulus.map (algebraMap (𝓞 K) (𝓞 F))).map (algebraMap (𝓞 F) (𝓞 L)) = ⊤ := by
      rw [hM]
      exact hAm
    have hBm' : B ⊔ (H.modulus.map (algebraMap (𝓞 K) (𝓞 F))).map (algebraMap (𝓞 F) (𝓞 L)) = ⊤ := by
      rw [hM]
      exact hBm
    have hNA : Ideal.relNorm (𝓞 F) A ≠ ⊥ := Ideal.relNorm_eq_bot_iff.not.mpr hA
    have hNB : Ideal.relNorm (𝓞 F) B ≠ ⊥ := Ideal.relNorm_eq_bot_iff.not.mpr hB
    have hNAne : (Ideal.relNorm (𝓞 F) A : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr hNA
    have hNBne : (Ideal.relNorm (𝓞 F) B : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr hNB
    have hNAm := relNorm_coprime F L _ A hAm'
    have hNBm := relNorm_coprime F L _ B hBm'
    have ha : Units.mk0 _ hNAne ∈ coprimeIdeals F (H.modulus.map (algebraMap (𝓞 K) (𝓞 F))) :=
      Subgroup.subset_closure ⟨_, hNA, hNAm, rfl⟩
    have hb : Units.mk0 _ hNBne ∈ coprimeIdeals F (H.modulus.map (algebraMap (𝓞 K) (𝓞 F))) :=
      Subgroup.subset_closure ⟨_, hNB, hNBm, rfl⟩
    have hwN : ((Units.mk0 _ hNAne / Units.mk0 _ hNBne : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) * (Ideal.relNorm (𝓞 F) B : FractionalIdeal (𝓞 F)⁰ F) =
          Ideal.relNorm (𝓞 F) A := by
      rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, div_mul_cancel₀ _ hNBne]
    have hw : (⟨_, div_mem ha hb⟩ : coprimeIdeals F (H.modulus.map (algebraMap (𝓞 K) (𝓞 F)))) ∈
        normPreimage K F H :=
      (mem_normPreimage_iff K F H _).mpr ⟨_, _, hNA, hNB, hNAm, hNBm, hwN, v, hv, by
        rw [Ideal.relNorm_relNorm (𝓞 K) (𝓞 F) A, Ideal.relNorm_relNorm (𝓞 K) (𝓞 F) B]
        exact hvn⟩
    have hu1 : (u : (FractionalIdeal (𝓞 L)⁰ L)ˣ) ∈ coprimeIdeals L
        ((H.modulus.map (algebraMap (𝓞 K) (𝓞 F))).map (algebraMap (𝓞 F) (𝓞 L))) := by
      rw [hM]
      exact u.2
    exact ⟨⟨u, hu1⟩, (mem_normPreimage_iff F L (normPreimageCongruence K F H) ⟨u, hu1⟩).mpr
      ⟨A, B, hA, hB, hAm', hBm', huAB, ⟨_, div_mem ha hb⟩, hw, hwN⟩, rfl⟩

end TowerNorm

universe u

/-- Janusz V.7: cyclic descent iterates along a finite abelian extension. -/
theorem classField_descends_abelian (d : ℕ) : ∀ (K₀ E₀ : Type u) [Field K₀] [NumberField K₀]
    [IsTotallyComplex K₀] [Field E₀] [NumberField E₀] [Algebra K₀ E₀] [IsAbelianGalois K₀ E₀]
    [Module.Finite (𝓞 K₀) (𝓞 E₀)] (H : CongruenceSubgroup K₀), Module.finrank K₀ E₀ = d →
      HasClassField E₀ (normPreimageCongruence K₀ E₀ H) → HasClassField K₀ H := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K₀ E₀ _ _ _ _ _ _ _ _ H hd hE
  haveI : FiniteDimensional K₀ E₀ := Module.Finite.of_restrictScalars_finite ℚ K₀ E₀
  by_cases hcyc : IsCyclic (E₀ ≃ₐ[K₀] E₀)
  · exact classField_descends_cyclic K₀ E₀ H hE
  obtain ⟨ι, hι, F, hFcyc, hbot⟩ := exists_cyclic_subfields_iInf_fixing_eq_bot K₀ E₀
  have hex : ∃ i, F i ≠ ⊥ := by
    by_contra hall
    push Not at hall
    apply hcyc
    have htop : (⊤ : Subgroup (E₀ ≃ₐ[K₀] E₀)) = ⊥ := by
      rw [← hbot]
      simp only [hall, IntermediateField.fixingSubgroup_bot, iInf_top]
    have hx : ∀ x : E₀ ≃ₐ[K₀] E₀, x = 1 := fun x =>
      (Subgroup.eq_bot_iff_forall ⊤).mp htop x (Subgroup.mem_top x)
    haveI : Subsingleton (E₀ ≃ₐ[K₀] E₀) := ⟨fun x y => (hx x).trans (hx y).symm⟩
    exact isCyclic_of_subsingleton
  obtain ⟨i, hi⟩ := hex
  haveI := hFcyc i
  haveI : IsAbelianGalois K₀ (F i) := IsAbelianGalois.tower_bot K₀ (F i) E₀
  haveI : NumberField (F i) := NumberField.of_module_finite K₀ (F i)
  haveI : IsTotallyComplex (F i) := NumberField.isTotallyComplex_of_algebra K₀ (F i)
  haveI : IsAbelianGalois (F i) E₀ := IsAbelianGalois.tower_top K₀ (F i) E₀
  haveI : Module.Finite (𝓞 K₀) (𝓞 (F i)) :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 K₀) (𝓞 (F i))
  haveI : Module.Finite (𝓞 (F i)) (𝓞 E₀) :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 (F i)) (𝓞 E₀)
  have hlt : Module.finrank (F i) E₀ < d := by
    rw [← hd, ← Module.finrank_mul_finrank K₀ (F i) E₀]
    have h0 : 0 < Module.finrank K₀ (F i) := Module.finrank_pos
    have h1 : Module.finrank K₀ (F i) ≠ 1 := fun h => hi (IntermediateField.finrank_eq_one_iff.mp h)
    have h2 : 0 < Module.finrank (F i) E₀ := Module.finrank_pos
    have h1' : 2 ≤ Module.finrank K₀ (F i) := by omega
    nlinarith
  have hE' := hasClassField_of_equivalent E₀ _ _
    ((congruenceEquivalent_equivalence E₀).symm (normPreimageCongruence_tower K₀ (F i) E₀ H)) hE
  exact classField_descends_cyclic K₀ (F i) H
    (ih _ hlt (F i) E₀ (normPreimageCongruence K₀ (F i) H) rfl hE')

/-- Janusz V.9.16: cyclotomic base change and repeated cyclic descent remove the
roots-of-unity hypothesis. -/
theorem exists_classField [IsTotallyComplex K] (H : CongruenceSubgroup K) :
    HasClassField K H := by
  haveI := raySubgroup_finiteIndex K H.modulus H.modulus_ne_bot
  haveI : H.subgroup.FiniteIndex := Subgroup.finiteIndex_of_le H.contains_ray
  have hn : 0 < Nat.card (coprimeIdeals K H.modulus ⧸ H.subgroup) := Nat.card_pos
  haveI : NeZero (Nat.card (coprimeIdeals K H.modulus ⧸ H.subgroup)) := ⟨hn.ne'⟩
  set n := Nat.card (coprimeIdeals K H.modulus ⧸ H.subgroup) with hndef
  haveI : FiniteDimensional K (CyclotomicField n K) :=
    IsCyclotomicExtension.finiteDimensional {n} K _
  haveI : IsGalois K (CyclotomicField n K) := IsCyclotomicExtension.isGalois {n} K _
  have hζ := IsCyclotomicExtension.zeta_spec n K (CyclotomicField n K)
  haveI : IsMulCommutative (CyclotomicField n K ≃ₐ[K] CyclotomicField n K) :=
    ⟨⟨fun a b => IsPrimitiveRoot.autToPow_injective K hζ (by rw [map_mul, map_mul, mul_comm])⟩⟩
  haveI : IsAbelianGalois K (CyclotomicField n K) := ⟨⟩
  haveI : IsTotallyComplex (CyclotomicField n K) := NumberField.isTotallyComplex_of_algebra K _
  haveI : Module.Finite (𝓞 K) (𝓞 (CyclotomicField n K)) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  have hexpE : ∀ c : coprimeIdeals (CyclotomicField n K)
      (normPreimageCongruence K (CyclotomicField n K) H).modulus ⧸
        (normPreimageCongruence K (CyclotomicField n K) H).subgroup, c ^ n = 1 := by
    intro c
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact normPreimage_pow_mem K _ H n (fun _ => pow_card_eq_one') u
  exact classField_descends_abelian _ K (CyclotomicField n K) H rfl
    (exists_classField_of_primitiveRoot _ _ n hn _ hζ hexpE)

/-- The conductor of an ideal group is the gcd of all its defining finite moduli,
represented by their ideal supremum. -/
def idealGroupConductor (H : CongruenceSubgroup K) : Ideal (𝓞 K) :=
  sSup {m | ∃ J : CongruenceSubgroup K, CongruenceEquivalent K H J ∧ J.modulus = m}

/-- Janusz V.6.2: the conductor itself is a defining modulus for the ideal group. -/
theorem exists_congruence_at_conductor (H : CongruenceSubgroup K) :
    ∃ J : CongruenceSubgroup K, CongruenceEquivalent K H J ∧
      J.modulus = idealGroupConductor K H := by
  set A : Set (Ideal (𝓞 K)) :=
    {m | ∃ J : CongruenceSubgroup K, CongruenceEquivalent K H J ∧ J.modulus = m} with hA
  have hne : A.Nonempty := ⟨H.modulus, H, (congruenceEquivalent_equivalence K).refl H, rfl⟩
  obtain ⟨M, ⟨J, hHJ, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr inferInstance A hne
  refine ⟨J, hHJ, ?_⟩
  have hsup : ∀ m ∈ A, m ≤ J.modulus := by
    rintro m ⟨J', hHJ', rfl⟩
    have hJJ' : CongruenceEquivalent K J J' := (congruenceEquivalent_equivalence K).trans
      ((congruenceEquivalent_equivalence K).symm hHJ) hHJ'
    obtain ⟨G, hG, hJG, -⟩ := exists_congruence_gcd K J J' hJJ'
    have hle : J.modulus ≤ G.modulus := hG ▸ le_sup_left
    have hGJ : CongruenceEquivalent K J G := by
      refine ⟨J.modulus, J.modulus_ne_bot, le_rfl, hle, ?_⟩
      rw [inf_eq_left.mpr J.ambient_le_coprimeIdeals]
      exact hJG
    have hGA : G.modulus ∈ A := ⟨G, (congruenceEquivalent_equivalence K).trans hHJ hGJ, rfl⟩
    have heq : J.modulus = G.modulus := (lt_or_eq_of_le hle).resolve_left (hmax _ hGA)
    rw [heq, hG]
    exact le_sup_right
  exact (le_antisymm (sSup_le hsup) (le_sSup ⟨J, hHJ, rfl⟩)).symm

end Cox.ClassFieldTheory
