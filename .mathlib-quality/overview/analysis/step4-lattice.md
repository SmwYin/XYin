# Step 4 — Mathlib-API audit: lattices, elliptic curves, Hermite normal form

Files audited: `XYin/uniqueness.lean`, `XYin/PhD/Cox/LatticeJ.lean`, `XYin/PhD/Cox/HermiteNormalForm.lean`,
`XYin/PhD/Cox/CyclicSublattice.lean`, `XYin/PhD/Cox/CyclicSublattice/Classification.lean`,
`XYin/PhD/Cox/SingularModuli.lean`.
Mathlib pin: commit `2abc2425` (2026-05-28). Every mathlib name below was verified to exist in
`.lake/packages/mathlib` at this pin.

---

## Definitions to Replace with Mathlib

**`Cox.not_isSquare_of_between_sq_aux` (SingularModuli.lean:59) → replace with `Nat.not_exists_sq`** —
Current: hand-rolled 15-line proof that `k² < N < (k+1)²` (k : ℤ, 0 ≤ k) forbids `IsSquare N`, via `sq_lt_sq₀` and `omega`.
Mathlib alternative: `Nat.not_exists_sq : m * m < n → n < (m + 1) * (m + 1) → ¬∃ t, t * t = n` and
`Nat.not_exists_sq' : m ^ 2 < n → n < (m + 1) ^ 2 → ¬∃ t, t ^ 2 = n` (`Mathlib/Data/Nat/Sqrt.lean:207,213`) — this is exactly the "between consecutive squares" lemma; the lead is CONFIRMED.
Impact: deletes the aux entirely; callers pass `k.toNat` (they already have `0 ≤ k`) and bridge `IsSquare N ↔ ∃ t, t * t = N` (defeq to `∃ r, N = r * r`, `IsSquare.exists_sq` / `⟨t, ht.symm⟩`).
**Action**: delete aux, use `Nat.not_exists_sq` with the two `nlinarith` bounds cast to ℕ (`Int.toNat_lt'`/`exact_mod_cast`). Difficulty: easy.

**`PeriodPair.CyclicSublattice.carrierEquiv` + `carrierToPeriodPairLinearMap` + `carrierToPeriodPairLinearMap_bijective` (CyclicSublattice.lean:303–330) → replace with `Submodule.equivMapOfInjective`** —
Current: ~28 lines building `S.carrier ≃ₗ[ℤ] S.toPeriodPair.lattice` by hand (a `LinearMap` structure literal plus a bijectivity proof).
Mathlib alternative: `Submodule.equivMapOfInjective (f : M →ₛₗ M₂) (i : Injective f) (p : Submodule R M) : p ≃ₗ p.map f` with simp lemma `Submodule.coe_equivMapOfInjective_apply` (`Mathlib/Algebra/Module/Submodule/Map.lean:146,160`), injectivity from `Submodule.injective_subtype` (`Submodule/LinearMap.lean:100`).
Impact: `carrierEquiv := (Submodule.equivMapOfInjective L.lattice.subtype L.lattice.injective_subtype S.carrier).trans (LinearEquiv.ofEq _ _ S.toPeriodPair_lattice.symm)`; `carrierEquiv_apply_coe` follows from the mathlib coe lemma.
**Action**: replace the three private decls with the one-line composite. Difficulty: easy.

**`PeriodPair.CyclicSublattice.dualMatrix` (CyclicSublattice.lean:434) → define via `Matrix.adjugate`** —
Current: `dualMatrix S = !![a S, -b S; 0, d S]`, a hand-written companion of the HNF matrix `!![d S, b S; 0, a S]`.
Mathlib alternative: `Matrix.adjugate_fin_two_of : adjugate !![a, b; c, d] = !![d, -b; -c, a]` (`Mathlib/LinearAlgebra/Matrix/Adjugate.lean:380`) shows `dualMatrix S = S.hermiteNormalForm.matrix.adjugate` exactly (the `-0` entry normalizes by `neg_zero`).
Impact: this is the conceptual content of the dual isogeny — `Matrix.mul_adjugate` / `Matrix.adjugate_mul` (`A * adjugate A = A.det • 1`, det = ±m) then explains `dualCarrier`'s "composition = multiplication by m" for free, and `Matrix.det_adjugate` (`det (adjugate A) = det A ^ (n-1)`, here `= det A`) discharges the det computation inside `dual_index_eq`.
**Action**: redefine `dualMatrix S := S.hermiteNormalForm.matrix.adjugate` (unfolds to the same literal by `adjugate_fin_two_of`), and use `Matrix.det_adjugate`/`mul_adjugate` where the dual determinant/index is computed. Difficulty: medium (touches five `dual_repr_*` proofs, but they simp through the same literal).

**`PeriodPair.invariantsDetermineLattice` (uniqueness.lean:328) → delete** —
Current: verbatim ∀-quantified restatement of `lattice_eq_of_g₂_eq_of_g₃_eq` two lines above, kept only to match a talk file.
Impact: redundant public decl.
**Action**: delete (or mark `deprecated`) and use `lattice_eq_of_g₂_eq_of_g₃_eq` at the call sites. Difficulty: trivial.

---

## API Choice Improvements

**`PeriodPair.smul` / `mem_smul_lattice` / `map_lattice_mulLeftLinearEquiv` / `smulLatticeEquiv` (LatticeJ.lean:33–100) → route through the pointwise `Submodule` action** —
Current: scaling of lattices is handled by bespoke lemmas: membership (`mem_smul_lattice`), image under `Units.mulLeftLinearEquiv` (verified mathlib, `Mathlib/Algebra/Module/Equiv/Basic.lean:903`), and a bespoke `≃ₗ`.
Mathlib alternative: `Submodule.pointwiseDistribMulAction : DistribMulAction α (Submodule R M)` (scoped `Pointwise` instance, `Mathlib/Algebra/Module/Submodule/Pointwise.lean:189`) gives `a • L.lattice : Submodule ℤ ℂ` for `a : ℂˣ`, with
`Submodule.mem_smul_pointwise_iff_exists : m ∈ a • S ↔ ∃ s ∈ S, a • s = m` (Pointwise.lean:221) and
`Submodule.smul_span : a • span R s = span R (a • s)` (`Mathlib/LinearAlgebra/Span/Basic.lean:286`).
Impact: one bridge lemma `(a • L).lattice = a • L.lattice` (provable by `smul_span` + `Set.smul_set_insert`/`smul_set_singleton`) makes `mem_smul_lattice` a one-liner instance of the mathlib iff, gives `smul_smul`-style composition of scalings for free, and lets `dualCarrier_map_subtype_aux` / `scale_carrier_map_subtype` / `complexSublatticeSpan_eq_scaledLattice` (Classification.lean:311) compute with `DistribMulAction` laws instead of double-`ext`/`rintro` transfers.
**Action**: add `lemma smul_lattice (a : ℂˣ) (L : PeriodPair) : (a • L).lattice = a • L.lattice`; re-derive the three membership/map lemmas from mathlib's pointwise API. Difficulty: medium.

**`Matrix.rankTwoContent` (HermiteNormalForm.lean:43) → define via `Finset.gcd`** —
Current: nested `Nat.gcd` of the four `natAbs` entries; four private divisibility lemmas (`rankTwoContent_dvd_entry`, `dvd_rankTwoContent`, `rankTwoContent_dvd_mul_right/left`) proved by hand-chained `Nat.gcd_dvd_left/right`, and the same chains re-done in `fixingMatrix_content_eq_one` (SingularModuli.lean:141) and `toCoxMatrix` (Classification.lean:47–53) modulo `Nat.gcd_comm/assoc` shuffling.
Mathlib alternative: `Finset.gcd` with `Finset.gcd_dvd : b ∈ s → s.gcd f ∣ f b` and `Finset.dvd_gcd : (∀ b ∈ s, a ∣ f b) → a ∣ s.gcd f` (`Mathlib/Algebra/GCDMonoid/Finset.lean:141,144`). Define `rankTwoContent A := Finset.univ.gcd fun p : Fin 2 × Fin 2 ↦ (A p.1 p.2).natAbs` (also generalizes beyond `Fin 2` for free).
Impact: `rankTwoContent_dvd_entry` becomes `Finset.gcd_dvd (mem_univ _)`, `dvd_rankTwoContent` becomes `Finset.dvd_gcd`; the mul lemmas keep their one `Matrix.mul_apply` step; the gcd-reassociation `simpa`s in SingularModuli/Classification become `Finset.gcd`-congruence over an explicit 4-element set instead of order-sensitive `Nat.gcd_comm/left_comm/assoc` juggling. Mathlib has NO matrix-content definition (verified: no `Matrix.content` anywhere), so the def itself stays project-local.
**Action**: refactor the definition; keep the public name/statement of the two `quotient_isAddCyclic_iff_*` theorems unchanged. Difficulty: medium.

**`Matrix.IsColumnHermiteNormalForm.belowDiagonal_eq_zero` (HermiteNormalForm.lean:36) → state via `Matrix.BlockTriangular id`** —
Current: field `∀ i j, j < i → A i j = 0`, definitionally `A.BlockTriangular id` (`Mathlib/LinearAlgebra/Matrix/Block.lean:61`), but stated raw, so the triangular-determinant computation is redone by hand at ≥3 sites: `d_mul_a_eq_m` (CyclicSublattice.lean:387), `hdetA` in `toCoxMatrix` (Classification.lean:43), `dual_index_eq`'s det step (CyclicSublattice.lean:582).
Mathlib alternative: `Matrix.det_of_upperTriangular [LinearOrder m] (h : M.BlockTriangular id) : M.det = ∏ i, M i i` (Block.lean:324), plus the whole `BlockTriangular` closure API (`BlockTriangular.mul`, `.det`, `invertibleToBlock`).
Impact: one derived lemma `IsColumnHermiteNormalForm.blockTriangular : A.BlockTriangular id` (rfl-level) plus `IsColumnHermiteNormalForm.det_eq : A.det = ∏ i, A i i` and `det_pos` kills the three ad-hoc `det_fin_two` computations and scales past rank two.
**Action**: add the two derived lemmas (or restate the field as `blockTriangular : A.BlockTriangular id`); rewrite the three det computations. Difficulty: easy–medium.

**`exists_unit_mul_pos_aux` (HermiteNormalForm.lean:95) → use `Int.sign`** —
Current: case split producing `s ∈ {1, -1}` with `0 < x * s`.
Mathlib alternative: take `s := x.sign`; `Int.sign_mul_self_eq_natAbs : sign a * a = natAbs a` (`Mathlib/Data/Int/Init.lean:205`) gives `x * x.sign = x.natAbs > 0`, and unit-ness from `Int.isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1` (`Mathlib/Algebra/Group/Int/Units.lean:45`) with `Int.sign_eq_one_or_neg_one` under `x ≠ 0`.
Impact: marginal golf; the aux is private and 7 lines. **Action**: optional. Difficulty: trivial.

**`reduced_eq_of_eq_add_mul` (HermiteNormalForm.lean:269) → `Int.ediv_emod_unique''`** —
Current: uniqueness-of-remainder proved via two `Int.emod_eq_of_lt` rewrites and `Int.add_emod`.
Mathlib alternative: `Int.ediv_emod_unique''` (`Mathlib/Data/Int/Lemmas.lean:117`, permits negative divisor) or `Int.ediv_emod_unique` (core) characterize `(q, r)` uniquely from `r + b*q = a ∧ 0 ≤ r < b`.
Impact: marginal; current proof is already 4 lines. **Action**: optional. Difficulty: trivial.

**`PeriodPair.j` vs `WeierstrassCurve.j` — bridge, don't replace** —
`WeierstrassCurve.j = W.Δ'⁻¹ * W.c₄ ^ 3` exists (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:385`, needs a `[W.IsElliptic]` instance making `Δ'` a unit). For `W := {a₁ = a₂ = a₃ = 0, a₄ = -g₂/4, a₆ = -g₃/4}` one computes `c₄ = 12·g₂`, `Δ = g₂³ − 27·g₃²`, so `W.j = 1728·g₂³/(g₂³−27g₃²) = L.j` on the nose — a bridge lemma `L.j = (W L).j` is available and would connect this cluster to the elliptic-curve library (`j_eq_zero_iff`, isomorphism invariance).
However *defining* `PeriodPair.j` through it is not recommended: it would drag `IsElliptic` instance management (`discriminant_ne_zero` becomes a prerequisite instead of a theorem) into every homothety lemma, and none of the downstream files need curve-side API. Mathlib has no lattice→Weierstrass-curve constructor (verified: `PeriodPair` is referenced nowhere outside `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`).
**Action**: keep `PeriodPair.j` as is; optionally add the bridge lemma when the EC connection is needed. Difficulty of bridge: medium.

---

## Hand-Rolled Patterns to Replace

**`PeriodPair.G_smul` (LatticeJ.lean:103) — inline equiv duplicates `smulLatticeEquiv`** —
The proof constructs a bare `Equiv` `e : L.lattice ≃ (a • L).lattice` by hand (10 lines: toFun/invFun/left_inv/right_inv) although `smulLatticeEquiv a L : L.lattice ≃ₗ[ℤ] (a • L).lattice` with simp lemma `coe_smulLatticeEquiv_apply` is defined 17 lines earlier in the same file.
**Action**: use `(smulLatticeEquiv a L).toEquiv.tsum_eq` and the existing coe simp lemmas. Difficulty: easy.

**Nested-coercion rfl-lemmas `coe_carrier_add` / `coe_carrier_zsmul` (CyclicSublattice.lean:122–130) and `hcoe_add` / `hcoe_zsmul` (Classification.lean:267–269)** —
These restate `Submodule.coe_add` / `SetLike.val_smul` (both already appear in the file's own `simp only` lists, e.g. CyclicSublattice.lean:468) for the two-step coercion `S.carrier → L.lattice → ℂ`. Applying the mathlib simp lemmas stepwise (`push_cast` or `simp [Submodule.coe_add, SetLike.val_smul]`) makes the four private lemmas unnecessary.
**Action**: inline; delete the private lemmas. Difficulty: easy.

**Triangular determinants computed entrywise** — see the `BlockTriangular` item above (`d_mul_a_eq_m`, Classification `hdetA`, `dual_index_eq`).

**`Cox.PrimitiveQuadraticEquation.fixingMatrix_content_eq_one` (SingularModuli.lean:141)** —
Four hand-chained `Nat.gcd_dvd_*` extractions; collapses to `Finset.gcd_dvd`/`Finset.dvd_gcd` after the `rankTwoContent` refactor above. Difficulty: easy (after that refactor).

---

## Missing tags/instances

**`MulAction ℂˣ PeriodPair` instance (LatticeJ.lean:44)** —
Only `SMul ℂˣ PeriodPair` is registered, so `smul_smul`, `one_smul`, `inv_smul_smul` are unavailable; `exists_sl2_smul_eq_of_periodPair_homothetic_aux` and the `scale`/`dual` composition arguments re-derive compositions by hand. `(a * b) • L = a • b • L` and `1 • L = L` hold by `PeriodPair` ext (`mk.injEq`) + `mul_assoc`/`one_mul`.
**Action**: upgrade the instance to `MulAction ℂˣ PeriodPair` (needs a `@[ext]` lemma for `PeriodPair`, itself missing). Difficulty: easy.

**`PeriodPair.Homothetic` equivalence-relation lemmas** —
`Homothetic.refl/symm/trans` (or an `Equivalence` bundling) are absent; each is one line from `j_eq_iff_homothetic` (or directly from the `MulAction` structure once added). Downstream (`theorem_11_23` reverse direction) would read better.
**Action**: add the three lemmas. Difficulty: trivial.

**`Fintype (PeriodPair.CyclicSublattice L m)`** —
`cyclicSublatticeEquivCoxMatrixOfPeriodPair L m : CyclicSublattice L m ≃ CoxMatrix m` exists and `CoxMatrix m` is finite (CoxMatrices/Cardinality file); `Fintype.ofEquiv _ (cyclicSublatticeEquivCoxMatrixOfPeriodPair L m).symm` gives finiteness of the sublattice family — the natural statement of "there are ψ(m) sublattices".
**Action**: add the instance next to the equiv. Difficulty: trivial.

**`IsColumnHermiteNormalForm` derived lemmas** — `det_eq`, `det_pos`, `blockTriangular` (see above); also `matrix_fin_two_eq : A = !![A 0 0, A 0 1; 0, A 1 1]` would subsume `originalMatrix_eq` (CyclicSublattice.lean:381, currently private and re-proved from scratch).

**Simp candidates** — `PeriodPair.j_smul` and `CyclicSublattice.j_scale`/`j_ofLatticeEq` are canonical normalization facts used in `calc` chains repeatedly; tagging `j_smul` `@[simp]` is safe (LHS strictly more complex). `dual_base_j` (CyclicSublattice.lean:666) is an `rfl` lemma that duplicates the definition of `CyclicSublattice.j`; either tag `@[simp]` or delete.

---

## Verified no-change (and refuted leads)

**`PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq` (uniqueness.lean) — NOT in mathlib** — At the pin, `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (1075 lines) ends with `derivWeierstrassP_sq`; there is no uniqueness theorem, no scaling action, no `j`, no `discriminant`, and the file carries the explicit TODO "Establish connections with the `ModularForm` library" (line ~937). The whole of uniqueness.lean and the LatticeJ homothety/weight lemmas (`G_smul`, `g₂_smul`, `g₃_smul`, `discriminant_ne_zero`, `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`) are prime mathlib-contribution candidates. Lead about mathlib providing lattice-equality-from-invariants: **REFUTED**.

**Hermite normal form — NOT in mathlib** — `grep -ri hermite` over `Mathlib/LinearAlgebra`, `Mathlib/Data/Matrix` is empty; `Mathlib/LinearAlgebra/Matrix/SmithNormalForm.lean` does not exist (Smith machinery lives in `FreeModule/PID.lean` as `Module.Basis.SmithNormalForm`, which the project correctly mirrors structurally); `Matrix.IsUpperTriangular` does not exist (only `Matrix.BlockTriangular`). Leads REFUTED except as noted under `BlockTriangular`. The HNF file is itself a mathlib-contribution candidate.

**Index = |det| API — already optimal** — `Mathlib/LinearAlgebra/FreeModule/Finite/CardQuotient.lean` provides exactly `Submodule.natAbs_det_equiv`, `Submodule.natAbs_det_basis_change`, `AddSubgroup.index_eq_natAbs_det`, `AddSubgroup.relIndex_eq_natAbs_det`; the project uses `AddSubgroup.index_eq_natAbs_det` in both `index_eq_natAbs_det` (HNF) and `dual_index_eq`. `Submodule.cardQuotRelDet` does not exist under that name; `Ideal.absNorm` is inapplicable (ambient is an abstract `AddCommGroup`, not a ring). Lead resolved: nothing more of the file is redundant against CardQuotient.

**Cyclic-quotient criterion — correct mathlib usage** — `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` correctly composes `Submodule.smithNormalFormTopBasis/BotBasis/Coeffs`, `Submodule.quotientEquivPiZMod` (all in `FreeModule/Finite/Quotient.lean` + `PID.lean`), `RingEquiv.piFinTwo` (`Mathlib/Algebra/Ring/Fin.lean:27`), `AddGroup.isAddCyclic_prod_iff` and `isAddCyclic_of_surjective` (`GroupTheory/SpecificGroups/Cyclic.lean`). No shortcut exists in mathlib.

**`Mathlib.GroupTheory.IndexNSmul` — is mathlib, used correctly** — `AddSubgroup.nsmul_index_mem`, `finrank_eq_of_finiteIndex`, `nsmulAddMonoidHom_injective_of_isTorsionFree`, `AddSubgroup.index_map_equiv` all verified in the mathlib file.

**`PrimitiveQuadraticEquation` / `IsImaginaryQuadratic` / `fixingMatrix` — no mathlib counterpart** — Mathlib has no binary quadratic forms (`BinaryQF`/`BinaryQuadraticForm` absent; `Zsqrtd` is ℤ[√d]-arithmetic, not BQF; the general `QuadraticForm` theory has no integral-binary/discriminant-reduction specialization) and no "imaginary quadratic point of ℍ" notion. Leads REFUTED. The structure is the right local design.

**`singularModulus_isIntegral` ±-monic handling — keep** — No mathlib lemma "root of a polynomial with unit leading coefficient is integral" exists; `Polynomial.integralNormalization` only yields integrality of `leadingCoeff • x`. The explicit `p` vs `-p` monic case split is the shortest route.

**`weierstrassP_eventuallyEq` (uniqueness.lean:252) — keep** — No mathlib lemma "analytic at x + equal iterated derivatives at x ⇒ eventually equal" (leansearch + loogle empty); the `HasFPowerSeriesAt` subtraction route is the intended API. Contribution candidate.

**`riemannZeta_six_aux` (LatticeJ.lean:196) — keep, contribute** — mathlib has `riemannZeta_four` but no `riemannZeta_six`; the aux derives it from `riemannZeta_two_mul_nat`. Trivial mathlib PR candidate.

**`eqOn_weierstrassP` / `lattice_le_of_eqOn`** — already on best API: `countable_of_Lindelof_of_discrete`, `Set.Countable.isConnected_compl_of_one_lt_rank`, `Set.Countable.dense_compl`, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `meromorphicOrderAt_congr` + `PeriodPair.order_weierstrassP`. No change.

**`exists_right_mul_isColumnHermiteNormalForm`** — Bézout via `Int.gcd_eq_gcd_ab`, `Int.emod_add_mul_ediv`; nothing in mathlib subsumes the column-reduction (no HNF), keep.
