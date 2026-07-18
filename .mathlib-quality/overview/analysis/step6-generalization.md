# Step 6 — Generalization Analysis

Scope: all project files under `XYin/` (excluding `PhD/Modularforms/`), read via the per-file
inventories in `.mathlib-quality/overview/inventory/` plus targeted source reads and mathlib greps
(`.lake/packages/mathlib`). Format per finding:
current signature → what the proof actually uses → literature generality → mathlib status →
**Action** → Difficulty (Low = change binders / delete in favour of mathlib; Medium = some proof
rework; High = restructure).

---

## A. HermiteNormalForm.lean (`XYin/PhD/Cox/HermiteNormalForm.lean`)

### A1. **`Matrix.exists_right_mul_isColumnHermiteNormalForm` — currently 2×2 over ℤ, works for n×n over any Bézout domain (existence) / EuclideanDomain-with-residues (canonical form)**
- Current: `(A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det ≠ 0) : ∃ B, IsUnit B.det ∧ (A * B).IsColumnHermiteNormalForm`.
- Proof actually uses (read `exists_hnf_transform`, lines 133–190): `Int.gcd_eq_gcd_ab` (Bézout identity), `Int.ediv_mul_cancel` (exact division by the gcd), `Int.emod_add_mul_ediv` / `Int.emod_nonneg` / `Int.emod_lt_of_pos` (Euclidean division with the canonical nonnegative residue), and `exists_unit_mul_pos_aux` (sign normalization via ℤ's linear order). So: *upper-triangularization* needs only a Bézout domain; *canonical reduction* (`0 ≤ r < d`, `0 < pivot`) needs ℤ's order/Euclidean structure, or abstractly a choice of residue transversal and associate representatives.
- Literature: HNF exists for n×m matrices over any PID, indeed any Bézout domain; uniqueness of the canonical form requires a chosen system of residues mod each pivot and of unit-normalized associates (Cohen, *A Course in Computational Algebraic Number Theory* §2.4; Newman, *Integral Matrices* Thm II.2–II.3; Wikipedia "Hermite normal form" — generalizes to Dedekind/principal ideal domains; the Isabelle AFP entry by Divasón–Aransay formalizes HNF over Bézout domains). Sources: [Hermite normal form — Wikipedia](https://en.wikipedia.org/wiki/Hermite_normal_form), [Hermite Canonical Form over a PID (SIGSAM)](https://dl.acm.org/doi/10.1145/101104.101105), [AFP Hermite entry](https://www.isa-afp.org/browser_info/current/AFP/Hermite/outline.pdf).
- Mathlib status: **no Hermite normal form at all** (grep of `LinearAlgebra`, `Data/Matrix`, `RingTheory` finds only Hermite *polynomials*). Mathlib has Smith normal form over PIDs (`Mathlib/LinearAlgebra/FreeModule/PID.lean`, `Submodule.smithNormalFormBotBasis` etc.), which the project already leans on.
- **Action**: what mathlib would want is n×n over ℤ first (statement of `IsColumnHermiteNormalForm` already takes `{ι} [Preorder ι]` — good), with the Bézout-domain existence as a follow-up. For this project, the honest write-up is: keep rank 2, but document that the algebraic core (`hnf_transform_mul_aux`) is Bézout-generic while reduction is ℤ-specific.
- Difficulty: **High** (n×n needs an induction the file does not have; 2×2→Bézout-existence alone would be Medium).

### A2. **`Module.Basis.HermiteNormalForm.matrix_mul_toMatrix_eq` — currently rank 2, works for any rank n**
- Current: stated with `bM : Basis (Fin 2) ℤ M` only because of the surrounding `variable` block (the inventory already flags this).
- Proof actually uses: `linearMap_toMatrix_mul_basis_toMatrix` — completely rank-generic.
- **Action**: move above the rank-2 `variable` section and state for `Fin n`. Pure binder change.
- Difficulty: **Low**.

### A3. **`matrix_eq` / `bN_eq` (HNF uniqueness) — currently rank 2 over ℤ; extends to rank n over ℤ, and to PIDs only relative to a residue system**
- Proof actually uses: upper-triangularity + `Int.le_of_dvd` (divisibility antisymmetry among positives — an ℤ-order fact) + `reduced_eq_of_eq_add_mul` (uniqueness of the canonical residue in `[0, d)`).
- Literature: uniqueness of HNF holds in rank n over ℤ (Cohen §2.4.2); over a general PID only after fixing unit/residue representatives.
- Mathlib status: absent (see A1).
- **Action**: if upstreaming ever happens, this is the rank-n induction to write; otherwise leave. Note `reduced_eq_of_eq_add_mul` is a self-contained ℤ lemma ("two residues in `[0,d)` congruent mod d are equal") that could be stated once, generally, near `Int.emod`.
- Difficulty: **High** (rank n), **Low** for extracting `reduced_eq_of_eq_add_mul`.

### A4. **`Matrix.rankTwoContent` + `quotient_isAddCyclic_iff_rankTwoContent_toMatrix_eq_one` — currently 2×2/ℤ, works for n×n over a PID via determinantal divisors**
- Current: content = gcd of the four entries; theorem: `IsAddCyclic (M ⧸ N) ↔ content(inclusion matrix) = 1` (Cox Ex. 11.16).
- Proof actually uses: Smith normal form (`Submodule.smithNormalFormCoeffs`), invariance of content under unimodular multiplication (`rankTwoContent_dvd_mul_left/right` — the proofs only use bilinearity of matrix mult + gcd axioms, valid over any GCD domain), `Submodule.quotientEquivPiZMod`, `AddGroup.isAddCyclic_prod_iff`, `Nat.coprime_iff_gcd_eq_one`. The only genuinely rank-2 step is "cyclic ⟺ gcd(d₀,d₁)=1", which for `d₀ ∣ d₁` says `d₀ = 1`.
- Literature generality: the content is the **first determinantal divisor** D₁(A); for n×n over a PID, M/N ≅ ⊕ R/(dᵢ) with d₁ ∣ … ∣ dₙ and the quotient is cyclic iff d₁ = … = d_{n−1} = 1, i.e. iff the gcd of the (n−1)×(n−1) minors D_{n−1}(A) is a unit (Newman, *Integral Matrices*, Thm II.9 on determinantal divisors). The rank-2 statement is the coincidence D₁ = D_{n−1} when n = 2.
- Mathlib status: no matrix content, no determinantal divisors (`Polynomial.content` exists over GCD domains; nothing for matrices).
- **Action**: at minimum rename/document `rankTwoContent` as D₁ and note the correct n×n generalization is via D_{n−1}, *not* via D₁ (a naive "content = 1 ⇒ cyclic" is false for n ≥ 3). Upstream candidate: matrix content over a `GCDMonoid` + invariance under unimodular multiplication.
- Difficulty: **Medium** (content API over GCD domain), **High** (full determinantal-divisor story).

---

## B. LaurentQExpansion machinery (`LaurentQExpansion/LaurentQExpansion.lean`, `Algebra.lean`)

### B1. **`meromorphicAt_of_comp_pow` — currently ℂ→ℂ at 0; correct generality is exactly ℂ (REFUTED beyond ℂ), but it is a strong mathlib candidate as stated**
- Current: `{g : ℂ → ℂ} {m : ℕ} (hm : m ≠ 0) (h : MeromorphicAt (g ∘ (·^m)) 0) : MeromorphicAt g 0`.
- Proof actually uses: `Complex.isOpenQuotientMap_pow` (open mapping theorem) and `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` (Riemann removable singularity) — both live in `Mathlib/Analysis/Complex/` and are genuinely one-complex-variable facts. **REFUTED for general nontrivially normed fields**: the removable-singularity step has no analogue over ℝ or a general 𝕜.
- Literature: descent of meromorphy along a ramified covering q ↦ qᵐ is standard one-variable complex analysis (implicit in every treatment of q-expansions at width N, e.g. Diamond–Shurman §1.2 / Cox §11).
- Mathlib status: absent — `Mathlib/Analysis/Meromorphic/` has `MeromorphicAt.comp_analyticAt` (the easy direction) and `meromorphicOrderAt_comp` but **no descent** (grep for `of_comp` in `Analysis/Meromorphic` is empty). The codomain could however be generalized from ℂ to a complete normed ℂ-space `E` for free (both mathlib inputs are stated for `f : ℂ → E`).
- **Action**: upstream to `Mathlib/Analysis/Meromorphic/` as `MeromorphicAt.of_comp_pow` (with the aux lemma), generalizing codomain ℂ → Banach `E` and the point 0 → arbitrary `z₀` (compose with translations). The file's inventory already flags it "no modular-forms content".
- Difficulty: **Low** to extract as-is; **Medium** with codomain/base-point generalization.

### B2. **`poleOrder` / `poleRemoved` / `to_qExpansion` / `laurentqExpansion` — currently defined for `f : ℍ → ℂ` through `cuspFunction h f`; the mathematical content is a Laurent-expansion API for an arbitrary meromorphic germ `g : ℂ → ℂ` at a point**
- Current: all four defs and ~25 lemmas (`coeff_of_geq`, `coeff_eq_zero_of_lt`, `poleOrder_to_order`, `to_qExpansion_eq_powerSeriesPart`, `laurentqExpansion_coeff_eq_circleIntegral`, …) take `(h : ℝ) (f : ℍ → ℂ)` and mention `f` only via `cuspFunction h f`.
- Proof actually uses: inspection of each proof shows the only cusp-specific inputs are `cuspFunction_qpow_mul_eq` and the junk-value branch `h ≤ 0`; everything else (`meromorphicOrderAt`, `AnalyticAt`, `qExpansion` as Taylor series, `HahnSeries` bookkeeping, `circleIntegral`) is about the germ `g = cuspFunction h f` at `0 ∈ ℂ`. E.g. `analyticAt_cuspFunction_poleRemoved` (132 lines) is "multiplying a meromorphic germ by z^{poleOrder} yields an analytic germ", and `laurentqExpansion_coeff_eq_circleIntegral` (151 lines) is the Cauchy formula for Laurent coefficients of a meromorphic function.
- Literature: the Laurent expansion of a function meromorphic at a point, with `a_n = (2πi)⁻¹∮ g(z)z^{−n−1}dz`, is textbook one-variable complex analysis (Ahlfors Ch. 5; for the cusp specialization Diamond–Shurman §1.1). The natural general statement is for `g : ℂ → E`, `E` complex Banach, at any `z₀`.
- Mathlib status: **absent** — `Mathlib/Analysis/Meromorphic/` never mentions `LaurentSeries` (grep confirms); mathlib has `meromorphicOrderAt`, `MeromorphicAt.eventually_analyticAt`, and the `qExpansion` power series, but no "Laurent series of a meromorphic germ".
- **Action**: restructure: define `MeromorphicAt.laurentCoeffs` / `laurentExpansionAt g z₀ : LaurentSeries ℂ` (pole order = `(−order).toNat`, pole-removed = `(· − z₀)^M • g`, series = shifted Taylor series), prove the coefficient/circle-integral lemmas there once, and recover the whole cusp API as `laurentqExpansion h f := laurentExpansionAt (cuspFunction h f) 0` plus the two genuinely cusp lemmas. This would also delete the duplicates the inventory flags (`meromorphicOrderAt_cuspFunction_eq_neg_poleOrder` twice, `cuspFunction_to_analyticAt_analyticAt`). Prime mathlib contribution.
- Difficulty: **High** (restructure), but each transported lemma is mechanical afterwards.

### B3. **`cuspFunction_nat_mul_eq_cuspFunction_pow`, `meromorphicOrderAt_cuspFunction_nat_mul`, `poleOrder_nat_mul` — cusp-specific glue, correctly so; but the embedded fact `analyticOrderAt (·^m) 0 = m` is general and is proved inline twice**
- The inventory notes the `analyticOrderAt_pow`/`analyticOrderAt_id` computation block is duplicated verbatim inside `meromorphicOrderAt_cuspFunction_nat_mul` (lines 227–239 vs 240–244).
- **Action**: extract `analyticOrderAt (fun q : ℂ ↦ q ^ m) 0 = m` (holds over any 𝕜) as a lemma; check `analyticOrderAt_pow` in current mathlib first — it may already compose to this in one line.
- Difficulty: **Low**.

### B4. **`analyticTaylor_comp_pow` (Algebra.lean, private) — currently ℂ; a general uniqueness statement about `PowerSeries.expand`**
- Current: `F =ᶠ[𝓝 0] G ∘ (·^m)` with both analytic ⇒ `analyticTaylor F = (analyticTaylor G).expand m hm`.
- Proof actually uses: `Complex.hasSum_taylorSeries_on_ball` + reindexing along `n ↦ m·n` + `HasFPowerSeriesAt.eq_formalMultilinearSeries`. The Taylor-sum input is the only ℂ-specific piece; over a general complete nontrivially normed field the same statement holds via `FormalMultilinearSeries` composition, but mathlib's convenient entry points are ℂ.
- Mathlib status: `PowerSeries.expand` exists (`Mathlib/RingTheory/PowerSeries/Expand.lean`); the analytic bridge "germ equality under `·^m` ⟺ series related by `expand`" does not.
- **Action**: upstream as a ℂ lemma (`AnalyticAt` + `expand`), noting the 𝕜-general version as future work. Also `analyticAt_hasFPowerSeriesAt_taylor` is flagged by the inventory as likely subsumed by existing mathlib API — check `AnalyticAt.hasFPowerSeriesAt` + `iteratedDeriv`-coefficient lemmas before keeping it.
- Difficulty: **Medium**.

---

## C. IntegralPowerSeries (`IntegralPowerSeries/IntegralPowerSeries.lean`)

### C1. **`powerSeriesMapAlgHom` — duplicate of mathlib, delete**
- Current: `(R A) [CommSemiring R] [Semiring A] [Algebra R A] : PowerSeries R →ₐ[R] PowerSeries A`, built by hand from `PowerSeries.map`.
- Mathlib status: `PowerSeries.mapAlgHom (φ : A →ₐ[R] B)` exists (`Mathlib/RingTheory/PowerSeries/Basic.lean:728`); the project's map is exactly `PowerSeries.mapAlgHom (Algebra.ofId R A)`.
- **Action**: replace the definition with the mathlib composite (or an abbrev), deleting the hand-rolled `commutes'` proof.
- Difficulty: **Low**.

### C2. **`HasCoeffsIn` / `powerSeriesMapSubalgebra` — currently `Algebra R A`; the literature/mathlib-standard form is `lifts` along an arbitrary ring hom**
- Current: membership in `AlgHom.range (powerSeriesMapAlgHom R A)`; already commendably general (CommSemiring/Semiring), used downstream only at `R = ℤ, A = ℂ`.
- What the proofs actually use: only ring-hom-ness of `algebraMap R A` (`coeff_map`, `map_C`, `Subalgebra.*_mem`); nothing uses the algebra structure beyond producing the map.
- Literature/mathlib parallel: mathlib's `Polynomial.lifts (f : R →+* S) : Subsemiring S[X]` (`Mathlib/Algebra/Polynomial/Lifts.lean`) is precisely this notion for polynomials, keyed to an arbitrary ring hom, with `liftsRing`, `mem_lifts_iff_coeff` analogues. **No `PowerSeries.lifts` exists in mathlib** (grep confirms).
- **Action**: restate as `PowerSeries.lifts (f : R →+* S) : Subsemiring S⟦X⟧` mirroring the polynomial file (the `hasCoeffsIn_iff_coeff` proof carries over verbatim), keep the `Algebra` version as the range-of-`mapAlgHom` corollary, and upstream. The ℂ-specific abbrev tower (`IsRIntegralCPowerSeries`, `IsIntegralCPowerSeries`, `coeToComplexPowerSeries.ringHom`, `RIntegralCPowerSeriesSubring`) adds no generality and could shrink to two abbrevs after this.
- Difficulty: **Medium** (mostly renaming/re-plumbing; proofs unchanged).

### C3. **`IsIntegralPowerSeriesmod` — currently ℤ→ℂ; works for any `f : R →+* S` with `f` injective-on-need and `c` a non-zero-divisor**
- Proof actually uses: `Int.modEq_iff_dvd`, cancellation `(1/c)·(c·t) = t` in ℂ (i.e. `c ≠ 0` in a field / `c` regular), and the round-trip lemma. The ℤ-mod language is convenience; the content is "if every coefficient of the lift is divisible by c, then `c⁻¹ • f` still lifts".
- **Action**: low-priority; if C2 happens, restate as a `lifts` lemma with `c : R` regular and `S` a field (or `c` invertible in `S`).
- Difficulty: **Low–Medium**. (Also: fix name `IsIntegralPowerSeries_mod`.)

---

## D. Irreducibility.lean private lemmas

### D1. **`card_le_minpoly_natDegree_of_injective_roots` + `irreducible_of_card_conjugates` — already fully general; extract/upstream as-is**
- Current: `{F E ι} [Field F] [CommRing E] [IsDomain E] [Algebra F E] [Fintype ι]`, α integral, an injective family of `minpoly`-roots ⇒ `card ι ≤ natDegree (minpoly F α)`; and the derived criterion: monic `p` with root α and `natDegree p ≤ card ι` ⇒ `Irreducible p` (indeed `p = minpoly F α`).
- Proof actually uses: `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`, `minpoly.monic/dvd/irreducible`, `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` — nothing project-specific (inventory concurs: "fully general, candidate for extraction/upstreaming").
- Literature: this is the standard "count the conjugates" irreducibility argument (Cox's proof of Thm 11.18(ii); same skeleton as the classical proof that Φ_m(X, j) is the minimal polynomial of j(mτ), Lang *Elliptic Functions* Ch. 5 §2).
- Mathlib status: no direct analogue found (`FieldTheory/Minpoly/*` has root-set cardinality lemmas but not this criterion). Possible micro-generalizations before upstreaming: `Fintype ι` → a `Finset` family; the intermediate lemma could conclude `p = minpoly F α` (strictly stronger, same proof).
- **Action**: move both out of `Cox` into a `ForMathlib` file (project has one), de-`private`, PR to `Mathlib/FieldTheory/Minpoly/`.
- Difficulty: **Low**.

---

## E. Interpolation.lean

### E1. **`eval_derivative_prod_X_sub_C_at` — mathlib already has it; delete**
- Current: `[CommRing R] [Fintype ι] [DecidableEq ι]`: `(derivative ∏ k, (X − C (r k))).eval (r i) = ∏ k ∈ univ.erase i, (r i − r k)`.
- Mathlib status: `Lagrange.derivative_nodal` + `Lagrange.eval_nodal_derivative_eval_node_eq` + `Lagrange.eval_nodal` (`Mathlib/LinearAlgebra/Lagrange.lean:595, 604, 571`) compose to exactly this statement, over `CommRing R` and arbitrary `Finset s` (strictly more general than the project's `Finset.univ`).
- **Action**: replace the 25-line proof with the two-line mathlib composition, or just use the mathlib lemmas at the call site in `recoveryFormula`.
- Difficulty: **Low**.

### E2. **`eval_interpolation_sum_at` — currently `Fintype ι`/`univ`; general un-normalized Lagrange evaluation over CommRing; not in mathlib**
- Current: `(∑ k, C (a k) * ∏ l ∈ univ.erase k, (X − C (r l))).eval (r i) = a i * ∏ l ∈ univ.erase i, (r i − r l)` over `[CommRing R]`.
- Mathlib status: mathlib's `Lagrange.interpolate` is over a **Field** with normalized `Lagrange.basis` (the `(v i − v j)⁻¹` weights), so this un-normalized CommRing statement is not there; it is however a two-step consequence of `Lagrange.eval_nodal_at_node`-style reasoning over the `nodal (s.erase k) v` polynomials.
- **Action**: generalize `univ` → arbitrary `s : Finset ι` (no injectivity of `r` needed — the proof only uses the vanishing factor `r i − r i`), restate in terms of `Lagrange.nodal (s.erase k) r`, upstream next to `nodal`.
- Difficulty: **Low**.

### E3. **`polynomial_prod_coeff_mdifferentiable_aux` (here) and `polynomial_prod_coeff_cuspMeromorphicAt` (AnalyticSupport) — two instances of one lemma about coefficient-wise predicates closed under +/·**
- Current: both prove "if every coefficient of every factor satisfies P, so does every coefficient of a `Finset.prod` of polynomials over `ℍ → ℂ`", for P = MDifferentiable resp. cusp-meromorphic, by the identical `Finset.induction_on`/`coeff_mul`/antidiagonal argument.
- What the proofs actually use: only that `{g | P g}` is a subsemiring of the function ring (closed under 0, 1, +, ·).
- General form: for `S : Subsemiring (α → ℂ)` (or any commutative ring), a product of polynomials with coefficients in `S` has coefficients in `S` — which is literally `Subsemiring.prod_mem` applied inside `Polynomial S`, i.e. the clean fix is to work with `Polynomial S` (the project already has the subring `HolomorphicFunction`) instead of `Polynomial (ℍ → ℂ)` plus a side predicate.
- Mathlib status: nothing to add — `Polynomial.lifts`/subring-valued polynomials already express this; the project just isn't using them.
- **Action**: consolidate the two lemmas into one parametrized by a `Subsemiring (ℍ → ℂ)` (Low), or restructure the interpolation polynomial to live over the subring (Medium).
- Difficulty: **Low–Medium**.

---

## F. LevelThree.lean jets and the Qj compute layer

### F1. **`jetMul`/`jetPow`/`jetShift`/`jetExpand` + soundness lemmas — defs are already generic `(ℕ → ℤ)`; the *window* `n < 37` is hard-coded in every soundness lemma**
- Current: `powerSeries_coeff_mul_eq_jetMul : (∀ n < 37, coeff n F = f n) → … → coeff n (F*G) = jetMul f g n` and siblings, with 37 = (pole-clearing exponent 36) + 1 baked in; `bivariateLaurentEval` window, `sigmaJetThree = jetExpand 9`, `widthJetThree = jetExpand 3` similarly bake in level 3 (orders −9 = −m², −3 = −m).
- What the proofs actually use: `coeff_mul`'s antidiagonal only reads indices ≤ n — the proofs are verbatim valid for any window `N` (replace `37` by a variable and `lia` still closes the bounds).
- Also: `jetMul` duplicates the Qj layer's `convArrayUpTo`/`convArrayCoeff` (Array-based Cauchy product) — two independent truncated-convolution implementations in one project.
- Mathlib status: `PowerSeries.trunc` exists but there is no "computable jet ring with soundness against `PowerSeries`" API; this is a plausible small mathlib contribution (truncated coefficient functions with `coeff_mul/pow/shift/expand` transfer lemmas).
- **Action**: parametrize the four soundness lemmas by `(N : ℕ)`; this is what unblocks reusing the whole certificate pipeline at level 5/7 (windows 36 → m²(m+1)). Consider merging with the Qj `convArrayUpTo` layer.
- Difficulty: **Low–Medium** (parametrize), **Medium** (merge with Qj layer).

### F2. **REFUTED: generalizing the ℤ compute layer (`sigmaPow`, `convArrayUpTo`, `inverseOnePlusCoeffsUpTo`, `qjCoeffInt`, jet certificates) to an arbitrary `CommRing`**
- These exist to make coefficients kernel-computable (`decide +kernel`); the whole design depends on decidable equality of closed ℤ terms and fast kernel `Int` arithmetic. A `CommRing R` version would type-check but be unusable (`decide` gone) and serve no consumer. Not worth it — keep over ℤ.

---

## G. Cardinality.lean (Cox matrices count)

### G1. **`card_filter_range_coprime_mul_aux` — currently a private project lemma; a general totient fact missing from mathlib**
- Current: `((Finset.range (k * g)).filter (g.Coprime ·)).card = k * g.totient`.
- Proof actually uses: mathlib's per-block `Nat.filter_coprime_Ico_eq_totient` + `Ico` glueing — fully general already (holds for all `g, k` including degenerate cases).
- Mathlib status: `Mathlib/Data/Nat/Totient.lean` has the single-block `filter_coprime_Ico_eq_totient (a n)` and the inequality `Ico_filter_coprime_le`, but not the exact k-block count.
- **Action**: upstream next to `filter_coprime_Ico_eq_totient` (arguably in `Ico a (a + k*g)` form for full generality).
- Difficulty: **Low**.

### G2. **`coxDivisorSumAux` / `card_coxMatrix` — currently an anonymous ad-hoc divisor sum; it *is* the Dedekind ψ function, absent from mathlib**
- Current: `card_coxMatrix : (Fintype.card (CoxMatrix m) : ℚ) = m ∏_{p ∣ m} (1 + 1/p)`, via the private multiplicative arithmetic function `coxDivisorSumAux n = ∑_{d ∣ n} (d/gcd(n/d,d))·φ(gcd(n/d,d))`.
- Literature: `|C(m)| = [SL₂(ℤ) : Γ₀(m)] = ψ(m)`, the **Dedekind psi function** ψ(n) = n∏_{p∣n}(1+1/p) — OEIS A001615, whose primary combinatorial meaning is exactly "number of cyclic (primitive) sublattices of index n" and the index of Γ₀(n) (see [Dedekind psi function — Wikipedia](https://en.wikipedia.org/wiki/Dedekind_psi_function), [OEIS A001615](https://oeis.org/A001615); Cox §11; Diamond–Shurman Ex. 1.2.3 gives the Γ₀ index).
- Mathlib status: `ArithmeticFunction` has ζ, σ, φ, μ and the full `IsMultiplicative.multiplicative_factorization` machinery (all used by the file), but **no Dedekind ψ** (grep "dedekind" in `NumberTheory/ArithmeticFunction*` is empty).
- What the proof actually uses: the fibration `CoxMatrix m ≃ Σ d ∣ m, fiber` is Cox-specific; everything from `coxDivisorTermAux` down is pure multiplicative number theory.
- **Action**: define `ArithmeticFunction.dedekindPsi` (ℕ-valued: `∑_{d∣n} …` or `n.factorization.prod (p^e + p^{e-1})`), prove `IsMultiplicative`, the prime-power value, and the ℚ Euler-product form — that is 5 of the file's private lemmas, generalized only by a name; then `card_coxMatrix : Fintype.card (CoxMatrix m) = dedekindPsi m` becomes the ℕ-valued statement (stronger than the current ℚ cast). Strong upstream candidate.
- Difficulty: **Medium** (mostly re-packaging).

---

## H. SymmetricCubicLaurent.lean

### H1. **Whole file — currently `[Field K]`; every proof only needs `[CommRing K] [IsDomain K]`**
- 26 occurrences of `Field K`; grep of the proofs shows no `⁻¹`/division. The order/leading-coefficient inputs (`HahnSeries.order_mul`, `order_pow`, `leadingCoeff_mul`) need only `NoZeroDivisors`/domain (checked: `HahnSeries.leadingCoeff_mul` requires `[NoZeroDivisors R]`, `Mathlib/RingTheory/HahnSeries/Multiplication.lean:573`).
- Same applies to `LaurentPolynomialEvaluation.lean` §F below.
- **Action**: weaken to `[CommRing K] [IsDomain K]` throughout. Mechanical.
- Difficulty: **Low**.

### H2. **`symmetric_bidegree_three_eq_zero_of_laurent_coeff` — currently bidegree ≤ 3, orders (−9, −3), ten hard-coded exponents; the triangular-detection argument works for bidegree ≤ n and any orders (−a, −b) with the weight map injective on the triangle**
- Current: symmetric `P`, `natDegree ≤ 3` both ways, `ord T = −9`, `ord J = −3`, monic leading coefficients, ten explicit vanishing coefficients ⇒ `P = 0`.
- What the proof actually uses (read the chain `cubicWeight` → `cubicWeight_strictMono` → `cubicBasis_coeff_self/zero_of_lt` → `Fin.reverseInduction`): (i) a symmetric polynomial of bidegree ≤ n is determined by its triangle coefficients `{(i,j) : j ≤ i ≤ n}` (the `symmetricCubicExpansion` block — four copy-pasted `coeff_*` lemmas that would collapse in the general version); (ii) the monomials `TⁱJʲ + TʲJⁱ` have leading exponent `−(a·i + b·j)` (only additivity of `HahnSeries.order`); (iii) **the weights `a·i + b·j` are pairwise distinct on the triangle** — the only place 9/3/bidegree-3 enter, via the literal `![…]` enumerations `cubicI`, `cubicJ` and `cubicWeight_strictMono` by `fin_cases`. For general level m one has a = m², b = m, and `a·i + b·j = m(m·i + j)` is injective on `{j ≤ i ≤ n}` whenever n < m + something — concretely, injectivity holds iff there is no collision `m(i−i′) = j′−j` within the triangle, which is a decidable arithmetic hypothesis one can simply take as an assumption.
- Literature: this is the standard q-expansion "back-substitution" proof that finitely many Fourier coefficients determine a symmetric Φ of known bidegree (Cox's derivation of (11.22); same triangular argument computes Φ_m for any m — e.g. the classical computations of Φ₅, Φ₇).
- Mathlib status: nothing comparable.
- **Action**: parametrize: replace `Fin 10`/`cubicI`/`cubicJ` by the `Finset` triangle `{(i,j) ∈ range(n+1)² | j ≤ i}` sorted by weight, take `(a b : ℤ)` with a strict-monotonicity/injectivity hypothesis on `(i,j) ↦ a·i + b·j`, and derive the level-3 instance by `decide`. This is the piece the project itself will need for higher-level modular polynomials.
- Difficulty: **High** (the enumeration-by-literal-vectors design must become order-theoretic), though every analytic ingredient is already general.

---

## I. LaurentPolynomialEvaluation.lean

### I1. **`polynomial_eval₂_laurentSeries_coeff` / `_injective` (Hasse q-expansion principle) — currently `[Field K]`, works for `[CommRing K] [IsDomain K]`**
- Proof actually uses: `HahnSeries.order_pow`/`order_mul` (domain), `leadingCoeff_mul` (`NoZeroDivisors`), `coeff_eq_zero_of_lt_order`, `Polynomial.leadingCoeff_ne_zero` — no inverses anywhere (grep confirms no `⁻¹`/`div` in the file).
- Literature: the "look at the lowest term" injectivity of `P ↦ P(J)` needs only an integral domain of coefficients (it is the standard proof that j is transcendental over ℂ, but works over ℤ or 𝔽_p verbatim — the project itself wants it over `ZMod p` in `Kronecker.lean`, where `jUnitLaurentSeriesMod` lives over `ZMod p`, a field only because p is prime; over `IsDomain` the statement would also cover ℤ directly and let `Kronecker` drop a cast).
- **Action**: weaken `Field K` → `CommRing K` + `IsDomain K` in the four field-assuming lemmas. Check whether the leading-coefficient-1 hypotheses can be relaxed to "leading coefficient a unit / non-zero-divisor" (the proof multiplies leading coefficients — regular elements suffice) — optional second step.
- Difficulty: **Low** (first step).

### I2. **`laurentSeriesMapRingHom` — currently `CommRing R S` and `Γ = ℤ`; works for any ordered monomial group and semirings; a bundled `HahnSeries.mapRingHom` is missing from mathlib**
- Proof actually uses: `HahnSeries.map_zero/one/add/mul` — mathlib's `HahnSeries.map_mul` needs only `NonUnitalNonAssocSemiring` + `f : R →ₙ+* S` (`Multiplication.lean:406`), and nothing in the bundling is ℤ-specific.
- Mathlib status: `HahnSeries.map` exists unbundled (`Basic.lean:143`) with the four hom lemmas, but grep finds **no bundled `→+*` version** in `RingTheory/HahnSeries/` or `LaurentSeries.lean`.
- **Action**: generalize to `HahnSeries.mapRingHom (f : R →+* S) : R⟦Γ⟧ →+* S⟦Γ⟧` for `[OrderedCancelAddCommMonoid Γ] [Semiring R] [Semiring S]` and upstream; the project keeps `laurentSeriesMapRingHom` as the `Γ = ℤ` abbreviation. `polynomialEvalLaurent_map` / `bivariateSpecializeLaurent_map` then also generalize `CommRing → Semiring` for free (their proofs are `hom_eval₂`/`eval₂_map`/`ringHom_ext`, all semiring-level).
- Difficulty: **Low**.

---

## J. uniqueness.lean (lattice determined by (g₂, g₃))

### J1. **REFUTED (as expected): the main pipeline is genuinely ℂ-specific**
- `eqOn_weierstrassP` uses the identity theorem plus connectivity of a countable-complement via `rank ℝ ℂ = 2`; `lattice_le_of_eqOn` uses `meromorphicOrderAt` pole comparison; `weierstrassP_eventuallyEq` uses `HasFPowerSeriesAt` over ℂ. The natural generality *is* ℂ-lattices/`PeriodPair` (Weierstrass data over ℂ) — matching the literature (Lang, *Elliptic Functions* Ch. 1; the algebraic analogue over other fields is a different theorem about Weierstrass curves, already in mathlib's `EllipticCurve` world). No action.

### J2. **`iteratedDeriv_sq_mul` — currently `g : ℂ → ℂ`; a general Leibniz-collapse fact**
- Current: `AnalyticAt ℂ g 0`, `2 ≤ n` ⇒ `iteratedDeriv n (z² · g z) 0 = n(n−1) · iteratedDeriv (n−2) g 0`.
- Proof actually uses: `iteratedDeriv_fun_mul` (Leibniz), `iteratedDeriv_fun_pow_zero`, `Nat.cast_choose_two` — all stated in mathlib for a general nontrivially normed field 𝕜 (and `ContDiffAt` would suffice in place of `AnalyticAt`).
- **Action**: restate over `{𝕜} [NontriviallyNormedField 𝕜]` with `ContDiffAt 𝕜 n g 0`, arbitrary base point via `(· − z₀)²`; small mathlib candidate near `iteratedDeriv_fun_mul`. The inventory already flags it "general-purpose helper".
- Difficulty: **Low**.

---

## K. CoxMatrix hypotheses and the Kronecker prime layer

### K1. **`CoxMatrix m` — no hidden assumptions to relax (checked)**
- The structure (`a·d = m`, `b < d`, `gcd(gcd a b) d = 1`) is stated for arbitrary `m : ℕ+`; no squarefree/`m > 1` assumption anywhere (`one_lt_card_coxMatrix` takes `1 < m` explicitly where needed). The Fintype/DecidableEq instances are generic. Nothing to do.

### K2. **`primeLowerCoxMatrix` / `primeFinToCoxMatrix` / `primeFinEquivCoxMatrix` — hard-coded to primes; correctly so**
- The bijection `CoxMatrix p ≃ Fin (p+1)` is a prime-only fact (|C(m)| = ψ(m) > m+1 for composite m — see G2). Not a generalization target; at most note that after G2 the *cardinality* statement `Fintype.card (CoxMatrix p) = p + 1` is `dedekindPsi p = p + 1`. No action.

### K3. **`jIntegralLaurentSeriesWidth` / `jUnitLaurentSeriesMod` (Kronecker.lean) — the "expand a Laurent series by m" construction is ad-hoc per width; a general `LaurentSeries.expand` is missing**
- `jIntegralLaurentSeriesWidth m` re-implements "substitute q ↦ qᵐ" on a Laurent series by an explicit coefficient formula (`if m ∣ k ∧ −m ≤ k then …`), in parallel with `PowerSeries.expand` (mathlib) and the LevelThree `single (−9) 1 * expand 9 …` pattern.
- **Action**: define once `LaurentSeries.expand (m : ℕ+) : LaurentSeries R →+* LaurentSeries R` (or reuse `HahnSeries.embDomain` along `k ↦ m·k`, which is what this is) and derive the width series; mathlib candidate (`HahnSeries.embDomainRingHom` for an ordered-monoid embedding may already be close — check `embDomain_mul` at `Multiplication.lean:903`).
- Difficulty: **Medium**.

---

## Summary table

| # | Declaration(s) | From → To | Difficulty |
|---|---|---|---|
| A2 | `matrix_mul_toMatrix_eq` | rank 2 → rank n (binder) | Low |
| A3′ | `reduced_eq_of_eq_add_mul` | extract general ℤ residue lemma | Low |
| B1 | `meromorphicAt_of_comp_pow` | upstream (ℂ, Banach codomain) | Low–Med |
| B3 | `analyticOrderAt (·^m) 0 = m` | extract, de-duplicate | Low |
| C1 | `powerSeriesMapAlgHom` | delete for `PowerSeries.mapAlgHom (Algebra.ofId)` | Low |
| D1 | `card_le_minpoly…`, `irreducible_of_card_conjugates` | extract + upstream (already general) | Low |
| E1 | `eval_derivative_prod_X_sub_C_at` | delete for `Lagrange.eval_nodal_derivative_eval_node_eq` | Low |
| E2 | `eval_interpolation_sum_at` | `univ` → `Finset`, upstream near `nodal` | Low |
| G1 | `card_filter_range_coprime_mul_aux` | upstream totient block-count | Low |
| H1 | SymmetricCubicLaurent | `Field K` → `IsDomain` | Low |
| I1 | `polynomial_eval₂_laurentSeries_*` | `Field K` → `IsDomain` | Low |
| I2 | `laurentSeriesMapRingHom` | ℤ/CommRing → Γ/Semiring, upstream bundled `HahnSeries.mapRingHom` | Low |
| J2 | `iteratedDeriv_sq_mul` | ℂ → 𝕜, upstream | Low |
| B4 | `analyticTaylor_comp_pow` | upstream `expand` bridge | Medium |
| C2 | `HasCoeffsIn` | `Algebra R A` → `PowerSeries.lifts (f : R →+* S)` | Medium |
| C3 | `IsIntegralPowerSeriesmod` | ℤ/ℂ → lifts + regular `c` | Low–Med |
| E3 | `polynomial_prod_coeff_*` ×2 | consolidate via `Subsemiring`/`Polynomial S` | Low–Med |
| F1 | jet soundness lemmas | window 37 → parameter N; merge with Qj conv layer | Low–Med |
| G2 | `coxDivisorSumAux` etc. | name it `ArithmeticFunction.dedekindPsi`, upstream, ℕ-valued `card_coxMatrix` | Medium |
| K3 | width/expand Laurent constructions | general `LaurentSeries.expand` | Medium |
| A4 | `rankTwoContent` + cyclic criterion | matrix content over GCD domain; n×n via D_{n−1} | Med–High |
| A1/A3 | HNF existence+uniqueness | 2×2/ℤ → n×n/ℤ (→ Bézout) | High |
| B2 | `poleOrder`/`laurentqExpansion` complex | cusp-specific → Laurent expansion of a meromorphic germ | High |
| H2 | `symmetric_bidegree_three_…` | bidegree 3, orders (−9,−3) → bidegree n, orders (−a,−b) + weight-injectivity | High |

**Refuted candidates** (look generalizable, aren't):
- `meromorphicAt_of_comp_pow` beyond ℂ — proof needs Riemann removable singularity + open mapping (`Complex.isOpenQuotientMap_pow`), both ℂ-only.
- uniqueness.lean pipeline beyond ℂ — identity theorem + `rank ℝ ℂ = 2` countable-complement connectivity + mathlib `PeriodPair` are all ℂ-lattice-specific; matches literature scope.
- Qj/link/LevelThree ℤ compute layer to `CommRing` — would destroy the `decide +kernel` certificates that are its entire purpose.
- `primeFinEquivCoxMatrix` beyond primes — false for composite m (|C(m)| = ψ(m) ≠ m+1).

Counts: **13 Low, 7 Medium (incl. Low–Med), 4 High**; 4 refuted.

### Sources
- [Hermite normal form — Wikipedia](https://en.wikipedia.org/wiki/Hermite_normal_form)
- [Hermite Canonical Form and Smith Canonical Form over a PID — ACM SIGSAM](https://dl.acm.org/doi/10.1145/101104.101105)
- [Divasón–Aransay, Hermite Normal Form (Isabelle AFP)](https://www.isa-afp.org/browser_info/current/AFP/Hermite/outline.pdf)
- [Dedekind psi function — Wikipedia](https://en.wikipedia.org/wiki/Dedekind_psi_function)
- [OEIS A001615 (Dedekind psi)](https://oeis.org/A001615)
- [Dedekind psi function — OeisWiki](https://oeis.org/wiki/Dedekind_psi_function)
