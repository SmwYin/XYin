# Adversarial decomposition: Cox §11.B–C

## Scope and source

Primary source: David A. Cox, *Primes of the Form x² + ny²*, 2nd ed., supplied scan.
The scan has no text layer; every locator below was checked against a 300 dpi rendering.

The chapter has a stable offset

```text
PDF page = printed page + 12.
```

The formalized scope is the complete mathematical content needed for printed pp. 225–236:

- §11.B: definition of a `Γ₀(m)` modular function, Lemma 11.10, Theorem 11.9,
  Lemma 11.11, equations (11.12)–(11.17), and Exercises 11.7–11.11 used by the proofs;
- §11.C: Theorem 11.18(i)–(v), equations (11.19)–(11.22), Theorem 11.23,
  Lemma 11.24, and Exercises 11.12–11.18 used by the proofs;
- prerequisites explicitly requested by the user: lattice `Δ`, lattice `j`, Theorem 10.9,
  equation (7.8), and Theorem 11.2(ii)–(iii).

Historical/bibliographical prose is out of scope.  The displayed polynomial (11.22) is in scope
as a verification theorem.

## Statement skeleton and build gate

The declarations are physically present under `XYin/PhD/Cox/` and contain `:= by sorry` (or a
definition with a `by sorry` body) exactly because this is the `/develop` planning phase.

| Layer | Skeleton file | Main source targets |
|---|---|---|
| HNF | `HermiteNormalForm.lean` | Exercises 7.15, 11.16, 11.17 |
| lattice `j` | `LatticeJ.lean` | Proposition 10.7; Theorems 10.9, 11.2 |
| modular functions | `ModularFunction.lean` | Lemma 11.10; Theorem 11.9 |
| representatives | `CoxMatrices.lean` | Lemma 11.11; (11.12), (11.13) |
| modular equation | `ModularPolynomial.lean` | (11.14)–(11.17); 11.18(i),(ii) inputs |
| cyclic sublattices | `CyclicSublattice.lean` | Lemma 11.24; Theorem 11.23 |
| arithmetic | `Arithmetic.lean` | Theorem 11.18(i)–(v); (11.19)–(11.22) |
| umbrella | `Section11BC.lean` | complete scope |

`lake build` succeeds for the full repository at this skeleton revision.  Existing project
warnings and old project sorries remain, but there are no elaboration or build errors.

The declarations follow the one-conclusion rule:

- Theorem 11.9 is split into `theorem_11_9_i` and `theorem_11_9_ii`.
- Lemma 11.10 is split into the constant and polynomial conclusions.
- Theorem 11.18 has separate declarations for (i), (ii), (iii), the two conclusions of (iv),
  and (v).
- Lemma 11.24 is represented by a single equivalence, since existence and uniqueness are the
  two directions of one classification statement.

## Existing API audit

### Reuse without new axioms

- `PeriodPair.lattice`, `latticeBasis`, `latticeEquivProd`, `G`, `g₂`, `g₃` from mathlib.
- `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq` and `invariantsDetermineLattice` from
  `XYin/uniqueness.lean`.  Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Project analytic `j`, `j_slashInvariant`, `j_HasIntegralQExpansion`, `j_poleOrder`, `jN`,
  and `jN_slashInvariant`.
- Mathlib `ModularForm.discriminant`, `discriminant_ne_zero`, and
  `discriminant_eq_E₄_cube_sub_E₆_sq`.
- Mathlib fundamental-domain API (`ModularGroup.fd`, `exists_smul_mem_fd`, compact truncated
  domains), meromorphic order/divisor API, and finite quotient/index API.
- `Module.Basis.SmithNormalForm`, `Submodule.quotientEquivPiZMod`, and determinant/index
  lemmas are models or supporting tools; mathlib has no HNF API.

### Reuse after repair

The `main` branch contains a nearly complete implementation of the requested three-step
injectivity route.  The scaling and change-of-basis portions are axiom-clean.  Its analytic
bridge currently imports `sorryAx` through the old `Delta_E4_eqn`; the plan replaces that
dependency with mathlib's discriminant theorems before porting it.

### Historical code that is evidence, not an implementation dependency

The deleted `main:XYin/PhD/Test/JLevelN/` experiment provides useful proof prototypes, but it
must not be restored wholesale.  Its known defects are:

1. an individual transformed root was connected to `laurentqExpansion 1`; its correct width is
   `m`, with local parameter `q^(1/m)`;
2. `Irreducible (modularPolynomial m)` did not make Cox's `X` variable direction precise;
3. the general `C(m)`/right-coset theorem remained a sorry and had no HNF foundation;
4. parts (ii) and (iii) were treated as unavailable even though Exercise 11.10 is in the scan
   and symmetry has a non-circular proof after Theorem 11.23;
5. several apparently implemented results still had transitive `sorryAx` dependencies.

The new skeleton explicitly fixes all five.

## Source-to-Lean decomposition

The short source anchors below are either theorem formulas or very short phrases.  They are
included to pin the statement, not to reproduce the book's prose.

### A. Lattice invariants and analytic `j`

#### A1. Scaling and the definitions

Source anchor, printed p. 206 / PDF p. 218:

```text
Δ(L) = g₂(L)^3 - 27 g₃(L)^2,
j(L) = 1728 g₂(L)^3 / Δ(L).
```

Lean mapping:

- `PeriodPair.discriminant`, `PeriodPair.j` (`LatticeJ.lean:45–48`);
- `G_smul`, `g₂_smul`, `g₃_smul`, `discriminant_smul`, `j_smul` (`:56–74`).

The source scaling convention is `g₂(aL)=a⁻⁴g₂(L)` and `g₃(aL)=a⁻⁶g₃(L)`.  Lean uses
`a : ℂˣ`, which makes every division/cancellation hypothesis explicit and eliminates a recurring
`a = 0` side case.

Attacks:

1. **Normalization attack:** omitting `1728` changes every integral modular polynomial.  The
   skeleton uses Cox's normalization exactly.
2. **Zero-scale attack:** allowing `a : ℂ` would make homothety false at `a=0`.  Units are
   necessary.
3. **Basis-vs-lattice attack:** `g₂_congr` and `g₃_congr` state invariance under equality of
   lattices, so later constructions never depend on an arbitrary ordered basis.

#### A2. Nonzero discriminant and homothety classification

Source anchors, Proposition 10.7 and Theorem 10.9, printed pp. 206–208 / PDF pp. 218–220:

```text
Δ(L) ≠ 0,
j(L)=j(L') ↔ L and L' are homothetic.
```

Lean mapping:

- `PeriodPair.discriminant_ne_zero` (`LatticeJ.lean:88`);
- `j_eq_of_homothetic`, `homothetic_of_j_eq`, `j_eq_iff_homothetic` (`:92–103`).

For the hard direction, equal `j` values are split into the special cases `g₂=0` (`j=0`),
`g₃=0` (`j=1728`), and the generic case.  In each case a fourth/sixth root supplies a unit
scaling; the existing uniqueness theorem then identifies the lattices.

Attacks:

1. **Exceptional-value attack:** dividing by `g₂g₃` loses `j=0` and `j=1728`; the case split is
   mandatory.
2. **Statement attack:** uniqueness proves equality of `lattice`, not equality of `PeriodPair`;
   the target is correctly `Homothetic`.
3. **Axiom attack:** the proof may use `IsAlgClosed ℂ` and `uniqueness.lean`, but must not inherit
   the old `Delta_E4_eqn` sorry.

#### A3. The analytic/lattice bridge

Source anchor, printed p. 220 / PDF p. 232:

```text
j(τ)=j([1,τ]).
```

Lean mapping:

- `UpperHalfPlane.periodPair` (`LatticeJ.lean:110`);
- `periodPair_g₂_eq_E4`, `periodPair_g₃_eq_E6`, `Delta_eq_E4_E6`,
  `j_eq_periodPair_j` (`:125–143`).

The constants are fixed as

```text
g₂([1,τ]) = (4π⁴/3) E₄(τ),
g₃([1,τ]) = (8π⁶/27) E₆(τ).
```

Attacks:

1. **Constant attack:** a factor-of-two error in mathlib's Eisenstein-series normalization
   destroys the bridge; both constants are separate public lemmas.
2. **Denominator attack:** cross multiplication needs both discriminants nonzero.
3. **Prior-proof attack:** the repaired proof must identify project `Delta` with mathlib
   `ModularForm.discriminant` pointwise before using the sorry-free cubic relation.

#### A4. Injectivity up to `SL₂(ℤ)` and surjectivity

Source anchors, equation (7.8), printed p. 138 / PDF p. 150, and Theorem 11.2(ii)–(iii),
printed p. 221 / PDF p. 233:

```text
[1,τ] ~ [1,τ'] ↔ ∃γ∈SL₂(ℤ), γτ=τ',
j(τ)=j(τ') ↔ ∃γ∈SL₂(ℤ), γτ=τ',
j : ℍ → ℂ is surjective.
```

Lean mapping: `periodPair_homothetic_iff_exists_sl2_smul_eq`,
`j_eq_iff_exists_sl2_smul_eq`, and `j_surjective` (`LatticeJ.lean:153–165`).

Attacks:

1. **Orientation attack:** a lattice basis change initially lies in `GL₂(ℤ)` with determinant
   `±1`; positivity of both imaginary parts is what excludes `-1`.
2. **Action-direction attack:** the theorem fixes `γ • τ = τ'`, not the inverse convention.
3. **Surjectivity-boundary attack:** compactness/open-closed arguments must account for the pole
   at the cusp and may not silently evaluate `j` at `∞` as a finite value.

### B. Modular functions and Theorem 11.9(i)

#### B1. Definition at every cusp

Source, printed pp. 225–226 / PDF pp. 237–238.  Exact formula anchor:

```text
f(γτ)=∑ a_n q^(n/m), with only finitely many negative terms.
```

Lean mapping: `IsGamma0ModularFunction`, `periodic_comp_sl2`, and
`cusp_laurent_finitePrincipalPart` (`ModularFunction.lean:27,57,64`).

Attacks:

1. **Holomorphicity attack:** Theorem 11.9 permits poles inside `ℍ`; the predicate uses
   `MeromorphicAt`, not `MDiff`.
2. **Cusp attack:** checking only `∞` is insufficient for `Γ₀(m)`; the definition quantifies over
   every `γ : SL₂(ℤ)`.
3. **Width attack:** period/expansion width `m` is valid for every transformed cusp even when the
   minimal cusp width is a divisor of `m`.

#### B2. Lemma 11.10

Short source anchors, printed p. 226 / PDF p. 238: “is constant”; “a polynomial in j(τ)”.

Lean mapping: `levelOne_constant_of_holomorphic` and
`levelOne_polynomialInJ_of_holomorphic` (`ModularFunction.lean:85,93`).

The constant theorem uses reduction to a truncated fundamental region and maximum modulus.
The polynomial theorem removes the finite principal part at `∞` using `j=q⁻¹+O(1)` and then
applies the constant theorem.

Attacks:

1. **Compactness attack:** the untruncated fundamental domain is not compact; bounded imaginary
   part and the cusp limit are separate cases.
2. **Principal-part attack:** the proof needs the leading coefficient of `j` to be exactly one.
3. **Internal-pole attack:** the polynomial conclusion assumes `MDiff f` on `ℍ`; it cannot be
   applied directly to arbitrary meromorphic `f` in Theorem 11.9(i).

#### B3. Pole clearing and Theorem 11.9(i)

Source formulas, printed pp. 227–228 / PDF pp. 239–240:

```text
(j(τ)-j(τ₀))^r f(τ),
(j(τ)-1728)^(r/2) f(τ),
j(τ)^(r/3) f(τ).
```

Lean mapping: `levelOne_exists_polynomial_clearing_poles` and `theorem_11_9_i`
(`ModularFunction.lean:101,107`).

Attacks:

1. **Infinite-pole attack:** one must first prove finitely many pole orbits in a compact
   fundamental-region truncation.
2. **Ramification attack:** ordinary points use a simple zero of `j-j(τ₀)`, while `i` and
   `exp(2πi/3)` have stabilizer orders two and three; treating them uniformly is false.
3. **Meromorphic-equality attack:** the rational expression is asserted only where the
   denominator is nonzero (`RationalIn`), avoiding false pointwise claims at poles.

Internal-node attack on Theorem 11.9(i): even if every pole is cleared, the clearing polynomial
could be zero.  The skeleton explicitly requires `P ≠ 0`, and division is guarded by its zero
set.  This node survives.

### C. Hermite normal form and `C(m)`

#### C1. General HNF API

Source motivation: Exercise 11.17, printed p. 247 / PDF p. 259.  Formula anchor:

```text
L'=[d,aτ+b],  d>0, a>0, 0≤b<d.
```

Lean mapping: `Matrix.IsColumnHermiteNormalForm` and
`Module.Basis.HermiteNormalForm` (`HermiteNormalForm.lean:26,46`).

The structure parallels `Module.Basis.SmithNormalForm` but fixes the ambient basis `bM` as a
parameter.  Its relation is the full matrix of `N.subtype` from `bN` to `bM`.

Attacks:

1. **Uniqueness attack:** HNF is not canonical if the ambient basis is allowed to vary; fixing
   `bM` is essential.
2. **Row/column attack:** generators are columns.  Rank two therefore has matrix
   `!![d,b;0,a]`, not its transpose.
3. **Range attack:** `0≤b<d` uses the first pivot `d`; reducing modulo `a` gives the wrong normal
   form for `[d,aτ+b]`.

#### C2. Existence, uniqueness, index, cyclic quotient

Source anchors: Exercise 7.15, printed p. 152 / PDF p. 164; equation (11.25) and Exercise 11.16,
printed pp. 235,247 / PDF pp. 247,259:

```text
index = |det A|,
L/L' cyclic ↔ gcd(a,b,c,d)=1.
```

Lean mapping: `exists_hermiteNormalForm`, `matrix_eq`, `index_eq_natAbs_det`, and
`quotient_isAddCyclic_iff_rankTwoContent_eq_one` (`HermiteNormalForm.lean:67,76,82,97`).

Attacks:

1. **Rank attack:** HNF existence requires the submodule to have full rank; without it, a square
   positive-diagonal matrix cannot exist.
2. **SNF attack:** mathlib's existing `SmithNormalForm` does not record divisibility-normalized
   invariant factors, so cyclicity cannot be inferred from it without an additional proof.
3. **Primitive attack:** gcd-one is equivalent to a cyclic quotient, not part of the definition
   of HNF.  The skeleton keeps these layers separate.

#### C3. Cox representatives

Source anchor, printed p. 228 / PDF p. 240:

```text
C(m)={[[a,b],[0,d]] : ad=m, a>0, 0≤b<d, gcd(a,b,d)=1}.
```

Lean mapping: `CoxMatrix`, `mobiusMatrix`, `inclusionMatrix`, `act`
(`CoxMatrices.lean:24,47,51,67`).

Attacks:

1. **Diagonal-swap attack:** Möbius matrix `[[a,b],[0,d]]` and HNF inclusion matrix
   `[[d,b],[0,a]]` are distinct; both are named.
2. **Finiteness attack:** `b<d≤m` is needed to construct the `Fintype`, not merely asserted.
3. **Positivity attack:** `d>0` is derived from `ad=m>0`; otherwise `act` would not preserve
   `ℍ`.

### D. Cosets and transformed q-expansions

#### D1. Lemma 11.11 and the cardinality formula

Source, printed pp. 228–229 / PDF pp. 240–241.  Short anchor: “one-to-one correspondence”.

```text
Γ₀(m)\SL₂(ℤ) ≃ C(m),
|C(m)|=m∏_{p|m}(1+1/p).
```

Lean mapping: `coxMatrixEquivRightCosets`, `card_coxMatrix`
(`CoxMatrices.lean:118,154`).

Attacks:

1. **Side attack:** Cox uses right cosets; a left quotient reverses the transformation law in
   (11.12).
2. **Primitive attack:** all determinant-`m` HNF matrices classify finite-index sublattices, but
   only primitive ones classify these right cosets/cyclic quotients.
3. **Counting attack:** the Euler product is written in `ℚ` so division by primes is literal;
   the left side remains a natural cardinal cast to `ℚ`.

#### D2. Equations (11.12) and (11.13)

Source, printed p. 229 / PDF p. 241:

```text
j(mγτ)=j(στ),
j(στ)=ζ_m^(-ab)t^(-a²)+∑_{n≥0} c_n ζ_m^(abn)t^(a²n), t=q^(1/m).
```

Lean mapping: `rightCosetEval_equiv`, `transformedJSeries`,
`laurentqExpansion_coxAction`, `reindex_bijective` (`CoxMatrices.lean:137,177,203,213`).

Attacks:

1. **Width regression:** the analytic Laurent expansion is at width `m`; width `1` is false for
   an individual root and was a defect in the historical experiment.
2. **Exponent attack:** since `ad=m`, `q(στ)=ζ_m^(ab)t^(a²)`; the exponent is `a²`, not `a/d` in
   the `t` variable.
3. **Support attack:** the formal Laurent support is bounded below by `-a²`, so the Hahn/Laurent
   series constructor is legitimate.
4. **Galois attack:** `b↦bk mod d` preserves `gcd(a,b,d)=1` only because `k` is coprime to `m`
   and hence to `d`.

### E. The modular equation and Theorem 11.9(ii)

#### E1. Equations (11.14) and (11.15)

Source, printed p. 230 / PDF p. 242:

```text
Φ_m(X,j(τ))=∏_i(X-j(mγ_iτ))=∏_{σ∈C(m)}(X-j(στ)).
```

Lean mapping: `BivariatePolynomial`, `existsUnique_modularPolynomialC`,
`modularPolynomialC_specializeY`, and `modularPolynomialC_rightCosetProduct`
(`ModularPolynomial.lean:22,76,89,94`).

Variable convention: outer `Polynomial.X` is Cox's root variable `X`; the inner coefficient
variable is Cox's `Y`.  Semantic evaluation is `Φ.eval x y := Φ.evalEval y x`.

Attacks:

1. **Variable-direction attack:** this convention makes “irreducible in X” an outer-polynomial
   statement over `ℂ(Y)` and resolves the old ambiguity.
2. **Normalization attack:** uniqueness includes monicity in `X`; otherwise any nonzero scalar
   multiple satisfies the same root equation.
3. **Specialization attack:** equality for every `τ` determines coefficients because analytic
   `j` is surjective; without A4, uniqueness would be unjustified.

#### E2. Equations (11.16) and (11.17)

Source, printed pp. 230–231 / PDF pp. 242–243:

```text
G(X,τ)=∑_i f(γ_iτ)∏_{j≠i}(X-j(mγ_jτ)),
f(τ)=G(j(mτ),j(τ))/∂_XΦ_m(j(mτ),j(τ)).
```

Lean mapping: `interpolationAt`, `interpolation_coeff_isLevelOne`, `recoveryFormula`, and
`theorem_11_9_ii` (`ModularPolynomial.lean:111,121,130`; `ModularFunction.lean:115`).

Attacks:

1. **Representative attack:** `rightCosetTranslate` takes modularity as an argument so the
   translate is independent of the chosen representative.
2. **Collision attack:** specialized roots can collide at CM points.  `recoveryFormula` therefore
   assumes its derivative denominator is nonzero instead of claiming false pointwise equality.
3. **Function-field attack:** irreducibility/separability is used over `ℂ(j)`, while the final
   `RationalInTwo` equality is guarded away from the denominator's zeros.

Internal-node attack on Theorem 11.9(ii): modularity of `G`'s coefficients alone gives only
`ℂ(j)` coefficients; it does not recover `f` until the Lagrange evaluation and separability leaf
are established.  The plan keeps these as distinct tickets.  This node survives.

### F. Theorem 11.18

#### F1. Part (i): integrality

Source, printed pp. 231–232 / PDF pp. 243–244.  Short anchor: “coefficients are integers”.

Lean mapping: `hasse_qExpansion_principle`, `coxPhiFunction_coeff_integerLaurent`,
`exists_modularPolynomialZ`, `modularPolynomial`, `theorem_11_18_i`
(`ModularPolynomial.lean:146–172`; `Arithmetic.lean:15`).

Proof leaves:

1. (11.13) places roots over a cyclotomic Laurent-series field.
2. `reindex_bijective` proves Galois automorphisms permute roots.
3. Symmetric coefficients are rational; their coefficients are algebraic integers, hence
   ordinary integers.
4. Period one eliminates non-integral powers of `q`.
5. Hasse's leading-term induction upgrades `A(j)∈ℤ((q))` to `A∈ℤ[X]`.

Attacks:

1. **Fixed-field attack:** Galois-fixed gives rational, not automatically integral; algebraic
   integrality is a separate hypothesis.
2. **Exponent attack:** rational coefficients in `q^(1/m)` do not imply integer exponents;
   level-one periodicity supplies that step.
3. **Bridge attack:** formal integrality is useless until `laurentqExpansion_coxAction` identifies
   it with the analytic root.

#### F2. Part (ii): irreducibility in `X`

Source: Exercise 11.10, printed p. 246 / PDF p. 258.  Short anchor: “irreducible … in X”.

Lean mapping: `modularPolynomialC_irreducibleInX`, `theorem_11_18_ii`
(`ModularPolynomial.lean:140`; `Arithmetic.lean:22`).

The target is

```text
Irreducible (map (ℂ[Y] → ℂ(Y)) Φ_m) in ℂ(Y)[X].
```

Attacks:

1. **Ring attack:** irreducibility in `ℤ[Y][X]`, `ℂ[Y][X]`, and `ℂ(Y)[X]` are not definitionally
   identical; the source proof counts embeddings over `ℂ(j)` and first yields the field target.
2. **Distinctness attack:** different right cosets must give different conjugates; (11.13) is the
   discriminator.
3. **Degree attack:** the number of embeddings gives a lower bound only after proving each map is
   a genuine base-field embedding.

#### F3. Part (iii): symmetry

Source statement, printed pp. 231–232 / PDF pp. 243–244:

```text
m>1 → Φ_m(X,Y)=Φ_m(Y,X).
```

Cox points to Lang for the proof.  The plan instead uses only later material in the supplied Cox
section: Theorem 11.23 and the dual inclusion `mL⊂L'⊂L`.  This is non-circular because Theorem
11.23 depends on (11.15), HNF, and surjectivity, not on symmetry.

Lean mapping: `CyclicSublattice.dual`, `modularPolynomial_dvd_swap`,
`theorem_11_18_iii` (`CyclicSublattice.lean:55`; `Arithmetic.lean:29,35`).

Attacks:

1. **Circularity attack:** Theorem 11.23 must be proved before symmetry without importing
   `Arithmetic.lean`; the file graph enforces this.
2. **Unit/sign attack:** identical zero loci give associates, not equality.  Irreducibility,
   monicity, swapping twice, and a diagonal/degree argument eliminate the unit and `-1` cases.
3. **Edge attack:** `m=1` is excluded exactly as in the source.

#### F4. Part (iv): diagonal degree and leading coefficient

Source, equation (11.19), printed p. 233 / PDF p. 245:

```text
j(τ)-j(στ)=q⁻¹-ζ_m^(-ab)q^(-a/d)+nonnegative t-powers.
```

Short source anchor for the conclusion: “it must be ±1”.

Lean mapping: `modularPolynomialDiagonal_leadingCoeff_isRootOfUnity`,
`theorem_11_18_iv_degree`, `theorem_11_18_iv_leadingCoeff`
(`Arithmetic.lean:45,51,56`).

Attacks:

1. **Tie attack:** if `a=d`, the two polar exponents coincide and may cancel.  `m` nonsquare is
   precisely what rules this out.
2. **Product attack:** leading coefficients multiply only after proving every factor is nonzero
   and using Laurent-series order multiplicativity in a domain.
3. **Degree attack:** root-of-unity leading coefficient does not by itself prove degree `>1`;
   the factor from `sigmaZero` has pole order `m>1`.

#### F5. Part (v): Kronecker congruence

Source, equations (11.20)–(11.21), printed pp. 233–234 / PDF pp. 245–246:

```text
j(σ_iτ)≡j(σ_0τ) mod (1-ζ_p),
j(σ_pτ)≡j(τ)^p mod (1-ζ_p),
Φ_p≡(X^p-Y)(X-Y^p) mod p.
```

Lean mapping: `primeCoxMatrixEquiv`, `jLaurentSeriesMod`, `specializeJMod`,
`specializeJMod_injective`, `kronecker_after_specializeJ`, `theorem_11_18_v`
(`Arithmetic.lean:63–103`).

Attacks:

1. **Prime-two attack:** any cyclotomic norm lemma with an odd-prime hypothesis needs a separate
   `p=2` branch; the final theorem covers every prime.
2. **Ideal attack:** divisibility by `1-ζ_p` of an ordinary integer implies divisibility by `p`
   only after Exercise 11.13's norm argument.
3. **Hasse attack:** equality after substituting `Y=j` must be lifted by an injective substitution
   theorem (`specializeJMod_injective`), not by informal coefficient comparison.
4. **Frobenius attack:** `c_n^p≡c_n` uses that the `c_n` are integers, so F1/Thm 11.8 is a hard
   dependency.

Internal-node attack on Theorem 11.18: parts (iii) and (v) both need (i), but for different
reasons (normalization/integrality versus reduction modulo `p`).  Neither may be scheduled before
integer descent.  The ticket graph enforces this.  This node survives.

### G. Lemma 11.24 and Theorem 11.23

#### G1. A basis-independent cyclic sublattice object

Source definition, printed p. 235 / PDF p. 247.  Short anchor: “cyclic of index m”.

Lean mapping: `PeriodPair.CyclicSublattice`, `toPeriodPair`, `j`, `scale`, `dual`
(`CyclicSublattice.lean:18–57`).

Attacks:

1. **Duplicate-basis attack:** storing an arbitrary `PeriodPair` for `L'` gives many values for
   the same sublattice.  The structure stores only a carrier submodule; HNF chooses a canonical
   period pair later.
2. **Relative-quotient attack:** the quotient is `L.lattice ⧸ carrier`, not `ℂ/L'`.
3. **Scaling attack:** index and cyclicity must be transported through a lattice equivalence;
   equality of ambient complex sets alone is insufficient.

#### G2. Lemma 11.24

Source, printed pp. 235–236 / PDF pp. 247–248:

```text
L'=d[1,στ], with a unique σ∈C(m).
```

Lean mapping: `CoxMatrix.sublattice`, `toCyclicSublattice`,
`cyclicSublatticeEquivCoxMatrix`, `cyclicSublattice_hnf_matrix`,
`coxMatrix_toPeriodPair_lattice` (`CyclicSublattice.lean:72–101`).

Attacks:

1. **Existence attack:** the least positive real integer in `L'` is encoded algebraically by
   HNF, avoiding an order-theoretic search in `ℂ`.
2. **Uniqueness attack:** uniqueness is relative to the fixed ambient basis `[1,τ]`; HNF matrix
   uniqueness supplies it.
3. **Cyclicity attack:** determinant `m` proves the index; gcd-one separately proves the quotient
   cyclic.  Neither implies the other.

#### G3. Theorem 11.23

Source, printed pp. 235–236 / PDF pp. 247–248:

```text
Φ_m(u,v)=0 ↔ ∃ L'⊂L cyclic of index m, u=j(L'), v=j(L).
```

Lean mapping: `modularPolynomialC_zero_iff_normalizedCyclicSublattice`, `theorem_11_23`
(`CyclicSublattice.lean:104,112`).

Attacks:

1. **Surjectivity attack:** the forward direction chooses `τ` with `j(τ)=v`; this is exactly
   A4 and cannot be replaced by injectivity.
2. **Normalization attack:** the reverse direction normalizes any lattice to `[1,τ]` and must
   transport the sublattice, index, cyclicity, and both `j` values through the same scaling.
3. **Dependency attack:** the proof uses only the complex product formula (11.15), not
   Theorem 11.18(iii); this keeps the symmetry route non-circular.

Internal-node attack: `Φ_m(u,v)=0` over `ℤ` is evaluated after coefficient mapping to `ℂ` using
the custom semantic variable order.  The skeleton's theorem statement makes both operations
explicit.  This node survives.

### H. Explicit example (11.22)

Source: printed p. 234 / PDF p. 246.  Lean mapping:
`modularPolynomialThreeExplicit` and `modularPolynomial_three` (`Arithmetic.lean:106,118`).

Attacks:

1. **OCR attack:** the final factor was visually verified as `22973`.
2. **Variable attack:** the formula uses the same outer-`X`, inner-`Y` convention as the general
   modular polynomial.
3. **Computation attack:** this is a theorem to prove from the canonical polynomial, not a new
   definition of `Φ₃`; it cannot mask a normalization error.

## B2 and prior-failure audit

`.mathlib-quality/b2_log.jsonl` did not exist.  It has been created as an empty JSONL file, so
there are no recorded prior B2 failures to replay.

The older scoped decomposition/tickets for Theorem 11.18 were also reviewed as prior art.  Their
open issues are resolved at the statement level as follows:

| Prior issue | Resolution in this skeleton |
|---|---|
| analytic/formal bridge unspecified | exact width-`m` equality `laurentqExpansion_coxAction` |
| “irreducible in X” ambiguous | outer variable is Cox `X`; target is `ℂ(Y)[X]` |
| no HNF | fixed-basis column HNF plus index/cyclic quotient layers |
| symmetry source absent | non-circular proof via Theorem 11.23 and dual sublattice |
| old injectivity inherited `sorryAx` | replace old Delta bridge with mathlib discriminant API |

## Confidence gate

- [x] Complete source pages and referenced exercises visually checked.
- [x] Every planned public declaration is physically stated in Lean.
- [x] `lake build` succeeds for the entire repository.
- [x] Every source result has an exact locator and a Lean/source mapping above.
- [x] Every leaf group has at least three distinct attacks; every major internal node is attacked.
- [x] Historical B2 log checked (empty) and prior experimental failures incorporated.
- [x] No unavailable external source blocks the plan: symmetry uses a supplied-Cox alternative.
- [x] Hard leaves are identified rather than hidden: HNF existence/uniqueness, meromorphic pole
  orbits, the analytic/formal q-expansion bridge, Galois descent, and Hasse injectivity.

The decomposition gate passes for planning.  Proof execution remains intentionally unstarted
until the user approves `plan-cox11bc.md` and `tickets-cox11bc.md`.
