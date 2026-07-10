# What the seven FieldExamples tell us about Mathlib's NumberField API

Generated 2026-06-17. An analysis (not an inventory) of `XYin/NumberField/FieldExamples/`,
read through the lens: *given seven worked number fields, what is the state of the Mathlib
NumberField API?*

The seven case studies are
`ℚ(√2)`, `ℚ(√5)`, `ℚ(√−6)`, `ℚ(∛3)`, `ℚ(ζ₃)`, `ℚ(ζ₅)`, `ℚ(ζ₈)`,
each dissected into the *same* ~10 modules. Each module is, in effect, one **invariant** of
a number field. That uniform grid is what makes the folder a good probe of the API: the same
invariant is computed for a real quadratic, an imaginary quadratic, a pure cubic, a non-Galois
field, and three cyclotomic fields of two different signatures. Where the API is mature, the
proof is one line and identical across fields; where it is thin, each field re-derives it by hand.

---

## 1. Which invariants can we talk about, and at what generality?

The folder exercises essentially the entire classical "first course" invariant list. The table
records, per invariant, the **primary Mathlib API** the proofs lean on and **how general that
API is** — i.e. whether it works for an arbitrary number field or only after the user supplies
something field-specific.

| Invariant | Primary Mathlib API used | Generality of the API |
|---|---|---|
| **Ring of integers `𝓞 K`** | `NumberField.RingOfIntegers`, `IsIntegralClosure`, `PowerBasis`; cyclotomic: `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton` | **General as a *definition*, weak as a *computation*.** `𝓞 K` always exists, but there is **no general recognizer** for "`ℤ[θ] = 𝓞 K`". Cyclotomic fields get it free; quadratics/cubic must hand-prove maximality (Eisenstein, discriminant peeling). |
| **Integral / power basis** | `PowerBasis ℤ (𝓞 K)`, `AdjoinRoot.powerBasis`, `IsPrimitiveRoot.integralPowerBasis` | General **for monogenic fields**. All seven happen to be monogenic; Mathlib has no API for the non-monogenic case (which the folder never tests). |
| **Discriminant** | `NumberField.discr`, `Algebra.discr`, `Algebra.discr_powerBasis_eq_norm`, `IsCyclotomicExtension.Rat.discr_prime` | General formulas exist, but **bridging `NumberField.discr` (ℤ) ↔ `Algebra.discr ℚ` ↔ explicit basis** is manual every time (`NumberField.coe_discr`, change-of-basis matrices). |
| **Signature (r₁, r₂) / places** | `NumberField.InfinitePlace`, `nrRealPlaces`, `nrComplexPlaces`, `card_add_two_mul_card_eq_rank`, `IsTotallyReal`, `IsTotallyComplex` | **Fully general.** This is the most polished corner. Signature is recovered uniformly via `r₁ + 2r₂ = n` + `omega`. No packaged `signature : ℕ × ℕ`, but the pieces are all general. |
| **Galois group / Galois-ness** | `IsGalois`, `IsGalois.card_aut_eq_finrank`, cyclotomic: `autEquivPow`, `Rat.galEquivZMod`, `fromZetaAut`; closure: `Polynomial.SplittingField`, `Gal.galActionHom_bijective_of_prime_degree` | `IsGalois` general; **identifying the group** is only easy for cyclotomic (abelian, full API) or prime-degree (`S₃` for ∛3). No general `GaloisClosure` constructor. |
| **CM structure** | `NumberField.IsCMField`, `NumberField.maximalRealSubfield`, `IsCMField.ofCMExtension`, `units_rank_eq_units_rank` | **General predicate exists** (Mathlib has `CMField.lean`), but *establishing* CM-ness is per-shape: cyclotomic via `Rat.isCMField`, imaginary quadratic via `ofCMExtension`. No decision procedure. |
| **Prime splitting / ramification / inertia** | `Ideal.ramificationIdx`, `Ideal.inertiaDeg`, `Ideal.absNorm`, `isPrime_of_irreducible_absNorm`; Kummer–Dedekind: `primesOverSpanEquivMonicFactorsMod`, `RingOfIntegers.monicFactorsMod` | General over Dedekind domains. Mathlib **does** have a usable Kummer–Dedekind (`Ideal/KummerDedekind.lean`), but it needs `exponent θ = 1`, and the folder *also* carries a hand-rolled `genResidueHom` (Common.lean) because the packaged version is awkward to drive to a concrete factorization. |
| **Class group / class number** | `NumberField.classNumber`, `ClassGroup`, `ClassGroup.mk0`, `NumberField.minkowskiBound`, `isPrincipalIdealRing_of_isPrincipal_of_pow_le_…` | **General and effective.** Minkowski-bound → check primes `≤ ⌊M⌋` → principal. This is the second most polished corner; class number 1 is mechanically verifiable for all seven. |
| **Unit group: torsion** | `NumberField.Units.torsion`, `CommGroup.torsion`, `Rat.torsionOrder` | **Fully general** and effective. Torsion (= roots of unity) is identified cleanly in every field. |
| **Unit group: rank** | `NumberField.Units.rank` (= `#places − 1`), Dirichlet | **General** (existence/rank). |
| **Unit group: fundamental system** | `NumberField.Units.fundSystem`, `closure_fundSystem_sup_torsion_eq_top` | **General existence, NO effective identification.** `fundSystem` is `Quotient.out` — abstract. There is **no API to certify a concrete unit is fundamental.** ← *this is where 2 of the 5 sorries live.* |
| **Regulator** | `NumberField.Units.regulator`, `regOfFamily_div_regulator` | Defined generally as a covolume, but **only computable once a generating system is certified** (index 1). Blocked by the same gap as fundamental units. |
| **Norm-Euclidean** | bespoke `normEuclidean` statement; `Algebra.norm ℤ/ℚ`; the folder's own `abs_intNorm_lt_of_abs_norm_le` | **No Mathlib API at all.** Each field is proved from scratch by nearest-lattice-point rounding. ← *the other 3 sorries live here.* |
| **Local–global** | `IsDedekindDomain.HeightOneSpectrum`, `adicCompletion`, `InfinitePlace`, product formula, `NumberField.DedekindZeta` | Completions + product formula exist generally; **no Hasse–Minkowski**. The `LocalGlobal` modules assemble places + product formula, not an actual local-to-global solvability theorem. |

**One-line reading of the table.** Mathlib lets you *state* every classical invariant of a
general number field, and *compute* the "rigid" ones (signature, class number, torsion,
ramification data) effectively and uniformly. The invariants that remain hard are exactly the
ones whose classical computation needs **geometry of numbers with an effective constant**:
the fundamental units / regulator (lower bound on the regulator) and norm-Euclideanity
(covering radius of the lattice). Those are precisely the two families where sorries survive.

---

## 2. Are the proofs "ordinary mathematics"?

**Mostly yes, with a sharp split.** Where Mathlib's API matches the textbook object, the Lean
proof *is* the textbook proof, often one line:

- **Class number 1**: compute Minkowski bound, `interval_cases` the primes below it, check each
  ideal is principal — exactly how a number theorist does it by hand.
- **Splitting laws**: `splits_iff_pm_one_mod_eight` / `…_mod_five` reduce to a Legendre symbol
  via `ZMod.exists_sq_eq_two_iff` etc. — quadratic reciprocity, the natural argument.
- **Signature**: `r₁ + 2r₂ = [K:ℚ]` then count complex places — the natural argument.
- **Cyclotomic Galois group**: `Gal(ℚ(ζₙ)/ℚ) ≅ (ℤ/n)ˣ` straight from `Rat.galEquivZMod`.

Where the proofs **diverge from how a mathematician thinks**, it is almost always one of three
Lean-specific frictions, and they cluster in the *foundational* modules:

1. **Proving `ℤ[θ] = 𝓞 K` by hand.** A mathematician says "disc is squarefree-ish, done."
   The folder instead does explicit work: CubeRootThree peels coordinates from
   `a³+3b³+9c³−9abc ≡ 0 (mod 27)` (`CubeRootThree/RingOfIntegers.lean`), SqrtTwo invokes the
   Eisenstein criterion, SqrtFive solves congruences mod 5 and 25. This is real mathematics but
   at a level of granularity no human writes out — it is filling the gap left by a missing
   recognizer.
2. **Transport across presentations.** `ℚ(√5)` appears as `QuadraticAlgebra`, as `AdjoinRoot`,
   as golden-ratio and as radical (`SqrtFive/Basic.lean` carries ~5 models with equivalences).
   Coordinatizing an integer in "the" basis means chasing `RingOfIntegers.equiv` and `PowerBasis`
   defeq — pure encoding overhead invisible to ordinary mathematics.
3. **Determinants/norms by `decide`/matrix.** E.g. building the multiplication-by-θ matrix
   `!![0,0,3;1,0,0;0,1,0]` and computing `Matrix.det_fin_three` where the mathematician just
   writes the norm form `x³+3y³+9z³−9xyz`.

The **norm-Euclidean** proofs, by contrast, are textbook-faithful: round each coordinate to the
nearest integer, bound the fractional part, feed the contraction lemma
`abs_intNorm_lt_of_abs_norm_le`. That is exactly the classical argument — it just has no library
support, so it is rebuilt per field.

---

## 3. Why do the five sorries remain?

They are not random hard spots; they are **two specific, named API gaps**, and both are
*geometry-of-numbers-with-an-effective-constant* problems.

**Gap A — certifying a fundamental unit system (2 sorries: `CyclotomicFive/Units`,
`CyclotomicEight/Units`).**
`fundamentalUnitSystem_isFundamental` claims a concrete unit (`1+ζ₅`, resp. `1+√2`) together
with the roots of unity generates `𝓞ˣ`. Mathlib's `fundSystem` proves such a system *exists*
(Dirichlet) but is defined by `Quotient.out` — there is **no way to prove a *named* unit is
fundamental**. Classically you'd bound the regulator from below (Artin/Remak-type bound) and
show your candidate's regulator can't be a proper multiple; Mathlib has **no regulator lower
bound and no unit-search API**.

Tellingly, **`SqrtFive/Units` *proves* the analogous statement** (`fundamentalUnit_generates`)
*without* that missing API — via a self-contained real-embedding window reduction: send the
golden unit to `Φ>1` under the real embedding, scale any unit into `[1, Φ)`, and use
discreteness (`interval_cases` on bounded coordinates) to force it to be torsion. This works
because `ℚ(√5)` has **unit rank 1 with a real embedding** — a one-dimensional window. The
cyclotomic fields are **totally complex** (no real embedding) and/or higher effective rank, so
the window argument has no foothold and you genuinely need the missing analytic bound. This is
the cleanest single illustration in the whole project of an *API gap*, not a *mathematics gap*:
the same theorem is reachable in rank-1-real and unreachable elsewhere purely because of which
tools the library ships.

**Gap B — norm-Euclideanity in dimension ≥ 3 (3 sorries: `CubeRootThree`, `CyclotomicFive`,
`CyclotomicEight` `Euclidean.lean`).**
The four proved cases are all **degree 2**: the error norm form is binary, and `nlinarith` on
`|coord − round| ≤ 1/2` closes it. ∛3, ζ₅, ζ₈ are degrees 3, 4, 4; the error form is a
ternary/quaternary cubic/biquadratic, and bounding it over the unit cube is a genuine
**covering-radius** computation. These fields *are* classically norm-Euclidean — the obstruction
is the absence of any Mathlib **geometry-of-numbers / covering-radius API** (or the absence of an
Artin-style finite exhaustive enumeration helper). So again: a missing-library problem, modulo
the real mathematical depth that the dimension-2 → dimension-3 jump carries.

Both gaps share a root cause: **Mathlib's number-field API is strong on *existence/rank/abstract
structure* and on *rigid* invariants, but thin on *effective constants* from the geometry of
numbers** (lower bounds on the regulator, covering radii, Hermite-constant-type bounds).

---

## 4. What API development would help?

Ordered by leverage (how many of the seven fields / how many invariants each unblocks):

**P1 — Effective geometry-of-numbers constants (unblocks both sorry families).**
- A **regulator lower bound** (`regulator K ≥ f(disc, rank)`, Remak/Friedman-type) plus a
  `IsFundamentalSystem` certificate: "a family whose `regOfFamily` equals the minimal achievable
  regulator generates `𝓞ˣ / torsion`." This is the missing piece behind Gap A and would let the
  cyclotomic units be certified the way `SqrtFive` is, but in any rank/signature.
- A **covering-radius ⇒ norm-Euclidean** lemma:
  `(∀ x:K, ∃ q:𝓞 K, |N_{K/ℚ}(x − q)| ≤ c) → c < 1 → NormEuclidean (𝓞 K)`,
  together with a generic `roundInBasis : PowerBasis ℤ (𝓞 K) → K → 𝓞 K` and a Minkowski-embedding
  nearest-point helper. This collapses all seven `Euclidean.lean` files to "compute `c`."

**P2 — A `𝓞 K = ℤ[θ]` recognizer (unblocks ~half the RingOfIntegers boilerplate).**
A Kummer–Dedekind / Dedekind-criterion theorem of the shape
"`Squarefree (discr of minpoly)` (or the index-coprime-to-`p` Dedekind test) ⇒
`integralClosure ℤ K = Algebra.adjoin ℤ {θ}`." Would replace the bespoke peeling/Eisenstein/
congruence arguments in CubeRootThree, SqrtTwo, SqrtFive with one call.

**P3 — Packaged "read-off" invariants with decision procedures.**
- `signature K : ℕ × ℕ` with a `decide`-friendly computation (currently re-derived via
  `card_add_two_mul_card_eq_rank` + `omega` each time).
- A directly-applicable Kummer–Dedekind front-end: from `minpoly` factored mod `p`, *return* the
  factorization of `(p)` as a product of explicit primes with their `e`, `f` — so the hand-rolled
  `genResidueHom` in `Common.lean` becomes unnecessary.
- A `GaloisClosure K` construction with its automorphism group, so non-Galois fields (∛3) don't
  route through `Polynomial.SplittingField` by hand.

**P4 — Genuinely missing theory the folder gestures at but cannot reach.**
- **Hasse–Minkowski / local–global for quadratic forms**: the `LocalGlobal` modules currently
  assemble completions + the product formula but state no real local-to-global principle. A
  Hasse–Minkowski theorem would give these modules actual content.
- **CM-field decision support**: `IsCMField` exists but is established per-shape; a procedure for
  quadratic and for "totally complex quadratic over totally real" would generalize it.

**Bottom line.** These seven fields show Mathlib's NumberField API is already strong enough to
*state* every classical invariant of an arbitrary number field and to *compute*, uniformly and
naturally, the rigid ones — signature, class number, ramification, torsion. The remaining
friction is concentrated in two places, both about **effective geometry-of-numbers constants**
(fundamental-unit/regulator certification and covering radii) and in one **missing recognizer**
(`ℤ[θ] = 𝓞 K`). Building P1 and P2 would turn most of this folder's hand-work — and the five
surviving sorries — into routine API calls.
