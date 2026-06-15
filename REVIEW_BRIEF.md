# Review brief — `FieldExamples`: worked number-field case studies in Lean / mathlib

*Prepared 2026-06-15 for an algebraic number theorist. Self-contained: no repository access required.*

*Purpose of this brief.* The author maintains a library of fully worked-out arithmetic of seven explicit number fields, formalised in the Lean 4 proof assistant on top of mathlib. The library is intended both as a reference and as a **demonstration / case study of mathlib's current `NumberField` API**. The two things we would value most from a reviewer are:

1. **Soundness and meaningfulness.** For each field we prove a fixed list of invariants (ring of integers, discriminant, splitting of primes, class group, unit group, Galois group, Euclidean status, local–global data). Are all of these statements *mathematically meaningful and correctly stated*? Is anything stated in a way that is vacuous, weaker than it appears, or subtly wrong?
2. **Redundancy.** The seven fields are developed from a uniform per-field template. Is the resulting structure the right amount of repetition, or are there results that should be proved once, generically, rather than seven times?

A standing third question runs through the whole brief: **does this collection make a good showcase of the algebraic-number-theory API that mathlib currently offers** — and where does it instead reveal gaps in that API?

---

## 1. Goal

We formalise, completely and explicitly, the standard first-course arithmetic of seven small number fields:

- three real or imaginary **quadratic** fields: $\mathbb{Q}(\sqrt 2)$, $\mathbb{Q}(\sqrt 5)$, $\mathbb{Q}(\sqrt{-6})$;
- one **pure cubic** field: $\mathbb{Q}(\sqrt[3]{3})$;
- three **cyclotomic** fields: $\mathbb{Q}(\zeta_3)=\mathbb{Q}(\sqrt{-3})$, $\mathbb{Q}(\zeta_5)$, $\mathbb{Q}(\zeta_8)$.

For each field $K$ we aim to establish, with machine-checked proofs: a ground-truth model of $K$ and of $\mathcal{O}_K$ with an explicit integral basis; the discriminant $d_K$; the splitting type of a sample of rational primes together with a general residue-class splitting criterion; the class number $h_K$ and the structure of the class group; the structure of the unit group $\mathcal{O}_K^\times$ (torsion, rank, a fundamental unit, the regulator); the Galois group of $K$ (and of its Galois closure where $K/\mathbb{Q}$ is not normal); whether $\mathcal{O}_K$ is norm-Euclidean; and a package of local–global data (finite and infinite places, completions, the product formula, the canonical and mixed embeddings, the house, adeles, and the Dedekind zeta function).

The fields were chosen to exhibit a spread of phenomena: trivial vs. nontrivial class group; PID/UFD vs. neither; totally real vs. totally complex vs. mixed signature; normal vs. non-normal; cyclic, Klein-four, and trivial Galois groups; norm-Euclidean vs. provably not Euclidean.

---

## 2. Background and references

### 2.1. Setting and conventions

Throughout, $K$ is a number field, $\mathcal{O}_K$ its ring of integers, $d_K = \operatorname{disc}(K/\mathbb{Q})$ the absolute discriminant, $h_K$ the class number, and $\mathcal{O}_K^\times$ the unit group. For a quadratic or cubic generator $\theta$ we write the field norm of $x+y\theta\;(+z\theta^2)$ as an explicit integral form $N(x,y,\dots)$. For a prime $\mathfrak p \mid p$ we write $e(\mathfrak p\mid p)$ for the ramification index and $f(\mathfrak p \mid p)$ for the residue (inertia) degree. The Minkowski constant for signature $(r_1,r_2)$ and degree $n$ is $\left(\tfrac{4}{\pi}\right)^{r_2}\tfrac{n!}{n^n}\sqrt{|d_K|}$.

For cyclotomic fields $\zeta_m$ denotes a fixed primitive $m$-th root of unity and $\Phi_m$ the $m$-th cyclotomic polynomial. We use the convention that the *regulator* of a rank-$r$ unit group is the covolume of the logarithmic unit lattice (so the regulator of a field of unit rank $0$ is $1$).

A note on what "proved" means here: every statement called *established* below is a theorem with a complete machine-checked proof and no appeal to unproved hypotheses. Statements flagged with a status note are the ones still standing on an unproved lemma (`sorry`); these are collected in §8.

### 2.2. References

The development follows the standard textbook treatment of these examples. The main background references are:

- [Marcus] Daniel A. Marcus. *Number Fields*. 2nd ed. Universitext. Springer, 2018. (Pure-cubic and cyclotomic examples; the discriminant of $\mathbb{Q}(\sqrt[3]{m})$; Minkowski-bound class-number computations.)
- [Neukirch] Jürgen Neukirch. *Algebraic Number Theory*. Grundlehren 322. Springer, 1999. (Places, completions, the product formula, the canonical embedding, the analytic class number formula.)
- [Washington] Lawrence C. Washington. *Introduction to Cyclotomic Fields*. 2nd ed. GTM 83. Springer, 1997. (Ring of integers, discriminant, units, and cyclotomic units of $\mathbb{Q}(\zeta_m)$.)
- [Cohen] Henri Cohen. *A Course in Computational Algebraic Number Theory*. GTM 138. Springer, 1993. (Explicit splitting via Kummer–Dedekind; fundamental-unit and regulator computations.)
- [Lemmermeyer] Franz Lemmermeyer. "The Euclidean algorithm in algebraic number fields." *Expositiones Mathematicae* 13 (1995), 385–416. (Survey of which rings of integers are norm-Euclidean; relevant to $\mathbb{Q}(\sqrt[3]{3})$ and the quartic cyclotomic fields.)
- [mathlib] The mathlib4 library, in particular its `NumberField`, `RamificationInertia`, `Ideal.absNorm`, `NumberField.Units`, `IsCyclotomicExtension`, `FinitePlace`/`InfinitePlace`, and `mixedEmbedding` developments.

> *[needs confirmation of exact citation]* For the norm-Euclidean property of $\mathbb{Q}(\sqrt[3]{3})$ we currently rely on the general statement in [Lemmermeyer]; a sharper original reference (e.g. the cubic tables of Cioffari or Godwin) may be preferable — see Q5.

### 2.3. State of the art

All seven results are classical and individually well known; none is research-level mathematics. The interesting object is the *formalisation*: to our knowledge mathlib does not yet contain a worked example computing the full invariant package for any single explicit field of degree $\ge 3$, and several of the supporting general theorems (an "explicit unit is fundamental" criterion; a regulator-from-fundamental-unit formula; a norm-Euclidean covering criterion in degree $\ge 3$) are *not present in mathlib* at the level of generality these examples need. The blockers in §8 are therefore as much statements about the current reach of the library as about the individual fields.

---

## 3. Strategy

The development uses a **uniform per-field template**. For each field $K$ the same sequence of self-contained units is built, in a near-linear import order:

> *Basic* (the field model and a number-field instance) $\to$ *Galois* $\to$ *Embeddings* $\to$ *RingOfIntegers* $\to$ *Discriminant* $\to$ *PrimeSplitting* $\to$ *ClassGroup* $\to$ *Units* $\to$ *Euclidean* $\to$ *LocalGlobal*,

with a small number of field-specific special-topic units appended (a *CMField* unit for the totally complex fields; *Subfields* / *QuadraticSubfield* units for $\mathbb{Q}(\zeta_8)$ and $\mathbb{Q}(\zeta_5)$; a *UniqueFactorization* unit for $\mathbb{Q}(\sqrt{-6})$).

Two modelling choices recur:

- **Quadratic fields** are built as an explicit two-dimensional quadratic algebra $\mathbb{Q}[\,\omega\,]$ with $\omega^2 = a\omega + b$, and separately as $\mathbb{Q}[X]/(\text{min.\ poly})$, with a proved $\mathbb{Q}$-algebra isomorphism between the two models. For $\mathbb{Q}(\sqrt 5)$ a *third* "radical" model generating $\sqrt 5$ directly is also given and identified with the golden-ratio model.
- **Cyclotomic fields** are built both as mathlib's cyclotomic field and as $\mathbb{Q}[X]/(\Phi_m)$, again with a proved equivalence; $\mathbb{Q}(\zeta_3)$ is in addition identified with the radical model $\mathbb{Q}(\sqrt{-3})$.
- **The pure cubic field** $\mathbb{Q}(\sqrt[3]{3})$ is built as $\mathbb{Q}[X]/(X^3-3)$ with power basis $\{1,\theta,\theta^2\}$.

A small shared file of algebraic helpers (see §10) is factored out: lemmas on divisors of $p^2$, on equality of ideals with equal norm under containment, on forcing a ramification index $\ge 2$ from a square containment of a mapped prime, and two homomorphism builders used to pin down unit-group structure. **This shared file is the only piece of genuine cross-field abstraction; everything else is currently re-proved per field** — which is precisely the redundancy question (Q3).

The class-number computations all follow the same recipe: bound ideal norms by the Minkowski constant, enumerate the finitely many prime ideals below the bound, and decide their principality by exhibiting (or ruling out) an element of the right norm.

---

## 4. Definitions

All definitions are standard; we restate the few that fix conventions or models.

**Definition 4.1 (field models).** For each $K$ we fix a concrete carrier. Quadratic fields: a two-dimensional $\mathbb{Q}$-algebra with a distinguished generator $\omega$ satisfying its minimal relation; e.g. for $\mathbb{Q}(\sqrt5)$ the golden ratio $\varphi$ with $\varphi^2=\varphi+1$, for $\mathbb{Q}(\sqrt2)$ the element $\sqrt2$ with $(\sqrt2)^2=2$, for $\mathbb{Q}(\sqrt{-6})$ the element $\theta$ with $\theta^2=-6$. Cyclotomic fields: a primitive root of unity $\zeta_m$. Pure cubic: $\theta=\sqrt[3]3$.

**Definition 4.2 (integral norm form).** For an element written in the integral basis we record the field norm as an explicit form with integer coefficients: $N(x+y\varphi)=x^2+xy-y^2$ for $\mathbb{Q}(\sqrt5)$ (discriminant $5$); $N(x+y\sqrt2)=x^2-2y^2$ for $\mathbb{Q}(\sqrt2)$; $N(x+y\theta)=x^2+6y^2$ for $\mathbb{Q}(\sqrt{-6})$; $N(x+y\zeta_3)=x^2-xy+y^2$ for $\mathbb{Q}(\zeta_3)$; and the ternary cubic form $N(x,y,z)=x^3+3y^3+9z^3-9xyz$ for $\mathbb{Q}(\sqrt[3]3)$.

**Definition 4.3 (norm-Euclidean).** $\mathcal{O}_K$ is *norm-Euclidean* if for all $a,b\in\mathcal{O}_K$ with $b\ne0$ there exist $q,r\in\mathcal{O}_K$ with $a=bq+r$ and $|N(r)|<|N(b)|$, where $N$ is the absolute value of the field norm.

**Definition 4.4 (fundamental-unit system / "isFundamental").** For a field of unit rank $1$ we fix a candidate unit $\eta$ and form the assertion that the subgroup generated by $\eta$ together with the torsion subgroup is the *whole* unit group. We call this candidate-system assertion `isFundamental`; it is the precise statement that $\eta$ is a fundamental unit. (This assertion is one of the two recurring blockers — §8.)

**Definition 4.5 (CM field).** For the totally complex fields, the *CMField* unit records that $K$ is totally imaginary, that complex conjugation is the unique nontrivial automorphism fixing the maximal totally real subfield $K^+$, and that $K/K^+$ is quadratic; for $\mathbb{Q}(\zeta_3)$ and $\mathbb{Q}(\sqrt{-6})$ one has $K^+=\mathbb{Q}$, for $\mathbb{Q}(\zeta_5)$ one has $K^+=\mathbb{Q}(\sqrt5)$, and for $\mathbb{Q}(\zeta_8)$ one has $K^+=\mathbb{Q}(\sqrt2)$.

---

## 5. Established results

We summarise per field. Everything in this section has a complete proof unless a status note says otherwise; the open items are gathered in §8.

### 5.0. Summary table

| Field | $\deg$ | sig. $(r_1,r_2)$ | $d_K$ | $h_K$, class gp. | $\mathcal{O}_K^\times$ | Galois gp. (closure) | norm-Eucl. |
|---|---|---|---|---|---|---|---|
| $\mathbb{Q}(\sqrt2)$ | $2$ | $(2,0)$ | $8$ | $1$, trivial | $\{\pm1\}\times\langle1+\sqrt2\rangle$ | $\mathbb{Z}/2$ | yes (proved) |
| $\mathbb{Q}(\sqrt5)$ | $2$ | $(2,0)$ | $5$ | $1$, trivial | $\{\pm1\}\times\langle\varphi\rangle$ | $\mathbb{Z}/2$ | yes (proved) |
| $\mathbb{Q}(\sqrt{-6})$ | $2$ | $(0,1)$ | $-24$ | $2$, $\mathbb{Z}/2$ | $\{\pm1\}$ | $\mathbb{Z}/2$ | **no** (proved not) |
| $\mathbb{Q}(\zeta_3)$ | $2$ | $(0,1)$ | $-3$ | $1$, trivial | $\mu_6$ | $\mathbb{Z}/2$ | yes (proved) |
| $\mathbb{Q}(\sqrt[3]3)$ | $3$ | $(1,1)$ | $-243$ | $1$, trivial | $\{\pm1\}\times\langle\theta^2-2\rangle$ | trivial ($S_3$) | yes — **open** |
| $\mathbb{Q}(\zeta_5)$ | $4$ | $(0,2)$ | $125$ | $1$, trivial | $\mu_{10}\times\langle1+\zeta_5\rangle$ | $\mathbb{Z}/4$ | yes — **open** |
| $\mathbb{Q}(\zeta_8)$ | $4$ | $(0,2)$ | $256$ | $1$, trivial | $\mu_8\times\langle1+\sqrt2\rangle$ | $\mathbb{Z}/2\times\mathbb{Z}/2$ | yes — **open** |

"open" in the last column means the property is true and believed, but the supporting lemma is currently a `sorry`. The unit-group entries marked with a free factor $\langle\eta\rangle$ are subject to the `isFundamental`/regulator caveat of §8 for the degree-$\ge3$ fields and for $\mathbb{Q}(\sqrt5)$.

### 5.1. The quadratic fields

**Theorem 5.1 (rings of integers).** $\mathcal{O}_{\mathbb{Q}(\sqrt2)}=\mathbb{Z}[\sqrt2]$ with basis $\{1,\sqrt2\}$; $\mathcal{O}_{\mathbb{Q}(\sqrt5)}=\mathbb{Z}[\varphi]$ with basis $\{1,\varphi\}$, $\varphi=\tfrac{1+\sqrt5}2$ (and the proof explicitly shows the naive order $\mathbb{Z}[\sqrt5]$ is a *proper* suborder); $\mathcal{O}_{\mathbb{Q}(\sqrt{-6})}=\mathbb{Z}[\sqrt{-6}]$ with basis $\{1,\sqrt{-6}\}$.

*Sketch.* In each case one verifies the candidate basis is integral, then shows maximality by the standard discriminant argument: an integer combination divisible by the relevant prime is forced back into the order. For $\sqrt5$ the residue $5\equiv1\pmod4$ is exactly what makes $\varphi$ (not $\sqrt5$) integral; the proof isolates a suborder with even "imaginary part" containing $\mathbb{Z}[\sqrt5]$ to exclude it. ∎

**Theorem 5.2 (discriminants).** $d_{\mathbb{Q}(\sqrt2)}=8$, $d_{\mathbb{Q}(\sqrt5)}=5$, $d_{\mathbb{Q}(\sqrt{-6})}=-24$, computed from the trace/Gram matrix of the chosen basis.

**Theorem 5.3 (splitting laws).** For $\mathbb{Q}(\sqrt5)$: $5$ ramifies, $(5)=(\sqrt5)^2$; an odd $p\ne5$ splits iff $p\equiv\pm1\pmod5$ and is inert iff $p\equiv\pm2\pmod5$. For $\mathbb{Q}(\sqrt2)$: $2$ ramifies, $(2)=(\sqrt2)^2$; $p$ splits iff $p\equiv\pm1\pmod8$, inert iff $p\equiv\pm3\pmod8$. For $\mathbb{Q}(\sqrt{-6})$: $2$ and $3$ both ramify, $(2)=\mathfrak p_2^2$, $(3)=\mathfrak p_3^2$; the split/inert dichotomy for $p\nmid 6$ is governed by the quadratic character of $-6$ (a residue-class criterion modulo $24$). Representative splittings ($11=(3+\varphi)(4-\varphi)$ in $\mathbb{Q}(\sqrt5)$; $7=(3+\sqrt2)(3-\sqrt2)$ in $\mathbb{Q}(\sqrt2)$; $7=(1+\sqrt{-6})(1-\sqrt{-6})$ in $\mathbb{Q}(\sqrt{-6})$) are verified explicitly.

*Sketch.* Kummer–Dedekind: the splitting of $p$ mirrors the factorisation of the minimal polynomial mod $p$, and the residue-class form of the criterion is read off via quadratic reciprocity (resp. its supplements for $p=2,5$). ∎

**Theorem 5.4 (class numbers and units, quadratic).** $h=1$ for $\mathbb{Q}(\sqrt2)$ and $\mathbb{Q}(\sqrt5)$ (Minkowski bound $<2$); $h=2$ with class group $\mathbb{Z}/2$ for $\mathbb{Q}(\sqrt{-6})$. Unit groups: $\{\pm1\}\times\langle1+\sqrt2\rangle$ and $\{\pm1\}\times\langle\varphi\rangle$ for the real fields (rank $1$, torsion $\{\pm1\}$, fundamental units $1+\sqrt2$ and $\varphi$); $\{\pm1\}$ for $\mathbb{Q}(\sqrt{-6})$ (rank $0$).

*Sketch for $\mathbb{Q}(\sqrt{-6})$, $h=2$.* The Minkowski bound is $\approx3.1$; the only prime ideals below it are $\mathfrak p_2=(2,\sqrt{-6})$ and $\mathfrak p_3=(3,\sqrt{-6})$, both non-principal because the form $x^2+6y^2$ represents neither $2$ nor $3$. The relation $(\sqrt{-6})=\mathfrak p_2\mathfrak p_3$ shows $[\mathfrak p_3]=[\mathfrak p_2]^{-1}=[\mathfrak p_2]$, and $\mathfrak p_2^2=(2)$ is principal, so the class group is exactly $\mathbb{Z}/2$. ∎

**Theorem 5.5 (Euclidean status, quadratic).** $\mathbb{Q}(\sqrt2)$ and $\mathbb{Q}(\sqrt5)$ are norm-Euclidean (rounding argument with remainder-norm bound $\le\tfrac12$, resp. $\le\tfrac34$). $\mathbb{Q}(\sqrt{-6})$ is **provably not** norm-Euclidean — indeed not a PID — exhibited concretely: dividing $\sqrt{-6}$ by $2$ leaves no remainder of norm $<4$, and $6=2\cdot3=-(\sqrt{-6})^2$ gives two genuinely distinct factorisations into irreducibles, with $2$ irreducible but not prime.

### 5.2. The Eisenstein field $\mathbb{Q}(\zeta_3)=\mathbb{Q}(\sqrt{-3})$

**Theorem 5.6.** $\mathcal{O}_K=\mathbb{Z}[\zeta_3]$ (the Eisenstein integers), basis $\{1,\zeta_3\}$; $d_K=-3$; $3$ ramifies as $(\zeta_3-1)^2$, $2$ is inert, and $p\ne3$ splits iff $p\equiv1\pmod3$; $h_K=1$; $\mathcal{O}_K^\times=\mu_6=\{\pm1,\pm\zeta_3,\pm\zeta_3^2\}$ (rank $0$); Galois group $\mathbb{Z}/2$; norm-Euclidean (proved). As a CM field its maximal real subfield is $\mathbb{Q}$. This field is **fully proved — no open lemmas.**

### 5.3. The pure cubic field $\mathbb{Q}(\sqrt[3]3)$

**Theorem 5.7.** $\mathcal{O}_K=\mathbb{Z}[\theta]$, $\theta=\sqrt[3]3$, basis $\{1,\theta,\theta^2\}$ (monogenic; the key arithmetic fact is $3\not\equiv\pm1\pmod9$); $d_K=-243=-3^5$; signature $(1,1)$.

**Theorem 5.8 (splitting).** $3$ is totally ramified, $(3)=(\theta)^3$. The prime $2$ is unramified with $(2)=(\theta-1)\cdot(\theta^2+\theta+1)$, of residue degrees $1$ and $2$. The prime $7$ is inert (residue degree $3$); $61$ splits completely into three degree-one primes. In general a prime $p\ne3$ has a degree-one factor iff $3$ is a cube modulo $p$, with full splitting type read from the factorisation of $X^3-3$ in $\mathbb{F}_p[X]$.

**Theorem 5.9 (class number, Galois).** $h_K=1$ (Minkowski bound $\approx4.4$; the primes $2,3$ below it are principal). $K/\mathbb{Q}$ is **not normal**: $\operatorname{Aut}(K/\mathbb{Q})$ is trivial, while the Galois closure $\mathbb{Q}(\theta,\zeta_3)$ has degree $6$ and Galois group $S_3$.

**Theorem 5.10 (units).** $\mathcal{O}_K^\times\cong\{\pm1\}\times\mathbb{Z}$, rank $1$, torsion $\{\pm1\}$, with candidate fundamental unit $\eta=\theta^2-2$ (inverse $2\theta^2+3\theta+4$). *Status:* the assertion that $\eta$ together with $\{\pm1\}$ generates $\mathcal{O}_K^\times$ (`isFundamental`) is **open** — §8.A.

**Status (Euclidean).** $\mathbb{Q}(\sqrt[3]3)$ is norm-Euclidean — this is the unique pure cubic field of smallest discriminant and the property is classical — but the proof is **open** (§8.B). Note $h_K=1$ is proved independently, so the PID/UFD conclusions do not depend on the Euclidean lemma.

### 5.4. The quartic cyclotomic fields $\mathbb{Q}(\zeta_5)$ and $\mathbb{Q}(\zeta_8)$

**Theorem 5.11 ($\mathbb{Q}(\zeta_5)$).** $\mathcal{O}_K=\mathbb{Z}[\zeta_5]$, basis $\{1,\zeta_5,\zeta_5^2,\zeta_5^3\}$; $d_K=125=5^3$; $5$ totally ramified $(1-\zeta_5)^4$, $2$ inert (order of $2$ mod $5$ is $4$); $h_K=1$; Galois group cyclic $\mathbb{Z}/4$. CM field with maximal real subfield $\mathbb{Q}(\sqrt5)$, where $\sqrt5=1+2\zeta_5+2\zeta_5^4$ (a Gauss sum). Unit group $\mu_{10}\times\langle1+\zeta_5\rangle$: rank $1$, torsion $\mu_{10}=\langle-\zeta_5\rangle$ (order $10$), candidate fundamental unit the cyclotomic unit $1+\zeta_5$ (inverse $-(\zeta_5+\zeta_5^3)$), conjectured regulator $2\log\varphi$. *Status:* `isFundamental` and the regulator value are **open** (§8.A); everything else proved.

**Theorem 5.12 ($\mathbb{Q}(\zeta_8)$).** $\mathcal{O}_K=\mathbb{Z}[\zeta_8]$, basis $\{1,\zeta_8,\zeta_8^2,\zeta_8^3\}$; $d_K=256=2^8$; $2$ totally ramified $(1-\zeta_8)^4$; sample splittings $(3)$ into two degree-$2$ primes and $(17)$ into four degree-$1$ primes are explicit; $h_K=1$; Galois group the Klein four-group $\mathbb{Z}/2\times\mathbb{Z}/2$, with the three quadratic subfields $\mathbb{Q}(i)$, $\mathbb{Q}(\sqrt2)$, $\mathbb{Q}(\sqrt{-2})$ matched to the three index-two subgroups. CM field with maximal real subfield $\mathbb{Q}(\sqrt2)$. Unit group $\mu_8\times\langle1+\sqrt2\rangle$: rank $1$, torsion $\mu_8=\langle\zeta_8\rangle$, candidate fundamental unit $1+\sqrt2=1+\zeta_8+\zeta_8^7$, conjectured regulator $2\log(1+\sqrt2)$. *Status:* `isFundamental` and the regulator value are **open** (§8.A); norm-Euclideanity is **open** (§8.B); everything else proved.

### 5.5. Local–global data (all fields)

Each *LocalGlobal* unit assembles, for its field: the relevant finite places (as height-one primes of $\mathcal{O}_K$, with their $e,f$ data), the corresponding completions, the infinite places (real/complex), the **product formula** verified on distinguished elements (the generator and the fundamental unit), the **canonical and mixed embeddings** with the image of $\mathcal{O}_K$ as a lattice, the **fundamental cone** with the statement that a unit fixes it iff it is $\pm1$, the **house** of distinguished elements, the **adele ring** with principal adeles, and the **Dedekind zeta function** together with its residue expression from the analytic class number formula.

*Status note.* The zeta function and its residue are set up at the level of *definitions and the class-number-formula expression*, used to display the analytic invariants in one place; they are not a re-derivation of the analytic class number formula itself. This is exactly the kind of place where we would like the reviewer's read on whether the statements are meaningful as written or merely decorative (Q2).

---

## 6. In progress

The seven fields are at three levels of completeness.

**Complete (no open lemmas):** $\mathbb{Q}(\sqrt{-6})$ and $\mathbb{Q}(\zeta_3)$. The first because its unit group has rank $0$ (no fundamental unit to certify) and it is treated as the non-Euclidean / non-UFD example, so its "Euclidean" content is a *negative* result that is fully proved; the second similarly has rank $0$.

**Complete except the rank-$1$ unit certification:** $\mathbb{Q}(\sqrt2)$ and $\mathbb{Q}(\sqrt5)$. Here `isFundamental` is settled for $\mathbb{Q}(\sqrt2)$ but the *regulator value* $\log(1+\sqrt2)$ remains open; for $\mathbb{Q}(\sqrt5)$ both the generation statement and the regulator $\log\varphi$ remain open.

**Complete except units and (for two of them) the Euclidean covering:** $\mathbb{Q}(\sqrt[3]3)$, $\mathbb{Q}(\zeta_5)$, $\mathbb{Q}(\zeta_8)$ — each missing `isFundamental` (and, for the cyclotomic pair, the regulator value), and each missing norm-Euclideanity.

There are no other in-progress targets; the per-field templates are otherwise filled.

---

## 7. Targets (not yet attempted)

These are not yet in the library and we mention them so the reviewer can judge whether they are the natural next steps (Q4):

- A **general "worked field" abstraction** that would let the per-field invariant package be stated once and instantiated, rather than re-proved seven times (this is the structural counterpart of the redundancy question, Q3).
- Two **general supporting theorems** that, if added to mathlib, would discharge the recurring blockers in §8 uniformly: (i) an explicit criterion certifying that a given unit of a rank-one field is fundamental, with the regulator equal to the appropriate $\log$ of its embedding; (ii) a norm-Euclidean covering criterion usable in degree $\ge3$.
- Further fields to round out the phenomenology (e.g. a field with non-cyclic class group, or a non-monogenic ring of integers such as $\mathbb{Q}(\sqrt[3]{m})$ with $m\equiv\pm1\pmod9$).

---

## 8. Where we're stuck

Two obstructions recur across the fields, and both are really **mathlib-API gaps** rather than difficulties peculiar to any one field.

**Stuck point 8.A — certifying a fundamental unit and computing the regulator (rank-$1$ fields).**
For $\mathbb{Q}(\sqrt[3]3)$, $\mathbb{Q}(\zeta_5)$, $\mathbb{Q}(\zeta_8)$ and $\mathbb{Q}(\sqrt5)$ we have an explicit candidate fundamental unit and the abstract structure theorem $\mathcal{O}_K^\times\cong(\text{torsion})\times\mathbb{Z}$, but we cannot yet prove that *our specific element* generates the free part (`isFundamental`), nor pin the regulator to its closed form ($\log\varphi$, $2\log\varphi$, $\log(1+\sqrt2)$, $2\log(1+\sqrt2)$). Dirichlet's unit theorem (available in mathlib) gives existence of a rank-one generator but not the identification of a named element as that generator. What is missing is a usable *quantitative* criterion — an Artin/Minkowski-type lower bound on the regulator, or an upper bound on the smallest non-torsion unit — that would let us exclude the existence of a smaller unit and conclude our candidate is fundamental. We have reduced each case to exactly this point. *We would like to know the cleanest route an expert would take here, and whether it can be made uniform across the four fields.* (See Q1.)

**Stuck point 8.B — norm-Euclidean covering in degree $\ge3$.**
For the quadratic fields the norm-Euclidean property falls to a one-line rounding bound. For $\mathbb{Q}(\sqrt[3]3)$ (a ternary cubic form) and the quartic cyclotomic fields ($\mathbb{Q}(\zeta_5)$, $\mathbb{Q}(\zeta_8)$) the same property is classical but requires a genuine **covering argument**: that every point of the relevant real vector space is within norm-distance $<1$ of a lattice point of $\mathcal{O}_K$. We do not have a formalised covering lemma at this level of generality, and the explicit form-by-form arguments in the literature are awkward to reproduce in the proof assistant. These three `sorry`s are independent of the class-number results (which are proved by Minkowski, not via Euclideanity), so nothing downstream breaks — but the Euclidean claims themselves stand on them. (See Q5.)

For completeness, the full list of open lemmas (`sorry`s) is: `isFundamental` for $\mathbb{Q}(\sqrt[3]3)$, $\mathbb{Q}(\zeta_5)$, $\mathbb{Q}(\zeta_8)$, $\mathbb{Q}(\sqrt5)$; the regulator value for $\mathbb{Q}(\zeta_5)$, $\mathbb{Q}(\zeta_8)$, $\mathbb{Q}(\sqrt5)$, $\mathbb{Q}(\sqrt2)$; and norm-Euclideanity for $\mathbb{Q}(\sqrt[3]3)$, $\mathbb{Q}(\zeta_5)$, $\mathbb{Q}(\zeta_8)$ — eleven lemmas in eight files, all within the two clusters above.

---

## 9. Open mathematical questions for the reviewer

**Q1 (the showcase question, and the heart of §8.A).** Treating these fields as a showcase of mathlib's `NumberField` API: what is the cleanest, ideally *uniform*, route to certifying a named element as the fundamental unit of a rank-one field and to computing its regulator — given that the library currently offers Dirichlet existence but no quantitative regulator bound? Is the right move to formalise a general Artin/Minkowski-type lower bound on the regulator, or is there a slicker per-field argument (e.g. via the continued-fraction/Pell structure for the real quadratic and cubic cases, or via cyclotomic units for $\mathbb{Q}(\zeta_5),\mathbb{Q}(\zeta_8)$) that an expert would prefer?

**Q2 (soundness / meaningfulness).** Are all the invariant statements *mathematically meaningful as stated*? In particular: (a) is our `isFundamental` formulation (Definition 4.4 — the candidate together with torsion generates the unit group) the right and full statement that "$\eta$ is a fundamental unit", or is there a sharper standard formulation? (b) In the *LocalGlobal* units, the Dedekind zeta function and its residue are introduced at the level of definitions plus the class-number-formula expression rather than re-proving the analytic class number formula — is this a meaningful and honest thing to record, or is it better dropped to avoid the appearance of a theorem we have not proved?

**Q3 (redundancy / abstraction).** The seven fields share an essentially identical invariant package but are currently proved one field at a time, with only a small shared helper file. Is this duplication acceptable (and even desirable, as a transparent catalogue), or should the common structure be lifted into a single reusable abstraction — and if so, at what altitude (a typeclass recording "this field has been fully worked out"? a tactic that discharges the standard package from minimal data)? Where is the line between a useful *example library* and code that ought to be generic theorems?

**Q4 (coverage).** As a demonstration of the API, is the chosen set of seven fields well chosen — do they exhibit the phenomena a reader should see (trivial vs. $\mathbb{Z}/2$ class group; PID vs. not; the three signature types; cyclic / Klein-four / trivial Galois; norm-Euclidean vs. not)? Is there an obviously missing example whose absence weakens the showcase (e.g. a non-cyclic class group, or a non-monogenic ring of integers)?

**Q5 (norm-Euclidean in degree $\ge3$, §8.B).** What is the most formalisation-friendly form of the covering argument proving $\mathbb{Q}(\sqrt[3]3)$, $\mathbb{Q}(\zeta_5)$ and $\mathbb{Q}(\zeta_8)$ norm-Euclidean? Is there a clean reduction (e.g. to a finite check over a fundamental domain) that avoids the case-heavy classical arguments, and what is the canonical reference we should cite (is [Lemmermeyer] sufficient, or is there a sharper primary source for the cubic case)?

**Q6 (anything obviously wrong).** Are any of the *computed* values suspect on inspection — discriminants ($8,5,-24,-3,-243,125,256$), the explicit prime factorisations, the unit/torsion orders, the class group of $\mathbb{Q}(\sqrt{-6})$? These were derived inside the proof assistant and are machine-checked relative to the definitions, but a sanity read by an expert is exactly what we want before treating the library as a reference.

---

## 10. Auxiliary technical results (appendix)

The shared helper file proves, generically: that a divisor of $p^2$ other than $1$ and $p^2$ equals $p$; that two ideals of equal absolute norm, one containing the other, are equal; that a nonzero residue mod a prime has an integer inverse representative; that a square containment $\mathfrak p\mathcal{O}_S\subseteq\mathfrak P^2$ (with non-containment in the next power) forces $e\ge2$, hence ramification, and the specialisation of this to $(p)$ over $\mathbb{Z}$ via the absolute norm; and two group-homomorphism builders (from a finite cyclic index to powers of a torsion element, and from $\mathbb{Z}$ to powers of a chosen unit) used to nail down unit-group structure. These are the only results currently shared across fields.

---

## 11. Document metadata

- Project name: `FieldExamples` (within the `XYin` Lean project).
- Brief generated: 2026-06-15.
- Length: ~6 pages.
- Build status at time of writing: compiles; **11 `sorry`s remaining**, in 8 files, all within the two blocker clusters of §8 (fundamental-unit/regulator certification, and norm-Euclidean covering in degree $\ge3$).
- Fields covered: seven — $\mathbb{Q}(\sqrt2)$, $\mathbb{Q}(\sqrt5)$, $\mathbb{Q}(\sqrt{-6})$, $\mathbb{Q}(\zeta_3)$, $\mathbb{Q}(\sqrt[3]3)$, $\mathbb{Q}(\zeta_5)$, $\mathbb{Q}(\zeta_8)$.
- Recent activity: file reorganisation into the near-linear per-field import order; incremental filling of the per-field templates (the bulk of each field's invariant package is complete).
