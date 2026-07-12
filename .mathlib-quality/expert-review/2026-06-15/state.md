# Expert-review session state

- Generated: 2026-06-15
- Audience: algebraic number theorist
- Goal of brief: soundness — is every statement mathematically meaningful, and is there redundancy? Plus: is this a good case-study/showcase of mathlib's current `NumberField` API?
- Scope: the whole `FieldExamples` folder (seven fields)
- Reply received: false
- Reply integrated: false

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | The showcase + §8.A question: cleanest, ideally uniform route to certifying a named element as the fundamental unit of a rank-one field and computing its regulator, given mathlib offers Dirichlet existence but no quantitative regulator bound. Artin/Minkowski regulator lower bound vs. per-field (Pell/continued-fraction, cyclotomic units) argument? |
| Q2 | Soundness/meaningfulness: (a) is the `isFundamental` formulation (candidate + torsion generates units) the right/full statement that η is a fundamental unit? (b) Is recording the Dedekind zeta function + residue at definition-level (not re-proving the analytic class number formula) meaningful and honest, or better dropped? |
| Q3 | Redundancy/abstraction: seven fields share an identical invariant package, proved per field with only a small shared helper file. Acceptable duplication, or lift into a reusable abstraction — and at what altitude (typeclass? tactic)? Where is the line between an example library and generic theorems? |
| Q4 | Coverage: is the chosen set of seven fields well chosen to exhibit the phenomena (trivial vs Z/2 class group, PID vs not, three signature types, cyclic/Klein-four/trivial Galois, norm-Euclidean vs not)? Any obviously missing example (non-cyclic class group, non-monogenic ring of integers)? |
| Q5 | Norm-Euclidean in degree ≥3 (§8.B): most formalisation-friendly form of the covering argument for Q(∛3), Q(ζ5), Q(ζ8)? Clean reduction to a finite check over a fundamental domain? Canonical reference (is Lemmermeyer enough, or a sharper primary source for the cubic case)? |
| Q6 | Anything obviously wrong: are the computed values suspect — discriminants (8,5,−24,−3,−243,125,256), explicit prime factorisations, unit/torsion orders, class group of Q(√−6)? |

## Ticket-board snapshot at brief time

No ticket board for `FieldExamples`. The project's `.mathlib-quality/tickets.md` and `plan.md` concern a separate modular-forms / Laurent q-expansion component, not these number-field examples. `FieldExamples` is developed directly in the Lean files with no `/develop` tickets.

Open mathematical sub-goals as understood at brief time (the 11 remaining `sorry`s, in two clusters):
- Cluster A — fundamental-unit certification (`isFundamental`) and regulator value, rank-1 fields:
  - `isFundamental`: Q(∛3), Q(ζ5), Q(ζ8), Q(√5)
  - regulator value: Q(ζ5)=2log φ, Q(ζ8)=2log(1+√2), Q(√5)=log φ, Q(√2)=log(1+√2)
- Cluster B — norm-Euclidean covering in degree ≥3:
  - Q(∛3), Q(ζ5), Q(ζ8)
- Fully proved (no open lemmas): Q(√−6) [non-PID/non-UFD example, h=2], Q(ζ3) [Eisenstein].
- Q(√2), Q(√5): `isFundamental` settled for √2; regulator open for both; generation open for √5.

## Stuck points (from §8 of brief)

1. 8.A — Certifying a named element as fundamental unit + regulator value for rank-1 fields. mathlib gives Dirichlet existence but no quantitative regulator/Artin bound. Reduced each case to exactly this point.
2. 8.B — Norm-Euclidean covering argument in degree ≥3 (Q(∛3), Q(ζ5), Q(ζ8)); quadratic cases trivial by rounding. Independent of class-number results (those use Minkowski).

## Reference list (from §2.2 of brief)

- [Marcus] Marcus, *Number Fields*, 2nd ed., Springer 2018.
- [Neukirch] Neukirch, *Algebraic Number Theory*, Springer 1999.
- [Washington] Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Springer 1997.
- [Cohen] Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, Springer 1993.
- [Lemmermeyer] Lemmermeyer, "The Euclidean algorithm in algebraic number fields," Expo. Math. 13 (1995), 385–416. [norm-Euclidean reference; possibly want sharper cubic source — Q5]
- [mathlib] mathlib4: NumberField, RamificationInertia, Ideal.absNorm, NumberField.Units, IsCyclotomicExtension, FinitePlace/InfinitePlace, mixedEmbedding.
