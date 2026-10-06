# Actual glued quotient rank verification

The retained module `AINTLIBDrafts.YZeroCoarseGluedQuotientRank` proves
`FiniteLocallyFreeSubgroup.gluedQuotientπ_finrank G N hkill r hG y`. The base
scheme is arbitrary; the actual nonzero killing integer and its genuine subgroup
killing equation are explicit. The supplied subgroup predicate is `G.HasRank r`.
No global Free, Noetherian, étale, domain, or model premise is added.

The actual glue data's target chart cover is jointly surjective, so each quotient
point has a chart lift. `free_gluePatch` genuinely comes from the construction's
chosen stable free affine patches, and is installed only for the selected patch.
The proved actual target-chart pullback square, in its flipped orientation, and
the retained global finite/flat projection theorems identify global fibre rank
at the covered point with the raw local projection rank. That rank is supplied
by the retained actual local theorem, not by an assumption about the quotient.

Two actual API examples check all target points and points obtained from a literal
quotient chart. No public chosen-kill or marked-axis wrapper, native function-field
degree or quotient elliptic-curve upgrade is asserted in this bounded leaf.
The actual pinned source uses explicit `N`/`NeZero N`/`hkill` arguments, rather
than a separate type named `KillingIntDatum`.

## Exact verification

- Approved temporary source: 55 lines, SHA `b351a781a05e920618fde4434dd664a85eb5f199623fe2764188096f5ff5372e`. Its first strict Lean run
  was session 65870 CLOSED exit 0, with no failed Lean staging source or diagnostic.
- Retained source: 76 lines, width 97, SHA `0782f711c8611c50cd94dc52bdca8baf0f97842a594b3f397c4aa885c010b529`.
  Retained/isolated copies agree byte-for-byte; the full approved suffix starting
  `@[expose] public section` is byte-preserved.
- Correct-name strict emission: session 70148 CLOSED exit 0 on pinned Lean
  4.35.0-rc3. Setup name `AINTLIBDrafts.YZeroCoarseGluedQuotientRank`, both implicit-variable
  options false, 9459 normalized imports available.
- All ten exact printed declarations use only the standard three axioms
  `propext`, `Classical.choice`, `Quot.sound`; both actual API examples passed;
  own errors/warnings: zero.
- Actual named log `/private/tmp/xyin-y0-glued-quotient-rank-check.log`, SHA `ca45e3ecd6625f9d6dab6c5b9e3817b85d52a5f7dc3072986402c0f8027e1155`.
- Setup SHA `5f5b679edc9ace580695672f0bf71c69809266d68aa8dd172814d12176a009aa`.
- All six Lean artifacts are inspected nonempty, sizes
  12472, 32376, 2136, 11955, 176, 1584; explicit C output 3602 bytes.
- Full command, names, source/setup/log/artifact hashes:
  `/private/tmp/xyin-y0-glued-quotient-rank-receipt.json`.

The source and artifacts are frozen at this receipt. No cumulative build or
user environment/model/settings change was performed for this bounded check.
