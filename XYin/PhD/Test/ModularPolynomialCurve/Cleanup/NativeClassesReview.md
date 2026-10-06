# Native marking classes review

Read-only scope: the retained marking-classifier naturality/action module, the retained
HomOver adapter, native roundtrip, native `GammaHClasses` descent, the subsequent
equal-fine-point marked-isomorphism module and reverse EllIso-to-HomOver adapter.
No Lean source edit, compiler invocation,
setup change or new axiom was made by
this reviewer. Only this report is written.

The source environment is AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `4.35.0-rc3`.
The local XYin toolchain is untouched.

| Reviewed retained module | Lines | SHA-256 | Receipt |
| --- | ---: | --- | --- |
| YZeroCoarseMarkingClassifiers.lean | 108 | `a5f2207e5493c363e7a6524c9ada1f3caa04c9452ed389f8d3be5d77c9b318d1` | Strict direct exit 0 reported; actual two standard-three checks read |
| YZeroCoarseHomOverClassifiers.lean | 97 | `cbd657598d8d85a28a8ed30928888fd5e0c716d4314f35fb39294ee308581f65` | Retained strict emit exit 0; all seven checks standard-three |
| YZeroCoarseNativeClasses.lean | 247 | `90353b439ca8098e902eaed1cc32dce37ab59166727ce4f6ad40fcb415b0339b` | Final equivalence artifact exit 0; all thirteen checks standard-three |
| YZeroCoarseNativeRoundtrip.lean | 103 | `38b4f33a1c91525ab22cbb816c65c4389a87ca6a9fb5d55b65b0507db4807f9a` | Strict artifact exit 0; all four checks standard-three |
| YZeroCoarseClassifierPointIso.lean | 102 | `3ea4c8b5b922cb56253c24be6668a5763b52d1f53f63cdeb536238af7de8522e` | Strict artifact exit 0; five checks use only standard axioms |
| YZeroCoarseEllIsoHomOver.lean | 110 | `17023dc57e5fd6b912e0e2516b24483a2fa06b9675747d0ccb92d62290369220` | Strict artifact exit 0; eight standard-three and three axiom-free checks |

## Actual classifier naturality

`fullComplexSchemePointOfMarking_map` uses mathlib's actual
`RepresentableBy.comp_homEquiv_symm` (`Yoneda.lean:290`). Its equality of classifying
elliptic-object maps is projected through `EllHom.baseHom`. The source/target objects
are the literal `complexEllObj` with `structMap = id`, so the native `u.base_w` proves
that its base morphism `b` is the identity. Cancelling this identity yields precisely
the claimed equality of classified fine complex points. No unsupported equality of
curve records or unrelated fine-point choice enters.

The cartesian pointed morphism is an actual `EllHom`; naturality does not assume that
a bare arbitrary curve map induces pullback on markings. It preserves exactly the
same full marking under the actual `gammaFullNaiveProblem.map`.

## Actual Borel action and positive glSmul

The exact pinned definitions agree with the proof's direction:

- `SchemeQuotient.lean:66`: `SchemeAction.ofAut ψ` has `hom g = (ψ g).inv`.
- `CoarseSpace.lean:65`: `baseSchemeAction` transports through `autMulHom` then projects
  to the base using `EllObj.autBase`.
- `RepresentableAut.lean:82`: `(autMulHom e).inv = transportHom e.inv`.
- `GammaHRepresentability.lean:3307`: `gammaHAut(g).hom` acts by `glSmul(g⁻¹)`, while
  its inverse component acts by positive `glSmul g`.

The retained proof applies `homEquiv_comp_transportHom` to the inverse natural
transformation, uses the classifier's actual inverse law, and then injectivity of the
same representing equivalence. Projection to the base gives postcomposition by the
literal `borelAction.hom g`. Therefore `fullComplexSchemePointOfMarking_glSmul` correctly
has positive `glSmul g` on its left side; changing it to `g⁻¹` would reverse the intended
convention. The existing composition convention remains a right action on points.

I read the complete strict log `/private/tmp/xyin-y0-marking-classifiers-check.log`:
both printed declarations have exactly `[propext, Classical.choice, Quot.sound]` and
no diagnostic lines. The retained file has two level-three sanity examples. Its owner
reports strict direct exit 0. Mathematical review result: no issue.

## Given HomOver and section transport

The adapter uses the original `f : E.HomOver E'` from the actual native
`Moduli/Groupoid.lean:44`; it requires `[IsIso f.hom]`. `baseHom` is literally the
identity and `top` literally `f.hom`. The curve square is cartesian by
`IsPullback.of_horiz_isIso`, using `f.over_w`; pointedness uses the original `f.zero_w`.
No new or arbitrarily selected curve isomorphism is introduced.

The section equation is the defining first-leg equation of the native
`EllHom.pullSection` (`Representability.lean:155`), specialized to the identity base.
Its iff has the correct direction: `pullSection Q = P` precisely when
`P.val ≫ f.hom = Q.val`. The reverse implication cancels the actual isomorphism
`f.hom`, then applies subtype extensionality. This bridge requires no level hypothesis
and its identity-section sanity example is relevant.

The seven scratch printed checks in `/private/tmp/YZeroHomOverClassifierProbe.log`
are exactly the standard three, including `EllHom.pullSection` and
`IsPullback.of_horiz_isIso`. The retained source has the same proof bodies, with only
header/documentation changes. Its strict retained emit passed with owner-reported exit
0. I independently read all seven checks and zero diagnostic lines in
`/private/tmp/xyin-y0-homover-classifiers.log`; the identity sanity passed in that file.
The retained/build source hashes match. The owner emitted the correct-name
`.olean`, private/server oleans, `.ilean`, and `.ir`, and saved its literal invocation
in `YZeroCoarseHomOverClassifiers.md`. I read
`/private/tmp/YZeroCoarseHomOverClassifiers.setup.json`: the module name is correct,
both automatic-implicit options are false, and there are no dynamic libraries.
Mathematical review: no issue.

## Native class descent

The exact upstream `GammaHClasses` (`Moduli/Coarse.lean:67`) is `Quot` of the relation
on native full-marked elliptic curves. A relation witness consists of the given pointed
`HomOver`, its total-space isomorphism, a matrix in the specified subgroup, and both
forward transported marking equations. It is not a quotient by arbitrary isogenies.
`Quot` generates the equivalence relation, so a `Quot.lift` requires exactly equality
on these generating witnesses.

The descent proof installs only the witness's proved `IsIso f.hom`, builds
the actual HomOver adapter, and applies the section iff to both `mapPoint` equations.
Subtype/product extensionality then gives the actual pulled full-marking equality.
Classifier naturality identifies the target classifier with that transformed marking.
Positive `glSmul` compatibility supplies the literal direct-σ Borel point equation.
The already proved actual coarse-fiber iff then gives equal coarse images, exactly the
well-definedness obligation of `Quot.lift`.

Representative computation is `rfl`, and source-j preservation uses the earlier
genuine given-curve source-j theorem. No source-j, class-map well-definedness, or Φ
equation is assumed as new data. I read the actual first descent log
`/private/tmp/xyin-y0-native-classes-descent-check.log`: both selected upstream
definitions and all three own declarations are standard-three, with no errors.
The lone initial own diagnostic was a Prop-class `letI` style warning. The owner
repaired it to `let`, reports warning-free scratch exit 0, and retained the same
proofs with only header/provenance documentation changes. I read the full retained
103-line snapshot; its maximum width is 95. The unreferenced upstream
`jLine_coarse_points`, `jLine_coarse_points_j`, and `exists_coarse_gammaH` have `sorry`
bodies in `Coarse.lean`, but none of them is used by the reviewed proof; the actual
selected axiom checks confirm this distinction.

The initial 103-line descent-only snapshot had SHA-256
`4b4f68340dfe270d0195829c7e802b1c40f1c71c06488be33d8fcbc63df2a11b`.
Its named retained artifact check passed with owner-reported exit 0 (session
77432). I read the complete preserved `/private/tmp/xyin-y0-native-classes-map-check.log`: all five
prints are exactly the standard three and there are no diagnostic lines. Both
level-three examples passed. Retained/worktree sources matched that snapshot hash;
the 27544-byte `.olean` and its private/server/ilean/ir companions were emitted.
The parent read this same code/log and accepted the frozen 103-line snapshot.

## Native classifier roundtrip

The parent's complete `YZeroNativeRoundtripProbe.lean` snapshot has SHA-256
`54187ae2245b77dab4660d37427d6fc030f0048c8823a21433cfc7405d49e732`.
I read all of it and `/private/tmp/YZeroNativeRoundtripProbe.log`: four printed
declarations are standard-three and there are no diagnostic lines. The parent reports
strict exit 0; the module uses only the marked-complex-curves import.

The normalization goes from `complexEllObj (actualNative.curve)` to the actual pulled
elliptic object. Their literal curve is the same, so its top map and base map are
identities; their structMaps need not be definitionally the same. The `base_w` field
correctly uses the fine point's actual base triangle `p.property`. Typed aliases for
the curve's π and zero expose the identity cartesian square and pointed equation,
without identifying these two elliptic-object records by `rfl`.

The normalization pulls every native section back identically by the actual
pullback-lift first-leg equation. Product/subtype extensionality gives identity on
the full marking. Naturality of the representing equivalence is then applied to this
normalization and the actual universal pullback classifier. Cancelling the genuine
equivalence's inverse law and projecting the resulting map equality to the typed
base gives `fullComplexSchemePointOfMarking_native = p` exactly. Its level-three
sanity checks the original fine point, not an arbitrary chosen image.

No class/Sigma quotient, freeness assertion or quotient-point equivalence is assumed
in this roundtrip proof. I also read the complete 103-line retained
`YZeroCoarseNativeRoundtrip.lean` after the parent's copy: the descriptive normalization
names, main namespace and documentation are the only changes to the reviewed proof.
Its maximum width is 96 and its only public import remains the marked-complex-curves
module. The parent confirms the final named strict artifact run (session 60427) exited
0. I independently read all four standard-three checks and zero diagnostic lines in
`/private/tmp/xyin-y0-native-roundtrip-check.log`; its level-three sanity passed.
The source hash is unchanged, retained/worktree copies match, and the emitted `.olean`
is 23216 bytes. Both the roundtrip and native-class setup JSONs have their correct
module names, `autoImplicit=false`, `relaxedAutoImplicit=false`, and no dynamic libraries.

## Surjectivity append

The subsequently reviewed native-class snapshot adds only the direct roundtrip import,
a short `gammaHClassesComplexPoint_surjective` proof, its sixth axiom print and
a third level-three example. For an actual coarse point `p`, its actual fine lift `q`
provides the native class of the literal pulled curve and marking. The class-map
representative formula reduces its image to that marking's classifier. The exact
roundtrip gives the original fine point `q`, and the already proved actual projection
equation gives `p`. There is no class inverse, independence-of-lift, freeness or desired
moduli-equation assumption.

The initial append failed only at `rw gammaHClassesComplexPoint_mk`: the implicit
transparency checker saw the native curve's opaque object base instead of `Spec ℂ`.
I read that actual failed receipt in
`/private/tmp/xyin-y0-native-classes-surjectivity-first-check.log`, including its
`sorryAx` staging print; it is not accepted as a proof receipt. The repair adds typed
`E : EllipticCurve (Spec ℂ)` and `L : E.FullLevelPt N` aliases for exactly the original
curve and marking. It introduces no replacement object or new assumption. That former
126-line source had SHA-256
`bdffb93e847510ec4440fb8db1e5cfcfcb98c026b68c35b5f05855927a9e6c3b`.
Its final named strict run (session 34114) passed
with owner-confirmed exit 0. I independently parsed the actual final
log, now preserved as `/private/tmp/xyin-y0-native-classes-surjectivity-check.log`:
all six axiom sets are exactly the
standard three, with zero diagnostic lines. The three level-three examples passed.
Retained/worktree hashes match and the actual emitted `.olean` is 28584 bytes;
private/server/ilean/ir companions were also emitted. Mathematical review of the repair:
no issue. This actual final receipt supersedes the failed staging receipt.

## Further marked-isomorphism seam

The additional authorized temporary `YZeroClassifierPointIsoProbe.lean` is 81 lines,
SHA-256 `c4142c89bc548ff55b68de2f8281760c2b9b047c6c53bd13bf9bee5918bf491e`.
Its source and final `/private/tmp/YZeroClassifierPointIsoProbe.log` were read.
The owner reports strict exit 0 with no diagnostics; three own declarations and the
native comparison primitive are standard-three, while `eqToIso` uses only `propext`.
Identity-isomorphism and level-three marked-existence examples pass.

The complete retained 102-line `YZeroCoarseClassifierPointIso.lean` was subsequently
read. Its core from the first `variable (N : ℕ)` through the namespace ending is
byte-identical to the accepted temporary core; only the normal header/provenance
documentation was added. Its sole public import remains MarkedComplexCurves and its
maximum width is 94. The actual named strict log
`/private/tmp/xyin-y0-classifier-point-iso.log` has the same five axiom checks and no
diagnostics. Its owner confirms exit 0 and both sanity examples passed. The
retained/worktree hashes match the table; the emitted `.olean` is 22880 bytes, with
its named companions present. The setup JSON has the correct module name, both
automatic-implicit options false, and no dynamic libraries. The companion
`YZeroCoarseClassifierPointIso.md` preserves the literal invocation.

The pointed isomorphism has the correct direction: given curve → its native pullback
→ the native pullback identified by actual fine-point equality → the target given
curve. Equality induction transports the actual native marking along that middle
`eqToIso`. Contravariant marking transport runs target marking → target native marking
→ source native marking → source marking. The inverse step correctly uses
`j.inv_hom_id` after `op_comp`; the actual theorem names are `CategoryTheory.op_comp`
and `op_id` in `Opposites.lean:87,91`. These namespace spellings were the only repaired
first-compile diagnostics. No full-level automorphism triviality or sorried coarse
classification is used. Mathematical orientation review: no issue.

## Reverse elliptic-object isomorphism converter

The separately authorized temporary `YZeroEllIsoHomOverProbe.lean` is now 77 lines,
SHA-256 `d2966260ae8bb355294640bc4c508cf5d725324671417f7c67b5703c33a4672d`.
I read its complete actual source and the actual native `EllHom`/`HomOver` structures.
It imports only the already checked HomOverClassifiers layer and requires no level or
marking hypothesis.

`complexEllHom_baseHom_eq_id` derives base identity from the original `base_w` field
between literal complex objects. `complexTotalIsoOfEllIso` has hom `e.hom.top` and
inverse `e.inv.top`; both scheme inverse laws are the actual object inverse laws
projected by `congrArg EllHom.top`. No arbitrary inverse or isomorphism-existence
assumption is substituted.

`complexHomOverOfEllIso` retains exactly that top map. Its π equation is the original
cartesian square's commutativity, with the proved identity base substituted. Its zero
equation is the original `zero_w`, with that same substitution. The specifically named
`IsIso` instance directly returns the constructed scheme isomorphism's `isIso_hom`;
it does not recursively ask typeclass search to prove its own result. The roundtrip
`complexEllHomOfHomOver_complexHomOverOfEllIso` uses `EllHom.ext`: the rebuilt identity
base agrees with the original proved identity base, and the rebuilt top map agrees
definitionally. Proof fields do not introduce a second morphism. The identity-HomOver
sanity uses the actual native pointed-curve category's identity.

The initial 73-line snapshot had hash
`0e3e37998765ed405f7c1acd88ec79157737de1eb31510c03fd8bb086c0eebef`.
Its first strict run failed to cancel identity arrows after substituting the base
identity in the π/zero proofs: the native object's curve aliases remained opaque
while the other arrows were canonical `E.π` and `E.zero`. Its complete failure log is
preserved in `/private/tmp/YZeroEllIsoHomOverProbe.first-failure.log`. Dependent kernel
metavariable errors and staging axiom output containing own declaration names are
excluded from the verification receipt.

The repaired snapshot adds explicitly typed canonical scheme arrows `t` and `b`,
and typed `h`/`hb`, in each of those two fields. These aliases denote the same original
top/base arrows; no statement, assumption, inverse law, or mathematical route changes.
I independently read that exact delta and the complete final
`/private/tmp/YZeroEllIsoHomOverProbe.log`. The owner confirms strict run 97062 exited
0 and the identity-HomOver example passed. The log has no diagnostics and ten clean
checks: all five own declarations, `EllHom.zero_w`, and the forward converter use only
`propext`, `Classical.choice`, and `Quot.sound`; the two `Iso` inverse-law projections
and `CommSq.w` are axiom-free. The current source hash agrees with this receipt.

Mathematical review of the converter: no issue. The temporary repaired snapshot is
strictly verified. The retained `YZeroCoarseEllIsoHomOver.lean` was subsequently supplied:
110 lines, maximum width 90, SHA-256
`17023dc57e5fd6b912e0e2516b24483a2fa06b9675747d0ccb92d62290369220`.
I read its complete source. With documentation removed, the five original declarations
and the identity example are unchanged from the checked 77-line temporary core. Its
sole public import remains HomOverClassifiers. The only new declaration is the requested
`@[simp] complexHomOverOfEllIso_hom`, whose actual top-map formula is definitionally
proved by `rfl`. The additional general, possibly nonidentity native-isomorphism example
rewrites the exact reconstruction equality inside the actual `gammaFullNaiveProblem.map`;
it introduces no marking-equality assumption. The extra axiom print corresponds exactly
to that new formula.

The named setup JSON has module name `AINTLIBDrafts.YZeroCoarseEllIsoHomOver`, both
automatic-implicit options false, and empty plugins/dynamic-library lists. The named
strict emission subsequently completed with exit 0. I read the complete actual
`/private/tmp/xyin-y0-ell-iso-homover.log`: all eleven checks are clean (eight standard-three,
three axiom-free) and there are no diagnostics. The owner confirms both identity and
general native-isomorphism level-functor sanity examples passed. The retained and build
sources have the same table hash. The emitted `.olean` is 25888 bytes; `.olean.private`,
`.olean.server`, `.ilean`, `.ir`, and `.ir.sig` exist with the correct module name. The
companion `YZeroCoarseEllIsoHomOver.md` records the exact strict compiler invocation,
pins, accepted proof and explicit exclusion of failed staging output.
This adapter itself asserts no relation between coarse points or injectivity of the
native class map.

## Native-class injectivity and equivalence append

The newly authorized actual NativeClasses append was independently read in full:
247 lines, maximum width 95, SHA-256
`90353b439ca8098e902eaed1cc32dce37ab59166727ce4f6ad40fcb415b0339b`.
Its only new imports are the two checked ClassifierPointIso/EllIsoHomOver leaves.
The former 126-line strict receipt remains preserved at
`/private/tmp/xyin-y0-native-classes-surjectivity-check.log`.
The new named strict run 25997 subsequently completed with exit 0, without repair
or any delta from this reviewed 247-line source. I independently read and parsed the
complete `/private/tmp/xyin-y0-native-classes-check.log`: all thirteen printed axiom
sets are exactly the standard three, and the log has zero diagnostic lines. The owner
confirms all five level-three sanity examples passed. Retained/build source hashes
match the table. Correct-name artifacts are present: `.olean` 43776 bytes,
`.olean.private` 163248, `.olean.server` 6232, `.ilean` 42989, `.ir` 2344, and `.ir.sig` 176.
The table now records this final verified equivalence snapshot.

The injectivity proof uses `Quot.induction_on₂` and the literal coarse-fiber criterion.
Its witness satisfies `classify β = classify α ≫ σ(g)`. The checked positive-glSmul
formula and that equality reversed give exactly
`classify (glSmul g α) = classify β`; no inverse Borel element is substituted. The
already checked equal-fine-point isomorphism has direction `E → E'` and pulls `β`
back to `αg`. The reverse adapter gives a genuine fixed-base `HomOver` `f` whose
top morphism is that same isomorphism hom, together with its actual `IsIso` instance.
Exact adapter reconstruction transfers the full-level pullback equation to the
old section-transport iff. Its `.mp` produces the two forward equations
`αg.P.val ≫ f.hom = β.P.val` and `αg.Q.val ≫ f.hom = β.Q.val`.

I freshly checked `Moduli/Coarse.lean:67–79`: the original raw `GammaHClasses`
relation asks precisely for `f`, `g`, `IsIso f.hom`, `g ∈ H`, and those two native
`mapPoint` equations. Subtype ext converts the actual scheme-arrow equalities to
these section equalities. The retained proof supplies exactly this witness to
`Quot.sound`; it neither assumes that the raw relation is already a setoid nor
uses a coarse-moduli classification theorem. Its mathematical argument is sound.

`Equiv.ofBijective` uses that injectivity and the previously checked actual full-lift
surjectivity. Its representative computation is definitional; the inverse-on-marking
API is the actual equivalence inverse law. The source-j formula is the already
checked given-curve source-j theorem. The inverse-on-full API applies equivalence
injectivity and the exact native classifier roundtrip. The inverse-on-specified-lift
API reverses `congrArg equiv.symm hq` before composing that full-point formula, so its
direction is correct. The two additional level-three examples exercise both inverse
laws on the actual native quotient and coarse scheme-point types.

Source review of all these additions: no mathematical issue. Native-class injectivity,
the equivalence, its representative/source-j computations and its two full-lift inverse
formulas are included in the actual new strict receipt and named artifacts above.

## Scope and remaining mathematical comparison

These classifier and transport proofs connect actual native marking relations to the
actual Borel scheme action. The checked descent adds a map from the pinned native
marked-curve classes to actual coarse complex scheme points, with the correct
representative and source-j formulas. The subsequent append supplies surjectivity
through genuine native roundtrip. The injectivity/equivalence append has passed both
source review and strict verification as recorded above. Thus, for nonzero levels
with `3 ≤ (N : ℤ)`, the actual native Borel full-marking classes are equivalent to the
actual coarse complex scheme points, preserving the given curve's source-j and
computing the inverse from any actual fine lift.

The existing native cyclic-subgroup lift theorem is a separate honest existence
statement. Identifying `GammaHClasses` with isomorphism classes of pairs `(E, C)` in the
exact fppf `GammaZeroStructure` sense still needs its own comparison. Neither this
review nor the reviewed adapters constructs `E/C`, a regular target-j, an analytic
Γ₀/lattice comparison, a Φ relation, or a scheme/function-field isomorphism.

Current checked snapshot: PASS-THROUGH, no mathematical issue in the six complete
retained modules. All six strict artifact checks passed. No Lean source edits or
compiler invocations were made by this reviewer. The separately authorized reverse
EllIso→HomOver converter has passed both actual source/orientation review and the
temporary and retained strict checks above. The parent owns the final
cumulative graph build and subsequent cyclic-pair classification/comparison work.
