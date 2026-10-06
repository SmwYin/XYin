# Borel changes preserve the embedded constant-axis subgroup ideal

The retained module is `AINTLIBDrafts/YZeroCoarseBorelAxis.lean`, in namespace
`ModularPolynomialCurveTest.AINTLIB.ConstantAxis`. It imports only the retained
`YZeroCoarseConstantAxis` bridge.

For a fixed actual elliptic curve `E` over `Spec R`, an invertible level `N`, a
naive full marking `L`, and `g : ↥(borel N)`, the theorem
`sectionAxisSubgroup_glSmul_borel_ker` proves the literal ideal equality

```lean
(sectionAxisSubgroup R N E hinv (E.glSmul g.val L)).ι.ker =
  (sectionAxisSubgroup R N E hinv L).ι.ker
```

Both ideals live in the same fixed curve `E.E`. The marking change replaces the
first section `P` by `(g₀₀.val : ℤ) • P`: the other coefficient is zero because
`g₁₀ = 0`. The actual matrix determinant is a unit, so
`det(g) = g₀₀ * g₁₁` makes `g₀₀` a unit. This is
`borel_fstEntry_isUnit`, using the same determinant calculation as the pinned
Borel subgroup's inverse-membership proof.

The generic theorem `sectionAxis_zsmul_of_unit` works over every scheme `S`:
for an `N`-killed section `P` and `v : (ZMod N)ˣ`,

```lean
sectionAxis E (((v : ZMod N).val : ℤ) • P) =
  (Sigma.reindex v.mulLeft (fun _ : ZMod N ↦ S)).hom ≫ sectionAxis E P
```

This is positive multiplication of labels, `a ↦ v * a`. On the `a`-component,
`val_smul_mul` identifies the lifted residue-class product with the composed
integer scalars. Reindexing is an actual scheme isomorphism, so
`Scheme.Hom.ker_comp_of_isIso` gives the ideal equality. Invertibility of `N`
on the base is used only by the existing subgroup constructor; the generic
scalar/reindexing argument needs no `N ≥ 3`, domain, field, or nontrivial-base
assumption.

The result establishes invariance of the embedded subgroup ideal under Borel
re-marking. Literal equality of `GammaZeroStructure` records, classification of
such records, and descent of a quotient-curve `j` invariant are separate results
and are not conclusions of this module.

Three sanity examples check a nonidentity unit modulo 3, the actual Borel
subgroup API at level 3, and a literal positive reindexing morphism equation
modulo 5. The last uses unit `2` with inverse `3`, so its displayed morphism
formula tests the direction of reindexing directly.

The temporary final fixture has 91 lines and SHA-256
`002c7fb1ffa02bc7cab397d04cd730d8b8f4c764f66b69f8a5bb6fa0bb3b5493`.
Its strict compile exited 0 with no warnings/errors and seven clean axiom
prints. Receipt: `/private/tmp/YZeroBorelAxisProbe.log`. The original failed
family-matching run is preserved separately at
`/private/tmp/YZeroBorelAxisProbe.first-failure.log`; its staged downstream
axiom output is excluded. The subsequent kernel-green run's deprecated-name
warning is preserved at `/private/tmp/YZeroBorelAxisProbe.kernel-green-warning.log`.
The retained proof explicitly types the constant family as its composition
with the label permutation before applying the actual reindexing equation.

The retained file has 119 lines and SHA-256
`9ee3ab2ae2024383b9a5712038ba2f238aa43678eae04166e9f2d6a34eb68703`.
It preserves the accepted three proofs and three sanity examples. The correctly
named strict artifact emission exited 0 with zero warnings/errors; all seven
printed checks depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Receipt: `/private/tmp/xyin-y0-borel-axis.log`.

The isolated environment pins AINTLIB
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, and Lean `v4.35.0-rc3`.
The setup `/private/tmp/YZeroCoarseBorelAxis.setup.json` names
`AINTLIBDrafts.YZeroCoarseBorelAxis` and sets both `autoImplicit` and
`relaxedAutoImplicit` to `false`. From `/private/tmp/xyin-y0-aintlib-work`, the
exact invocation was:

```sh
/private/tmp/xyin-y0-elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean -DautoImplicit=false -DrelaxedAutoImplicit=false --setup /private/tmp/YZeroCoarseBorelAxis.setup.json -o .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseBorelAxis.olean -i .lake/build/lib/lean/AINTLIBDrafts/YZeroCoarseBorelAxis.ilean -c .lake/build/ir/AINTLIBDrafts/YZeroCoarseBorelAxis.c AINTLIBDrafts/YZeroCoarseBorelAxis.lean > /private/tmp/xyin-y0-borel-axis.log 2>&1
```

The `.olean`, `.olean.private`, `.olean.server`, `.ilean`, `.ir`, `.ir.sig`,
and `.c` artifacts are present in the isolated build directories. The retained
source and isolated copy were byte-equal after compilation. The local XYin
toolchain and all previously frozen bridge sources were unchanged.
