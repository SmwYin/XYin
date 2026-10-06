# Finite flat scheme degree: single-module verification

Pinned AINTLIB `ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, mathlib
`300d0e535721bc098547106fc297d8ba2a63f6bb`, Lean `4.35.0-rc3`.

Retained source `/Users/dfa25dxu/Projects/Lean/XYin/XYin/PhD/Test/ModularPolynomialCurve/AINTLIBDrafts/FiniteFlatFunctionFieldDegree.lean`: 126 lines, SHA256 `6405935361d6aa44a1ef735f01d67adb3e7eadb967ed3d60f5ee5142ec5708e4`.
The isolated source is byte-identical. Only a minimal licence/scope header
was added to accepted107; its complete mathematical suffix is unchanged.

The theorem applies to finite flat dominant maps between integral schemes,
with the literal native `functionFieldAlgebra`. It uses a nonempty affine
neighbourhood of the specified target point. Native germs establish both
scalar towers and both function fields as fraction rings; injectivity gives
faithful scalar action. The actual `toSpecΓ` pullback transports fibre rank
to the affine fraction-field rank identity. No Noetherian, genus or elliptic
model assumption is introduced. Identity-induced modules and finite flat
Spec maps are checked as two distinct API examples.

Independent reviewer `/root/y0_j_descent` read the complete107 source and
complete third log, checking every scalar/pullback orientation and example.
Named session11602 CLOSED exit0: ten exact standard-three axiom outputs,
two examples, zero diagnostics. Strict named setup `/private/tmp/xyin-y0-aintlib-work/FiniteFlatFunctionFieldDegree.setup.json` preserves
both implicit options false. Six canonical Lean outputs and the C output
have size/SHA receipts in `/private/tmp/FiniteFlatFunctionFieldDegree-receipt.json`.

The first failed staging check (app vs appLE and implicit SpecMap_iff)
is excluded. The second and third checks both closed successfully. This
leaf is after the 60-module checkpoint and awaits the next cumulative gate.
It is a degree bridge; it proves no quotient genus, Weierstrass presentation,
target j or modular-polynomial identity.
