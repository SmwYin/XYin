# The old coordinate cannot generally descend to the actual quotient

The retained `NativeCoordinateTowerObstruction.lean` uses the source's actual
Weierstrass RatFunc embedding, not an arbitrary coordinate. Its native field has
degree two over that embedding. If the genuine quotient function field admits an
algebra under this same RatFunc embedding, compatible with the actual quotient
field pullback, the scalar-tower degree law forces its subgroup rank to divide two.
The rank-three API refutes any such compatible tower. This is a conditional
obstruction; the theorem does not assume or assert a quotient coordinate exists.

The strict temporary proof passed in owner-polled session71641, exit0 after two
preserved binder-normalization failures. Correct-name emission15954 was
owner-polled CLOSED, exit0: five exact std3 checks, two actual subgroup APIs,
zero diagnostics. The accepted proof was retained with header/documentation only.
The original independent geometric source scalars and native field map remain.

112 lines, width96; retained/work SHA
`9518c05e4d132ba0247c8a596e572f3489ffc9b4f8345875d2c53777abeb6821`.
Six nonempty canonical Lean outputs and C were individually hashed in
`/private/tmp/NativeCoordinateTowerObstruction-receipt.json`; full named log is
`/private/tmp/NativeCoordinateTowerObstruction-named.log`.
Independent full-source/log/setup/output-hash mathematical review by the build
auditor passed. Strict implicit options remain false, with no plugins/dynlibs.
This leaf follows and is excluded from the historical99-module checkpoint.
