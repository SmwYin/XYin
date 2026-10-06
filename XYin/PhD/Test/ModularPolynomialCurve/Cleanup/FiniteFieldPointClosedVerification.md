# Finite field-valued points have closed image

`FiniteFieldPointClosed.lean` gives a reusable separated-over-field statement:
a point defined over a finite extension, with its actual over-base triangle,
has closed image. It needs no finite-type or properness assumption on the whole
scheme. Finiteness of the actual composite cancels by separatedness; the range
is a singleton because the extension field spectrum is subsingleton.

Strict temporary5882 and correct-name2594 were owner-polled CLOSED, exit0.
Five exact std3 checks, two rational/finite-extension API examples, zero diagnostics.
The earlier temporary failure affected only a misnamed final primitive print;
its proof/source/log were preserved. No statement or proof was changed by that fix.

62 lines, width85; retained/work SHA
`01684af0afa95f5732b06ef6629d6a511b3b95dcc0641cffe9d7f3a1d7621ba6`.
Six canonical Lean artifacts plus C are individually hashed in
`/private/tmp/FiniteFieldPointClosed-receipt.json`. Full named log is
`/private/tmp/FiniteFieldPointClosed-named.log`.
Build auditor independently reviewed the whole source, output and present hashes:
PASS. Strict implicit settings remain false, no plugins/dynlibs.
This leaf is excluded from the historical99-module checkpoint.
