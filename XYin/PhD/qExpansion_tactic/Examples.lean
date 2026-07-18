/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import XYin.PhD.qExpansion_tactic.Qj

/-!
# Examples for the `#qexp` commands and the `qexp_coeff` elaborator

Demonstrations of the `q`-expansion tactic layer from `XYin.PhD.qExpansion_tactic.Qj`:
the informational `#qexp _ coeff` / `#qexp _ precision` commands and the proof-producing
`qexp_coeff` term elaborator, in both its automatic form (the coefficient value is
computed during elaboration) and its manual form (the expected value is supplied and
certified).  All examples are facts about the formal power series `qj_qexpansion` and
`Delta_qexpansion` in `ℤ⟦X⟧`; see `XYin.PhD.qExpansion_tactic.link` for the bridge to
the analytic modular objects.
-/

open XYin.PhD.qExpansion_tactic
open scoped XYin.PhD.qExpansion_tactic

-- Display the fourth `q·j` coefficient, and all coefficients up to the fourth.
#qexp qj coeff 4
#qexp qj precision 4

-- The elaborated proof terms and their statements, in auto and manual form.
#check qexp_coeff qj 4
#check qexp_coeff qj 4 864299970

-- Auto mode: the value `864299970` (the `j`-invariant coefficient `c(3)`) is
-- discovered during elaboration.
example : qj_qexpansion.coeff 4 = 864299970 := qexp_coeff qj 4

-- Manual mode: the expected value is supplied and certified.
example : qj_qexpansion.coeff 4 = 864299970 := qexp_coeff qj 4 864299970

-- The same commands for the discriminant `Δ`.
#qexp Delta coeff 4
#qexp Delta precision 4

#check qexp_coeff Delta 4
#check qexp_coeff Delta 4 (-1472)

-- Auto mode for `Δ`: the Ramanujan tau value `τ(4) = -1472` is discovered.
example : Delta_qexpansion.coeff 4 = -1472 := qexp_coeff Delta 4

-- Manual mode for `Δ`.
example : Delta_qexpansion.coeff 4 = -1472 := qexp_coeff Delta 4 (-1472)

-- A larger instance: the hundredth coefficient is still computed instantly.
#qexp qj coeff 100
#qexp qj precision 100

/-
Stress tests, commented out to keep this file fast to build: the native-evaluation
route scales to `n = 2000`, where the `q·j` coefficient is a 238-digit integer.
`#qexp qj coeff 2000` prints the value, and `#check qexp_coeff qj 2000` elaborates a
full `native_decide`-backed proof of the corresponding coefficient identity (auto mode,
so the 238-digit value need not be written out).

#qexp qj coeff 1000
#qexp qj coeff 2000
#check qexp_coeff qj 2000
-/
