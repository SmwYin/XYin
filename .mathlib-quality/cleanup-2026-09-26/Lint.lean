import XYin
import Batteries.Tactic.Lint

/-! Project-wide lint of every declaration in a module under `XYin` (2026-09-26, worker finb). -/

-- The simp / argument / docstring linters requested for the cleanup.
#lint only simpNF simpComm simpVarHead unusedArguments defLemma docBlame synTaut in XYin

-- The full default set; its only findings are `defsWithUnderscore` naming hits (deferred).
#lint- in XYin
