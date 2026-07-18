/-
Copyright (c) 2026 The XYin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The XYin contributors
-/
import Lean
import Lean.Meta.Native
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Util.Qq

/-!
# Fast integer computation of the `q`-expansions of `Δ` and `q·j`

This file is the computational engine of the `q`-expansion tactic layer: fast integer
arithmetic for the `q`-expansion coefficients of the discriminant `Δ` and of `q·j`
(`j` the modular `j`-invariant), via divisor power sums, array convolutions, and
power-series inversion, entirely in `Array Int`.

On top of the computational layer we define the formal power series `Delta_qexpansion`
and `qj_qexpansion` in `ℤ⟦X⟧`, the informational `#qexp` commands, and the
proof-producing `qexp_coeff` term elaborator, which certifies coefficient identities
such as `qj_qexpansion.coeff 4 = 864299970` by compiled native evaluation.  Proofs
produced this way depend on the `Lean.ofReduceBool` axiom (the `native_decide` trust
base).  The identification of these formal series with the analytic `q`-expansions of
`Δ` and `q·j` is carried out in `XYin.PhD.qExpansion_tactic.link`.

## Main definitions

* `deltaCoeffInt`, `qjCoeffInt`: the `n`-th `q`-expansion coefficient of `Δ`
  (the Ramanujan `τ` function) and of `q·j`, computed by array convolutions.
* `Delta_qexpansion`, `qj_qexpansion`: the corresponding formal series in `ℤ⟦X⟧`.
* `mkQexpCoeffProof`: the `MetaM` routine producing `native_decide`-backed proofs of
  coefficient identities for a `QexpTarget`.
* `qexp_coeff` (term syntax) and `#qexp` (command syntax): the user-facing entry points.
-/

open scoped Qq

namespace XYin.PhD.qExpansion_tactic

/-- Whether the `#qexp` commands and the `qexp_coeff` elaborator log elapsed wall-clock
time (configured by editing this definition). -/
def reportTiming : Bool := true

/-- Sum of `d^k` over positive divisors `d` of `n`, computed by finite search. -/
def sigmaPow (k n : Nat) : Int :=
  (List.range n).foldl
    (fun acc i =>
      let d := i + 1
      if n % d = 0 then acc + (d : Int) ^ k else acc)
    0

/-- The `n`-th `q`-expansion coefficient of the normalized Eisenstein series
`E₄ = 1 + 240·∑ σ₃(n) qⁿ`. -/
def e4CoeffInt (n : Nat) : Int :=
  if n = 0 then 1 else 240 * sigmaPow 3 n

/-- The `n`-th `q`-expansion coefficient of the normalized Eisenstein series
`E₆ = 1 - 504·∑ σ₅(n) qⁿ`. -/
def e6CoeffInt (n : Nat) : Int :=
  if n = 0 then 1 else -504 * sigmaPow 5 n

/-- Evaluate a coefficient function on indices `0..n` into an array. -/
def coeffArray (f : Nat → Int) (n : Nat) : Array Int :=
  (List.range (n + 1)).foldl (fun acc i => acc.push (f i)) #[]

/-- Convolution coefficient `(a * b)_n = Σ_{i=0..n} a_i b_{n-i}`. -/
def convArrayCoeff (a b : Array Int) (n : Nat) : Int :=
  (List.range (n + 1)).foldl
    (fun acc i => acc + a.getD i 0 * b.getD (n - i) 0)
    0

/-- Convolution table up to index `n`. -/
def convArrayUpTo (a b : Array Int) (n : Nat) : Array Int :=
  (List.range (n + 1)).foldl
    (fun acc i => acc.push (convArrayCoeff a b i))
    #[]

/-- Coefficients of `(1 + a₁q + a₂q² + ...)⁻¹` up to index `n` (inclusive). -/
def inverseOnePlusCoeffsUpTo (a : Array Int) (n : Nat) : Array Int :=
  (List.range (n + 1)).foldl
    (fun acc k =>
      match k with
      | 0 => acc.push 1
      | m + 1 =>
          let next :=
            -((List.range (m + 1)).foldl
              (fun s i => s + a.getD (i + 1) 0 * acc.getD (m - i) 0)
              0)
          acc.push next)
    #[]

/-- The `q`-expansion coefficients of `Δ = (E₄³ - E₆²)/1728` up to index `n`
(the Ramanujan `τ` values `τ(0) = 0, τ(1) = 1, τ(2) = -24, …`).  The integer division
by `1728` is exact by the classical congruence `E₄³ ≡ E₆² [MOD 1728]`. -/
def deltaCoeffsArrayUpTo (n : Nat) : Array Int :=
  let e4 := coeffArray e4CoeffInt n
  let e6 := coeffArray e6CoeffInt n
  let e4Sq := convArrayUpTo e4 e4 n
  let e4Cube := convArrayUpTo e4Sq e4 n
  let e6Sq := convArrayUpTo e6 e6 n
  (List.range (n + 1)).foldl
    (fun acc i => acc.push ((e4Cube.getD i 0 - e6Sq.getD i 0) / 1728))
    #[]

/-- The `n`-th `q`-expansion coefficient of `Δ`, i.e. the Ramanujan `τ(n)`. -/
def deltaCoeffInt (n : Nat) : Int := (deltaCoeffsArrayUpTo n).getD n 0

/-- The list of `Δ`-coefficients `[τ(0), …, τ(n)]` (for `#qexp Delta precision`). -/
def deltaCoeffsUpTo (n : Nat) : List Int := (deltaCoeffsArrayUpTo n).toList

/-- The `n`-th coefficient of the unit power series `Δ/q = 1 - 24q + 252q² - …`. -/
def deltaOverQCoeffInt (n : Nat) : Int := deltaCoeffInt (n + 1)

/-- The coefficients of `Δ/q` up to index `n`, as an array. -/
def deltaOverQArrayUpTo (n : Nat) : Array Int :=
  let delta := deltaCoeffsArrayUpTo (n + 1)
  (List.range (n + 1)).foldl
    (fun acc i => acc.push (delta.getD (i + 1) 0))
    #[]

/-- The coefficients of `q/Δ = (Δ/q)⁻¹` up to index `n`. -/
def qoverDeltaCoeffsArrayUpTo (n : Nat) : Array Int :=
  inverseOnePlusCoeffsUpTo (deltaOverQArrayUpTo n) n

/-- The `n`-th coefficient of the power series `q/Δ`. -/
def qoverDeltaCoeffInt (n : Nat) : Int :=
  (qoverDeltaCoeffsArrayUpTo n).getD n 0

/-- The `q`-expansion coefficients of `q·j = E₄³·(q/Δ)` up to index `n`; entry `n` is
the `j`-invariant Fourier coefficient `c(n-1)`, so the array starts `1, 744, 196884, …`. -/
def qjCoeffsArrayUpTo (n : Nat) : Array Int :=
  let top := n + 1
  let e4 := coeffArray e4CoeffInt top
  let e4Sq := convArrayUpTo e4 e4 top
  let e4Cube := convArrayUpTo e4Sq e4 top
  convArrayUpTo e4Cube (qoverDeltaCoeffsArrayUpTo n) n

/-- The `n`-th coefficient of `q·j`, i.e. the `j`-invariant coefficient `c(n-1)`. -/
def qjCoeffInt (n : Nat) : Int := (qjCoeffsArrayUpTo n).getD n 0

/-- The list of `q·j` coefficients `[1, 744, 196884, …]` (for `#qexp qj precision`). -/
def qjCoeffsUpTo (n : Nat) : List Int := (qjCoeffsArrayUpTo n).toList

/-- The formal power series `∑ qjCoeffInt(n)·qⁿ ∈ ℤ⟦q⟧`, the candidate `q`-expansion of
`q·j`; identified with the analytic expansion in `link.lean`. -/
def qj_qexpansion : PowerSeries ℤ :=
  PowerSeries.mk qjCoeffInt

/-- The `n`-th coefficient of `qj_qexpansion` is the computed integer `qjCoeffInt n`. -/
theorem qj_qexpansion_coeff_eq (n : Nat) :
    qj_qexpansion.coeff n = qjCoeffInt n := by
  simp [qj_qexpansion]

/-- The formal power series `∑ τ(n)·qⁿ ∈ ℤ⟦q⟧`, the candidate `q`-expansion of `Δ`;
identified with the analytic expansion in `link.lean`. -/
def Delta_qexpansion : PowerSeries ℤ :=
  PowerSeries.mk deltaCoeffInt

/-- The `n`-th coefficient of `Delta_qexpansion` is the computed `deltaCoeffInt n`. -/
theorem Delta_qexpansion_coeff_eq (n : Nat) :
    Delta_qexpansion.coeff n = deltaCoeffInt n := by
  simp [Delta_qexpansion]

open Lean Meta in
/-- Produce a proof of the decidable proposition `p` by compiled native evaluation of its
`Decidable` instance (a programmatic `native_decide`).  The resulting proof depends on
the `Lean.ofReduceBool` axiom. -/
def mkNativeDecideProofFor (p : Expr) : MetaM Expr := do
  let d ← mkDecide p
  match (← nativeEqTrue `qexp_coeff d) with
  | .notTrue =>
      throwError "native_decide evaluated proposition as false{indentExpr p}"
  | .success prf =>
      let inst := d.appArg!
      return mkApp3 (mkConst ``of_decide_eq_true) p inst prf

open Lean in
/-- The data describing one target of the `#qexp`/`qexp_coeff` machinery: a formal power
series together with its computable coefficient function (as a value for evaluation and
as a name for proof construction) and the bridging coefficient lemma. -/
structure QexpTarget where
  /-- The formal power series whose coefficient identities are certified. -/
  series : Q(PowerSeries ℤ)
  /-- The name of the computable coefficient function (e.g. `qjCoeffInt`). -/
  coeffName : Name
  /-- The name of the lemma `series.coeff n = coeffName n`. -/
  coeffEqName : Name
  /-- The coefficient function itself, for evaluation inside the elaborators. -/
  coeffFn : Nat → Int
  /-- The coefficient list `[c(0), …, c(n)]`, for the `#qexp _ precision` command. -/
  coeffsUpTo : Nat → List Int

/-- The `qexp_coeff`/`#qexp` target data for `q·j`. -/
def qjTarget : QexpTarget where
  series := q(qj_qexpansion)
  coeffName := ``qjCoeffInt
  coeffEqName := ``qj_qexpansion_coeff_eq
  coeffFn := qjCoeffInt
  coeffsUpTo := qjCoeffsUpTo

/-- The `qexp_coeff`/`#qexp` target data for `Δ`. -/
def deltaTarget : QexpTarget where
  series := q(Delta_qexpansion)
  coeffName := ``deltaCoeffInt
  coeffEqName := ``Delta_qexpansion_coeff_eq
  coeffFn := deltaCoeffInt
  coeffsUpTo := deltaCoeffsUpTo

/-- Look up the target data for a `#qexp`/`qexp_coeff` identifier (`qj` or `Delta`). -/
def qexpTarget? : Lean.Name → Option QexpTarget
  | `qj => some qjTarget
  | `Delta => some deltaTarget
  | _ => none

open Lean Meta Qq in
/-- Build a proof term of `t.series.coeff n = xQ` by chaining the bridging lemma
`t.coeffEqName` with a native-evaluation certificate of `t.coeffName n = xQ`
(via `mkNativeDecideProofFor`).  Fails if `xQ` does not evaluate to the actual
coefficient; `xQ` may be any closed integer term, not only a literal. -/
def mkQexpCoeffProof (t : QexpTarget) (n : Nat) (xQ : Q(ℤ)) : MetaM Expr := do
  let nQ : Q(Nat) := Qq.mkNatLitQ n
  let propExpr ← mkEq (← mkAppM t.coeffName #[nQ]) xQ
  let hval ← mkNativeDecideProofFor propExpr
  let proof0 ← mkAppM t.coeffEqName #[nQ]
  let proofExpr ← mkAppM ``Eq.trans #[proof0, hval]
  let series : Q(PowerSeries ℤ) := t.series
  let target : Q(Prop) := q(($series).coeff $nQ = $xQ)
  mkExpectedTypeHint proofExpr target

/-- `#qexp qj coeff n` / `#qexp Delta coeff n` prints a single `q`-expansion
coefficient (informational; produces no proof term). -/
syntax (name := qexpCoeffCmd) "#qexp" ident "coeff" num : command

/-- `#qexp qj precision n` / `#qexp Delta precision n` prints all coefficients up to
index `n` (informational; produces no proof term). -/
syntax (name := qexpPrecisionCmd) "#qexp" ident "precision" num : command

open Lean Elab Command in
elab_rules : command
  | `(command| #qexp $which:ident coeff $n:num) => do
      let some t := qexpTarget? which.getId
        | throwErrorAt which "unknown q-expansion target; expected `qj` or `Delta`"
      let nVal := n.getNat
      let t0 ← liftIO IO.monoMsNow
      let valueStr := toString (t.coeffFn nVal)
      if valueStr.length == 0 then
        throwError "internal error: empty q-expansion coefficient output"
      let t1 ← liftIO IO.monoMsNow
      logInfoAt n valueStr
      if reportTiming then
        logInfoAt n m!"[qexp time: {t1 - t0}ms]"
  | `(command| #qexp $which:ident precision $n:num) => do
      let some t := qexpTarget? which.getId
        | throwErrorAt which "unknown q-expansion target; expected `qj` or `Delta`"
      let nVal := n.getNat
      let t0 ← liftIO IO.monoMsNow
      let valueStr := toString (t.coeffsUpTo nVal)
      if valueStr.length == 0 then
        throwError "internal error: empty q-expansion precision output"
      let t1 ← liftIO IO.monoMsNow
      logInfoAt n valueStr
      if reportTiming then
        logInfoAt n m!"[qexp time: {t1 - t0}ms]"

end XYin.PhD.qExpansion_tactic

/-- `qexp_coeff qj n` / `qexp_coeff Delta n`: a proof term of the coefficient identity
`qj_qexpansion.coeff n = c` (resp. for `Delta_qexpansion`), with the value `c` computed
automatically.  The proof depends on the `Lean.ofReduceBool` axiom. -/
syntax (name := qexpCoeffAuto) "qexp_coeff" ident num : term

/-- `qexp_coeff qj n x` / `qexp_coeff Delta n x`: a proof term of
`qj_qexpansion.coeff n = x` (resp. for `Delta_qexpansion`) for a user-supplied value
`x`; elaboration fails if `x` is not the actual coefficient. -/
syntax (name := qexpCoeffManual) "qexp_coeff" ident num term : term

open Lean Elab Term XYin.PhD.qExpansion_tactic in
elab_rules : term
  | `(qexp_coeff $which:ident $n:num) => do
      let some t := qexpTarget? which.getId
        | throwErrorAt which "unknown q-expansion target; expected `qj` or `Delta`"
      let nVal := n.getNat
      let t0 ← IO.monoMsNow
      let xQ : Q(ℤ) := Qq.mkIntLitQ (t.coeffFn nVal)
      let proof ← Lean.Meta.liftMetaM <| mkQexpCoeffProof t nVal xQ
      let t1 ← IO.monoMsNow
      if reportTiming then
        logInfoAt n m!"[qexp_coeff time: {t1 - t0}ms]"
      pure proof
  | `(qexp_coeff $which:ident $n:num $x:term) => do
      let some t := qexpTarget? which.getId
        | throwErrorAt which "unknown q-expansion target; expected `qj` or `Delta`"
      let nVal := n.getNat
      let xExpr ← elabTermEnsuringType x q(ℤ)
      synthesizeSyntheticMVarsNoPostponing
      let xQ : Q(ℤ) ← instantiateMVars xExpr
      let t0 ← IO.monoMsNow
      let proof ← Lean.Meta.liftMetaM <| mkQexpCoeffProof t nVal xQ
      let t1 ← IO.monoMsNow
      if reportTiming then
        logInfoAt n m!"[qexp_coeff time: {t1 - t0}ms]"
      pure proof
