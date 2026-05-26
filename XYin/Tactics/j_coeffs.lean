import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Ring.RingNF

open Lean Elab Tactic Meta

namespace XYin
namespace Tactics

namespace QjSandboxModel

def E4q : PowerSeries ℂ :=
  PowerSeries.mk (Function.update (fun m => (240 : ℂ) * ArithmeticFunction.sigma 3 m) 0 1)

def E6q : PowerSeries ℂ :=
  PowerSeries.mk (Function.update (fun m => -(504 : ℂ) * ArithmeticFunction.sigma 5 m) 0 1)

noncomputable def Delta_qexpansion : PowerSeries ℂ :=
  (1 / 1728 : ℂ) • (E4q ^ 3 - E6q ^ 2)

noncomputable def Deltaoverq_qexpansion : PowerSeries ℂ :=
  PowerSeries.mk (fun m => Delta_qexpansion.coeff (m + 1))

noncomputable def qj_qexpansion : PowerSeries ℂ :=
  E4q ^ 3 * Deltaoverq_qexpansion⁻¹

end QjSandboxModel

private structure ParsedCoeff where
  kExpr : Expr
  seriesExpr : Expr

private def parseCoeffExpr? (e : Expr) : Option ParsedCoeff :=
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  match fn, args with
  | ``PowerSeries.coeff, _ =>
      if args.size >= 4 then
        some { kExpr := args[2]!, seriesExpr := args[3]! }
      else
        none
  | ``DFunLike.coe, #[_, _, _, _, coeffPart, seriesExpr] =>
      let (cfn, cargs) := coeffPart.getAppFnArgs
      match cfn, cargs with
      | ``PowerSeries.coeff, #[_, _, kExpr] => some { kExpr, seriesExpr }
      | _, _ => none
  | _, _ => none

private def isQjSeriesExpr (e : Expr) : Bool :=
  match e.cleanupAnnotations.getAppFn with
  | .const n _ => n.toString.endsWith "qj_qexpansion"
  | _ => false

private def parseExistsQjCoeff? (target : Expr) : TacticM (Option Nat) := withMainContext do
  let (fn, args) := target.cleanupAnnotations.getAppFnArgs
  if fn != ``Exists || args.size != 2 then
    return none
  let domain := args[0]!
  let pred := args[1]!
  withLocalDeclD `x domain fun x => do
    let body ← whnf (mkApp pred x)
    let some (_, lhs, rhs) := body.eq? | return none
    let parsed? :=
      match parseCoeffExpr? lhs, parseCoeffExpr? rhs with
      | some c, _ => if rhs == x then some c else none
      | _, some c => if lhs == x then some c else none
      | _, _ => none
    let some parsed := parsed? | return none
    if !isQjSeriesExpr parsed.seriesExpr then
      return none
    return parsed.kExpr.cleanupAnnotations.numeral?

private def parseEqQjCoeff? (target : Expr) : TacticM (Option Nat) := withMainContext do
  let some (_, lhs, _) := target.cleanupAnnotations.eq? | return none
  let some parsed := parseCoeffExpr? lhs | return none
  if !isQjSeriesExpr parsed.seriesExpr then
    return none
  return parsed.kExpr.cleanupAnnotations.numeral?

private def sigmaPow (p n : Nat) : Int :=
  if n == 0 then
    0
  else
    Id.run do
      let mut s : Int := 0
      for d in [1:n+1] do
        if n % d == 0 then
          s := s + Int.ofNat (d ^ p)
      return s

private def mkCoeffArray (nMax : Nat) (f : Nat → Int) : Array Int :=
  Id.run do
    let mut arr : Array Int := #[]
    for n in [0:nMax+1] do
      arr := arr.push (f n)
    return arr

private def convAt (a b : Array Int) (n : Nat) : Int :=
  Id.run do
    let mut s : Int := 0
    for i in [0:n+1] do
      s := s + a[i]! * b[n - i]!
    return s

private def convArray (nMax : Nat) (a b : Array Int) : Array Int :=
  mkCoeffArray nMax (fun n => convAt a b n)

private def e4Coeff (n : Nat) : Int :=
  if n == 0 then 1 else 240 * sigmaPow 3 n

private def e6Coeff (n : Nat) : Int :=
  if n == 0 then 1 else -504 * sigmaPow 5 n

private structure QjData where
  e4 : Array Int
  e6 : Array Int
  e4Squared : Array Int
  e4Cubed : Array Int
  e6Squared : Array Int
  deltaOverQ : Array Int
  invDeltaOverQ : Array Int
  qj : Array Int

private def computeQjData (n : Nat) : QjData :=
  Id.run do
    let nMax := n + 1
    let e4 := mkCoeffArray nMax e4Coeff
    let e6 := mkCoeffArray nMax e6Coeff
    let e4sq := convArray nMax e4 e4
    let e4cu := convArray nMax e4sq e4
    let e6sq := convArray nMax e6 e6
    let delta := mkCoeffArray nMax (fun k => (e4cu[k]! - e6sq[k]!) / 1728)
    let deltaOverQ := mkCoeffArray n (fun k => delta[k + 1]!)
    let a0 := deltaOverQ[0]!
    let invA0 := 1 / a0
    let mut inv : Array Int := #[]
    for k in [0:n+1] do
      if k == 0 then
        inv := inv.push invA0
      else
        let mut s : Int := 0
        for i in [1:k+1] do
          s := s + deltaOverQ[i]! * inv[k - i]!
        inv := inv.push (-invA0 * s)
    let qj := mkCoeffArray n (fun k => convAt e4cu inv k)
    return ({
      e4 := e4
      e6 := e6
      e4Squared := e4sq
      e4Cubed := e4cu
      e6Squared := e6sq
      deltaOverQ := deltaOverQ
      invDeltaOverQ := inv
      qj := qj } : QjData)

private def complexIntTerm (z : Int) : TacticM (TSyntax `term) := do
  let zStx ← PrettyPrinter.delab (mkIntLit z)
  `((($zStx : ℤ) : ℂ))

private structure QjNames where
  e4 : TSyntax `term
  e6 : TSyntax `term
  delta : TSyntax `term
  deltaOverq : TSyntax `term
  qj : TSyntax `term

private def mkQjNames : QjNames where
  e4 := ⟨mkIdent `E4q⟩
  e6 := ⟨mkIdent `E6q⟩
  delta := ⟨mkIdent `Delta_qexpansion⟩
  deltaOverq := ⟨mkIdent `Deltaoverq_qexpansion⟩
  qj := ⟨mkIdent `qj_qexpansion⟩

private def asSimpLemma (t : TSyntax `term) :
    TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
  `(Lean.Parser.Tactic.simpLemma| $(t):term)

private def asRwRule (t : TSyntax `term) :
    TacticM (TSyntax `Lean.Parser.Tactic.rwRule) :=
  `(Lean.Parser.Tactic.rwRule| $(t):term)

private def indexedIdent (stem : String) (k : Nat) : TSyntax `ident :=
  ⟨mkIdent (Name.mkSimple s!"{stem}{k}")⟩

private def indexedTerm (stem : String) (k : Nat) : TSyntax `term :=
  ⟨mkIdent (Name.mkSimple s!"{stem}{k}")⟩

private def indexedSimpLemmas (stem : String) (stop : Nat) :
    TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let mut lemmas := #[]
  for k in [0:stop] do
    lemmas := lemmas.push (← asSimpLemma (indexedTerm stem k))
  return lemmas

private def indexedRwRules (stem : String) (stop : Nat) :
    TacticM (Array (TSyntax `Lean.Parser.Tactic.rwRule)) := do
  let mut rules := #[]
  for k in [0:stop] do
    rules := rules.push (← asRwRule (indexedTerm stem k))
  return rules

private def addE4Fact (names : QjNames) (k : Nat) (v : TSyntax `term) : TacticM Unit := do
  let e4 := names.e4
  let e4S ← asSimpLemma e4
  let hE4 := indexedIdent "hE4" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  evalTactic (← `(tactic|
    have $hE4 : PowerSeries.coeff $kStx $e4 = $v := by
      simp [$e4S, PowerSeries.coeff_mk,
        ArithmeticFunction.sigma, Function.update, Nat.divisors,
        Finset.sum_filter, Finset.sum_Ico_eq_sub, Finset.sum_range_succ]
      all_goals norm_num))

private def addE4Facts (names : QjNames) (data : QjData) (n : Nat) : TacticM Unit := do
  for k in [0:n+2] do
    addE4Fact names k (← complexIntTerm data.e4[k]!)

private def addE6Fact (names : QjNames) (k : Nat) (v : TSyntax `term) : TacticM Unit := do
  let e6 := names.e6
  let e6S ← asSimpLemma e6
  let hE6 := indexedIdent "hE6" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  evalTactic (← `(tactic|
    have $hE6 : PowerSeries.coeff $kStx $e6 = $v := by
      simp [$e6S, PowerSeries.coeff_mk,
        ArithmeticFunction.sigma, Function.update, Nat.divisors,
        Finset.sum_filter, Finset.sum_Ico_eq_sub, Finset.sum_range_succ]
      all_goals norm_num))

private def addE6Facts (names : QjNames) (data : QjData) (n : Nat) : TacticM Unit := do
  for k in [0:n+2] do
    addE6Fact names k (← complexIntTerm data.e6[k]!)

private def addE4SqFact (names : QjNames) (k : Nat) (v : TSyntax `term) : TacticM Unit := do
  let e4 := names.e4
  let hE4Sq := indexedIdent "hE4Sq" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let e4Rules ← indexedRwRules "hE4" (k + 1)
  evalTactic (← `(tactic|
    have $hE4Sq : PowerSeries.coeff $kStx ($e4 ^ 2) = $v := by
      rw [pow_two]
      rw [PowerSeries.coeff_mul]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [$[$e4Rules],*]
      all_goals norm_num))

private def addE4SqFacts (names : QjNames) (data : QjData) (n : Nat) : TacticM Unit := do
  for k in [0:n+2] do
    addE4SqFact names k (← complexIntTerm data.e4Squared[k]!)

private def addE4CubeFact (names : QjNames) (k : Nat) (v : TSyntax `term) : TacticM Unit := do
  let e4 := names.e4
  let hE4Cube := indexedIdent "hE4Cube" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let e4SqRules ← indexedRwRules "hE4Sq" (k + 1)
  let e4Rules ← indexedRwRules "hE4" (k + 1)
  evalTactic (← `(tactic|
    have $hE4Cube : PowerSeries.coeff $kStx ($e4 ^ 3) = $v := by
      rw [show $e4 ^ 3 = $e4 ^ 2 * $e4 by ring]
      rw [PowerSeries.coeff_mul]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [$[$e4SqRules],*, $[$e4Rules],*]
      all_goals norm_num))

private def addE4CubeFacts (names : QjNames) (data : QjData) (n : Nat) : TacticM Unit := do
  for k in [0:n+2] do
    addE4CubeFact names k (← complexIntTerm data.e4Cubed[k]!)

private def addE6SqFact (names : QjNames) (k : Nat) (v : TSyntax `term) : TacticM Unit := do
  let e6 := names.e6
  let hE6Sq := indexedIdent "hE6Sq" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let e6Rules ← indexedRwRules "hE6" (k + 1)
  evalTactic (← `(tactic|
    have $hE6Sq : PowerSeries.coeff $kStx ($e6 ^ 2) = $v := by
      rw [pow_two]
      rw [PowerSeries.coeff_mul]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [$[$e6Rules],*]
      all_goals norm_num))

private def addE6SqFacts (names : QjNames) (data : QjData) (n : Nat) : TacticM Unit := do
  for k in [0:n+2] do
    addE6SqFact names k (← complexIntTerm data.e6Squared[k]!)

private def addDeltaFact (names : QjNames) (k : Nat) (v : TSyntax `term) : TacticM Unit := do
  let deltaOverq := names.deltaOverq
  let delta := names.delta
  let deltaOverqS ← asSimpLemma deltaOverq
  let deltaS ← asSimpLemma delta
  let hE4Cube ← asRwRule (indexedTerm "hE4Cube" (k + 1))
  let hE6Sq ← asRwRule (indexedTerm "hE6Sq" (k + 1))
  let hDelta := indexedIdent "hDelta" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  evalTactic (← `(tactic|
    have $hDelta : PowerSeries.coeff $kStx $deltaOverq = $v := by
      simp [$deltaOverqS, $deltaS, PowerSeries.coeff_mk, PowerSeries.coeff_smul]
      rw [$hE4Cube, $hE6Sq]
      all_goals norm_num))

private def addDeltaFacts (names : QjNames) (data : QjData) (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addDeltaFact names k (← complexIntTerm data.deltaOverQ[k]!)

private def addDeltaConstFact (names : QjNames) : TacticM Unit := do
  let deltaOverq := names.deltaOverq
  let hDelta0 := indexedTerm "hDelta" 0
  evalTactic (← `(tactic|
    have hDeltaConst : PowerSeries.constantCoeff $deltaOverq = (((1 : ℤ) : ℂ)) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply $deltaOverq]
      exact $hDelta0))

private def addInvFact (names : QjNames) (k : Nat) (v : TSyntax `term) : TacticM Unit := do
  let deltaOverq := names.deltaOverq
  let hInv := indexedIdent "hInv" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let deltaRules ← indexedRwRules "hDelta" (k + 1)
  let invRules ← indexedRwRules "hInv" k
  evalTactic (← `(tactic|
    have $hInv : PowerSeries.coeff $kStx (($deltaOverq)⁻¹) = $v := by
      rw [PowerSeries.coeff_inv]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [hDeltaConst]
      try rw [$[$deltaRules],*, $[$invRules],*]
      all_goals norm_num))

private def addInvFacts (names : QjNames) (data : QjData) (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addInvFact names k (← complexIntTerm data.invDeltaOverQ[k]!)

private def finishQjProof (names : QjNames) (_n : Nat) : TacticM Unit := do
  let qj := names.qj
  let e4Facts ← indexedSimpLemmas "hE4Cube" (_n + 1)
  let invFacts ← indexedSimpLemmas "hInv" (_n + 1)
  evalTactic (← `(tactic| simp only [$(qj):term]))
  evalTactic (← `(tactic| rw [PowerSeries.coeff_mul]))
  evalTactic (← `(tactic| rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]))
  evalTactic (← `(tactic|
    simp only [Finset.sum_range_succ, $[$e4Facts],*, $[$invFacts],*]))
  evalTactic (← `(tactic| all_goals norm_num))

private def runJCoeffsCore (label : String) : TacticM Unit := withMainContext do
  let target ← getMainTarget
  let existsN? ← parseExistsQjCoeff? target
  let eqN? ←
    match existsN? with
    | some _ => pure none
    | none => parseEqQjCoeff? target
  let n? :=
    match existsN? with
    | some n => some n
    | none => eqN?
  let some n := n? |
    throwError s!"{label}: expected a qj coefficient at a concrete numeral."
  let names := mkQjNames
  let data := computeQjData n
  let w ← complexIntTerm data.qj[n]!
  if existsN?.isSome then
    evalTactic (← `(tactic| refine ⟨$w, ?_⟩))
  withTheReader Core.Context (fun ctx =>
      { ctx with maxHeartbeats := max ctx.maxHeartbeats 10000000000 }) do
    addE4Facts names data n
    addE6Facts names data n
    addE4SqFacts names data n
    addE4CubeFacts names data n
    addE6SqFacts names data n
    addDeltaFacts names data n
    addDeltaConstFact names
    addInvFacts names data n
    finishQjProof names n
  logInfo m!"[{label}] computed result: {data.qj[n]!}"

private def withElapsedLog (label : String) (act : TacticM Unit) : TacticM Unit := do
  let start ← IO.monoMsNow
  try
    act
    let stop ← IO.monoMsNow
    logInfo m!"[{label}] elapsed: {stop - start}ms"
  catch ex =>
    let stop ← IO.monoMsNow
    logInfo m!"[{label}] failed after: {stop - start}ms"
    throw ex

private def runJCoeffsCertify : TacticM Unit :=
  runJCoeffsCore "j_coeffs_certify"

syntax (name := jCoeffsCertify) "j_coeffs_certify" : tactic

elab_rules : tactic
  | `(tactic| j_coeffs_certify) => runJCoeffsCertify

private def runJCoeffs : TacticM Unit :=
  runJCoeffsCore "j_coeffs"

syntax (name := jCoeffs) "j_coeffs" : tactic

elab_rules : tactic
  | `(tactic| j_coeffs) => withElapsedLog "j_coeffs" runJCoeffs

end Tactics
end XYin
