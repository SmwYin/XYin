import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Ring.RingNF
import XYin.Tactics.j_coeffs

open Lean Elab Tactic Meta

namespace XYin
namespace Tactics

private inductive GeneratorTag where
  | E4
  | E6
  deriving BEq, DecidableEq, Repr

-- The current evaluator is rational-valued, matching E4/E6 and rational-coefficient generators.
private structure GeneratorSpec where
  tag : GeneratorTag
  suffix : String
  coeffRat : Nat → Rat
  simpNames : Array Name := #[]

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

private def e4CoeffRat (n : Nat) : Rat :=
  if n == 0 then 1 else ((240 * sigmaPow 3 n : Int) : Rat)

private def e6CoeffRat (n : Nat) : Rat :=
  if n == 0 then 1 else ((-504 * sigmaPow 5 n : Int) : Rat)

private def divisorSumSimpNames : Array Name :=
  #[
    ``ArithmeticFunction.sigma,
    ``Function.update,
    ``Nat.divisors,
    ``Finset.sum_filter,
    ``Finset.sum_Ico_eq_sub,
    ``Finset.sum_range_succ
  ]

private def generatorRegistry : Array GeneratorSpec :=
  #[
    { tag := .E4, suffix := "E4q", coeffRat := e4CoeffRat, simpNames := divisorSumSimpNames },
    { tag := .E6, suffix := "E6q", coeffRat := e6CoeffRat, simpNames := divisorSumSimpNames }
  ]

private def findGeneratorSpecBySuffix? (n : Name) : Option GeneratorSpec :=
  generatorRegistry.find? (fun spec => n.toString.endsWith spec.suffix)

private def isQjSeriesExpr (e : Expr) : Bool :=
  match e.cleanupAnnotations.getAppFn with
  | .const n _ => n.toString.endsWith "qj_qexpansion"
  | _ => false

private structure ParsedCoeffTarget where
  n : Nat
  seriesExpr : Expr

private def parseCoeffExpr? (e : Expr) : Option (Expr × Expr) :=
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  match fn, args with
  | ``PowerSeries.coeff, _ =>
      if args.size >= 4 then
        some (args[2]!, args[3]!)
      else
        none
  | ``DFunLike.coe, #[_, _, _, _, coeffPart, seriesExpr] =>
      let (cfn, cargs) := coeffPart.getAppFnArgs
      match cfn, cargs with
      | ``PowerSeries.coeff, #[_, _, kExpr] => some (kExpr, seriesExpr)
      | _, _ => none
  | _, _ => none

private def parseExistsCoeffTarget? (target : Expr) : TacticM (Option ParsedCoeffTarget) :=
    withMainContext do
  let (fn, args) := target.cleanupAnnotations.getAppFnArgs
  if fn != ``Exists || args.size != 2 then
    return none
  let domain := args[0]!
  let pred := args[1]!
  unless (← isDefEq domain (mkConst ``Complex)) do
    return none
  withLocalDeclD `x domain fun x => do
    let body ← whnf (mkApp pred x)
    let some (_, lhs, rhs) := body.eq? | return none
    let parsed? :=
      match parseCoeffExpr? lhs, parseCoeffExpr? rhs with
      | some c, _ => if rhs == x then some c else none
      | _, some c => if lhs == x then some c else none
      | _, _ => none
    let some (kExpr, seriesExpr) := parsed? | return none
    let some n := kExpr.cleanupAnnotations.numeral? | return none
    return some { n := n, seriesExpr := seriesExpr }

private def parseEqCoeffTarget? (target : Expr) : TacticM (Option ParsedCoeffTarget) :=
    withMainContext do
  let some (_, lhs, rhs) := target.cleanupAnnotations.eq? | return none
  let parsed? :=
    match parseCoeffExpr? lhs, parseCoeffExpr? rhs with
    | some c, _ => some c
    | _, some c => some c
    | _, _ => none
  let some (kExpr, seriesExpr) := parsed? | return none
  let some n := kExpr.cleanupAnnotations.numeral? | return none
  return some { n := n, seriesExpr := seriesExpr }

private def parseCoeffTarget? (target : Expr) : TacticM (Option (Bool × ParsedCoeffTarget)) := do
  if let some parsed ← parseExistsCoeffTarget? target then
    return some (true, parsed)
  if let some parsed ← parseEqCoeffTarget? target then
    return some (false, parsed)
  return none

private def parseAddArgs? (e : Expr) : Option (Expr × Expr) :=
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  if (fn == ``HAdd.hAdd || fn == ``Add.add) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    none

private def parseSubArgs? (e : Expr) : Option (Expr × Expr) :=
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  if (fn == ``HSub.hSub || fn == ``Sub.sub) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    none

private def parseMulArgs? (e : Expr) : Option (Expr × Expr) :=
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  if (fn == ``HMul.hMul || fn == ``Mul.mul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    none

private def parseSmulArgs? (e : Expr) : Option (Expr × Expr) :=
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  if (fn == ``HSMul.hSMul || fn == ``SMul.smul) && args.size >= 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    none

private def parseNegArg? (e : Expr) : Option Expr :=
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  if fn == ``Neg.neg && args.size >= 1 then
    some args[args.size - 1]!
  else
    none

private def parseInvArg? (e : Expr) : Option Expr :=
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  if fn == ``Inv.inv && args.size >= 1 then
    some args[args.size - 1]!
  else
    none

private partial def parseRatScalar? (e : Expr) : MetaM (Option Rat) := do
  let e := e.cleanupAnnotations
  if let some n := e.numeral? then
    return some n
  if let some arg := parseNegArg? e then
    return (← parseRatScalar? arg).map (fun q => -q)
  let (fn, args) := e.getAppFnArgs
  if fn == ``Rat.cast && args.size >= 1 then
    return ← parseRatScalar? args[args.size - 1]!
  if (fn == ``HAdd.hAdd || fn == ``Add.add) && args.size >= 2 then
    match (← parseRatScalar? args[args.size - 2]!), (← parseRatScalar? args[args.size - 1]!) with
    | some a, some b => return some (a + b)
    | _, _ => return none
  if (fn == ``HSub.hSub || fn == ``Sub.sub) && args.size >= 2 then
    match (← parseRatScalar? args[args.size - 2]!), (← parseRatScalar? args[args.size - 1]!) with
    | some a, some b => return some (a - b)
    | _, _ => return none
  if (fn == ``HMul.hMul || fn == ``Mul.mul) && args.size >= 2 then
    match (← parseRatScalar? args[args.size - 2]!), (← parseRatScalar? args[args.size - 1]!) with
    | some a, some b => return some (a * b)
    | _, _ => return none
  if (fn == ``HDiv.hDiv || fn == ``Div.div) && args.size >= 2 then
    match (← parseRatScalar? args[args.size - 2]!), (← parseRatScalar? args[args.size - 1]!) with
    | some a, some b => if b == 0 then return none else return some (a / b)
    | _, _ => return none
  return none

private def evalNatExpr? (e : Expr) : MetaM (Option Nat) := do
  return e.cleanupAnnotations.numeral?

private def parsePowArgs? (e : Expr) : MetaM (Option (Expr × Nat)) := do
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  match fn, args with
  | ``HPow.hPow, #[_, _, _, _, base, exp] =>
      return (← evalNatExpr? exp).map (fun m => (base, m))
  | ``Pow.pow, #[_, _, base, exp] =>
      return (← evalNatExpr? exp).map (fun m => (base, m))
  | _, _ => return none

private inductive QexpExpr where
  | gen (spec : GeneratorSpec) (expr : Expr)
  | add (expr : Expr) (lhs rhs : QexpExpr)
  | neg (expr : Expr) (arg : QexpExpr)
  | sub (expr : Expr) (lhs rhs : QexpExpr)
  | mul (expr : Expr) (lhs rhs : QexpExpr)
  | pow (expr : Expr) (base : QexpExpr) (k : Nat)
  | inv (expr : Expr) (base : QexpExpr)
  | smul (expr : Expr) (c : Rat) (base : QexpExpr)
  | shift (expr : Expr) (base : QexpExpr) (offset : Nat)

private def QexpExpr.expr : QexpExpr → Expr
  | .gen _ e => e
  | .add e _ _ => e
  | .neg e _ => e
  | .sub e _ _ => e
  | .mul e _ _ => e
  | .pow e _ _ => e
  | .inv e _ => e
  | .smul e _ _ => e
  | .shift e _ _ => e

private def QexpExpr.withExpr (newExpr : Expr) : QexpExpr → QexpExpr
  | .gen spec _ => .gen spec newExpr
  | .add _ lhs rhs => .add newExpr lhs rhs
  | .neg _ arg => .neg newExpr arg
  | .sub _ lhs rhs => .sub newExpr lhs rhs
  | .mul _ lhs rhs => .mul newExpr lhs rhs
  | .pow _ base k => .pow newExpr base k
  | .inv _ base => .inv newExpr base
  | .smul _ c base => .smul newExpr c base
  | .shift _ base offset => .shift newExpr base offset

private def parseShiftIndex? (idx var : Expr) : MetaM (Option Nat) := do
  if (← isDefEq idx var) then
    return some 0
  if let some (lhs, rhs) := parseAddArgs? idx then
    if (← isDefEq lhs var) then
      return ← evalNatExpr? rhs
    if (← isDefEq rhs var) then
      return ← evalNatExpr? lhs
  return none

private partial def parseQexpExpr? (e : Expr) : MetaM (Option QexpExpr) := do
  let e := e.cleanupAnnotations
  match e.getAppFn with
  | .const nm _ =>
      if let some spec := findGeneratorSpecBySuffix? nm then
        return some (.gen spec e)
  | _ => pure ()
  let (fn, args) := e.getAppFnArgs
  if fn == ``PowerSeries.mk && args.size >= 1 then
    match args[args.size - 1]! with
    | .lam name type body _ =>
        let parsed? ← withLocalDeclD name type fun m => do
          let body := body.instantiate1 m
          let some (idx, base) := parseCoeffExpr? body | return none
          let some offset ← parseShiftIndex? idx m | return none
          let some base' ← parseQexpExpr? base | return none
          return some (.shift e base' offset)
        if let some parsed := parsed? then
          return some parsed
    | _ => pure ()
  if let some (lhs, rhs) := parseAddArgs? e then
    if let some lhs' ← parseQexpExpr? lhs then
      if let some rhs' ← parseQexpExpr? rhs then
        return some (.add e lhs' rhs')
  if let some arg := parseNegArg? e then
    if let some arg' ← parseQexpExpr? arg then
      return some (.neg e arg')
  if let some (lhs, rhs) := parseSubArgs? e then
    if let some lhs' ← parseQexpExpr? lhs then
      if let some rhs' ← parseQexpExpr? rhs then
        return some (.sub e lhs' rhs')
  if let some (lhs, rhs) := parseMulArgs? e then
    if let some lhs' ← parseQexpExpr? lhs then
      if let some rhs' ← parseQexpExpr? rhs then
        return some (.mul e lhs' rhs')
  if let some (c, base) := parseSmulArgs? e then
    if let some c' ← parseRatScalar? c then
      if let some base' ← parseQexpExpr? base then
        return some (.smul e c' base')
  if let some (base, k) ← parsePowArgs? e then
    if let some base' ← parseQexpExpr? base then
      return some (.pow e base' k)
  if let some base := parseInvArg? e then
    if let some base' ← parseQexpExpr? base then
      return some (.inv e base')
  let eWhnf ← withTransparency .reducible <| whnf e
  if eWhnf != e then
    if let some parsed ← parseQexpExpr? eWhnf then
      return some (parsed.withExpr e)
  return none

private def mkCoeffArray (nMax : Nat) (f : Nat → Rat) : Array Rat :=
  Id.run do
    let mut arr : Array Rat := #[]
    for n in [0:nMax+1] do
      arr := arr.push (f n)
    return arr

private def convAt (a b : Array Rat) (n : Nat) : Rat :=
  Id.run do
    let mut s : Rat := 0
    for i in [0:n+1] do
      s := s + a[i]! * b[n - i]!
    return s

private def convArray (nMax : Nat) (a b : Array Rat) : Array Rat :=
  mkCoeffArray nMax (fun n => convAt a b n)

private def powArray (nMax : Nat) (a : Array Rat) (k : Nat) : Array Rat :=
  Id.run do
    let one := mkCoeffArray nMax (fun n => if n == 0 then 1 else 0)
    let mut acc := one
    for _ in [0:k] do
      acc := convArray nMax acc a
    return acc

private def invArray (nMax : Nat) (a : Array Rat) : Array Rat :=
  Id.run do
    let a0 := a[0]!
    let invA0 := 1 / a0
    let mut inv : Array Rat := #[]
    for k in [0:nMax+1] do
      if k == 0 then
        inv := inv.push invA0
      else
        let mut s : Rat := 0
        for i in [1:k+1] do
          s := s + a[i]! * inv[k - i]!
        inv := inv.push (-invA0 * s)
    return inv

private partial def QexpExpr.coeffs (e : QexpExpr) (nMax : Nat) : Array Rat :=
  match e with
  | .gen spec _ => mkCoeffArray nMax spec.coeffRat
  | .add _ lhs rhs =>
      let l := lhs.coeffs nMax
      let r := rhs.coeffs nMax
      mkCoeffArray nMax (fun n => l[n]! + r[n]!)
  | .neg _ arg =>
      let a := arg.coeffs nMax
      mkCoeffArray nMax (fun n => -a[n]!)
  | .sub _ lhs rhs =>
      let l := lhs.coeffs nMax
      let r := rhs.coeffs nMax
      mkCoeffArray nMax (fun n => l[n]! - r[n]!)
  | .mul _ lhs rhs => convArray nMax (lhs.coeffs nMax) (rhs.coeffs nMax)
  | .pow _ base k => powArray nMax (base.coeffs nMax) k
  | .inv _ base => invArray nMax (base.coeffs nMax)
  | .smul _ c base =>
      let a := base.coeffs nMax
      mkCoeffArray nMax (fun n => c * a[n]!)
  | .shift _ base offset =>
      let a := base.coeffs (nMax + offset)
      mkCoeffArray nMax (fun n => a[n + offset]!)

private partial def QexpExpr.generatorExprs (e : QexpExpr) : Array Expr :=
  match e with
  | .gen _ expr => #[expr]
  | .add _ lhs rhs => lhs.generatorExprs ++ rhs.generatorExprs
  | .neg _ arg => arg.generatorExprs
  | .sub _ lhs rhs => lhs.generatorExprs ++ rhs.generatorExprs
  | .mul _ lhs rhs => lhs.generatorExprs ++ rhs.generatorExprs
  | .pow _ base _ => base.generatorExprs
  | .inv _ base => base.generatorExprs
  | .smul _ _ base => base.generatorExprs
  | .shift _ base _ => base.generatorExprs

private partial def QexpExpr.generatorSpecs (e : QexpExpr) : Array GeneratorSpec :=
  match e with
  | .gen spec _ => #[spec]
  | .add _ lhs rhs => lhs.generatorSpecs ++ rhs.generatorSpecs
  | .neg _ arg => arg.generatorSpecs
  | .sub _ lhs rhs => lhs.generatorSpecs ++ rhs.generatorSpecs
  | .mul _ lhs rhs => lhs.generatorSpecs ++ rhs.generatorSpecs
  | .pow _ base _ => base.generatorSpecs
  | .inv _ base => base.generatorSpecs
  | .smul _ _ base => base.generatorSpecs
  | .shift _ base _ => base.generatorSpecs

private def QexpExpr.generatorSimpNames (e : QexpExpr) : Array Name :=
  e.generatorSpecs.foldl (fun acc spec => acc ++ spec.simpNames) #[]

private partial def QexpExpr.hasInv : QexpExpr → Bool
  | .gen .. => false
  | .add _ lhs rhs => lhs.hasInv || rhs.hasInv
  | .neg _ arg => arg.hasInv
  | .sub _ lhs rhs => lhs.hasInv || rhs.hasInv
  | .mul _ lhs rhs => lhs.hasInv || rhs.hasInv
  | .pow _ base _ => base.hasInv
  | .inv .. => true
  | .smul _ _ base => base.hasInv
  | .shift _ base _ => base.hasInv

private def QexpExpr.needsNoInvFacts : QexpExpr → Bool
  | .mul _ lhs rhs => lhs.hasInv || rhs.hasInv
  | _ => false

private def exprTerm (e : Expr) : TacticM (TSyntax `term) := do
  let stx ← PrettyPrinter.delab e
  return ⟨stx⟩

private def complexRatTerm (q : Rat) : TacticM (TSyntax `term) := do
  let qStx ← PrettyPrinter.delab (Lean.toExpr q)
  `((($qStx : ℚ) : ℂ))

private def asSimpLemma (t : TSyntax `term) :
    TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
  `(Lean.Parser.Tactic.simpLemma| $(t):term)

private def asRwRule (t : TSyntax `term) :
    TacticM (TSyntax `Lean.Parser.Tactic.rwRule) :=
  `(Lean.Parser.Tactic.rwRule| $(t):term)

private def nameSimpLemma (n : Name) :
    TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
  asSimpLemma (⟨mkIdent n⟩ : TSyntax `term)

private def evalIfGoals (stx : TSyntax `tactic) : TacticM Unit := do
  unless (← getGoals).isEmpty do
    evalTactic stx

private def withStage {α : Type} (label : String) (act : TacticM α) : TacticM α := do
  try
    act
  catch ex =>
    throwError m!"qexp_coeffs: stage {label} failed\n{ex.toMessageData}"

private def exprSimpLemma (e : Expr) :
    TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) := do
  asSimpLemma (← exprTerm e)

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

private def indexedTerms (stem : String) (stop : Nat) : Array (TSyntax `term) :=
  Id.run do
    let mut terms := #[]
    for k in [0:stop] do
      terms := terms.push (indexedTerm stem k)
    return terms

private def indexedRwRules (stem : String) (stop : Nat) :
    TacticM (Array (TSyntax `Lean.Parser.Tactic.rwRule)) := do
  let mut rules := #[]
  for k in [0:stop] do
    rules := rules.push (← asRwRule (indexedTerm stem k))
  return rules

private def proveDirectCoeffFact (stem : String) (expr : Expr) (qexp : QexpExpr)
    (k : Nat) (v : Rat) : TacticM Unit := do
  let h := indexedIdent stem k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let exprStx ← exprTerm expr
  let vStx ← complexRatTerm v
  let genSimp ← qexp.generatorExprs.mapM exprSimpLemma
  let extraSimp ← qexp.generatorSimpNames.mapM nameSimpLemma
  let allSimp := genSimp ++ extraSimp
  evalTactic (← `(tactic|
    have $h : PowerSeries.coeff $kStx $exprStx = $vStx := by
      set_option linter.unusedSimpArgs false in
        simp [pow_succ, PowerSeries.coeff_mk, PowerSeries.coeff_mul, PowerSeries.coeff_smul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          $[$allSimp],*]
      all_goals ring_nf))

private def emitDirectCoeffFacts (stem : String) (qexp : QexpExpr) (n : Nat) : TacticM Unit := do
  let coeffs := qexp.coeffs n
  for k in [0:n+1] do
    proveDirectCoeffFact stem qexp.expr qexp k coeffs[k]!

private partial def emitMaximalNoInvFacts (stem : String) (qexp : QexpExpr) (n : Nat) :
    TacticM (Array (TSyntax `term)) := do
  if !qexp.hasInv then
    match qexp with
    | .gen .. => return #[]
    | _ =>
        emitDirectCoeffFacts stem qexp n
        return indexedTerms stem (n + 1)
  else
    match qexp with
    | .gen .. => return #[]
    | .add _ lhs rhs | .sub _ lhs rhs | .mul _ lhs rhs =>
        return (← emitMaximalNoInvFacts (stem ++ "L") lhs n) ++
          (← emitMaximalNoInvFacts (stem ++ "R") rhs n)
    | .neg _ arg | .pow _ arg _ | .smul _ _ arg | .shift _ arg _ =>
        emitMaximalNoInvFacts (stem ++ "A") arg n
    | .inv .. => return #[]

private def emitInvFactsForNode (stem : String) (expr : Expr) (base : QexpExpr)
    (n : Nat) : TacticM (Array (TSyntax `term)) := do
  let baseStem := stem ++ "Base"
  emitDirectCoeffFacts baseStem base n
  let baseTerm ← exprTerm base.expr
  let hConst := mkIdent (Name.mkSimple (stem ++ "Const"))
  let base0 ← complexRatTerm ((base.coeffs 0)[0]!)
  let hBase0 := indexedTerm baseStem 0
  evalTactic (← `(tactic|
    have $hConst : PowerSeries.constantCoeff $baseTerm = $base0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply $baseTerm]
      exact $hBase0))
  let invCoeffs := (QexpExpr.inv expr base).coeffs n
  for k in [0:n+1] do
    let hInv := indexedIdent stem k
    let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
    let vStx ← complexRatTerm invCoeffs[k]!
    let baseRules ← indexedRwRules baseStem (k + 1)
    let invRules ← indexedRwRules stem k
    let hConstRule ← asRwRule (⟨hConst.raw⟩ : TSyntax `term)
    evalTactic (← `(tactic|
      have $hInv : PowerSeries.coeff $kStx (($baseTerm)⁻¹) = $vStx := by
        rw [PowerSeries.coeff_inv]
        simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
        rw [$hConstRule]
        try rw [$[$baseRules],*, $[$invRules],*]
        all_goals norm_num))
  return indexedTerms stem (n + 1)

private partial def emitInvFacts (stem : String) (qexp : QexpExpr) (n : Nat) :
    TacticM (Array (TSyntax `term)) := do
  match qexp with
  | .gen .. => return #[]
  | .add _ lhs rhs | .sub _ lhs rhs | .mul _ lhs rhs =>
      return (← emitInvFacts (stem ++ "L") lhs n) ++ (← emitInvFacts (stem ++ "R") rhs n)
  | .neg _ arg | .pow _ arg _ | .smul _ _ arg =>
      emitInvFacts (stem ++ "A") arg n
  | .shift _ arg offset =>
      emitInvFacts (stem ++ "S") arg (n + offset)
  | .inv expr base =>
      let child ← emitInvFacts (stem ++ "B") base n
      let here ← emitInvFactsForNode (stem ++ "I") expr base n
      return child ++ here

private def runQexpCoeffsCore : TacticM Unit := withMainContext do
  let target ← getMainTarget
  let some (isExists, parsed) ← parseCoeffTarget? target |
    throwError "qexp_coeffs: expected a coefficient goal with concrete numeral index."
  if isQjSeriesExpr parsed.seriesExpr then
    evalTactic (← `(tactic| j_coeffs))
    return
  let some qexp ← parseQexpExpr? parsed.seriesExpr |
    throwError "qexp_coeffs: unsupported q-expansion expression."
  let coeffs := qexp.coeffs parsed.n
  let valueRat := coeffs[parsed.n]!
  let witness ← complexRatTerm valueRat
  withTheReader Core.Context (fun ctx =>
      { ctx with maxHeartbeats := max ctx.maxHeartbeats 10000000000 }) do
    if isExists then
      withStage "refine witness" <| evalTactic (← `(tactic| refine ⟨$witness, ?_⟩))
    let genTerms ← qexp.generatorExprs.mapM exprTerm
    let extraSimp ← qexp.generatorSimpNames.mapM nameSimpLemma
    let noInvFacts ←
      if qexp.needsNoInvFacts then
        withStage "non-inverse coefficient facts" <| emitMaximalNoInvFacts "hQexpN" qexp parsed.n
      else
        pure #[]
    let invFacts ← withStage "inverse facts" <| emitInvFacts "hQexp" qexp parsed.n
    withStage "structural simp" <| evalTactic (← `(tactic|
      set_option linter.unusedSimpArgs false in
        try simp only [map_add, map_sub, map_neg, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
          PowerSeries.coeff_smul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.sum_range_succ, Nat.reduceAdd, Nat.reduceSub]))
    for invFact in invFacts do
      let invLemma ← asSimpLemma invFact
      withStage "inverse rewrite" <| evalIfGoals (← `(tactic| try simp only [$invLemma]))
    for noInvFact in noInvFacts do
      let noInvLemma ← asSimpLemma noInvFact
      withStage "non-inverse rewrite" <| evalIfGoals (← `(tactic| try simp only [$noInvLemma]))
    for genTerm in genTerms do
      let genLemma ← asSimpLemma genTerm
      withStage "generator unfold" <| evalIfGoals (← `(tactic| try simp only [$genLemma]))
    withStage "final simp" <| evalIfGoals (← `(tactic|
      set_option linter.unusedSimpArgs false in
        try simp [pow_succ, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
          PowerSeries.coeff_smul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_filter,
          Finset.sum_Ico_eq_sub, Finset.sum_range_succ, $[$extraSimp],*]))
    withStage "ring_nf" <| evalIfGoals (← `(tactic| all_goals ring_nf))
  logInfo m!"[qexp_coeffs] computed result: {valueRat}"

private def withElapsedLog (label : String) (act : TacticM Unit) : TacticM Unit := do
  let start ← IO.monoMsNow
  try
    act
    let stop ← IO.monoMsNow
    logInfo m!"[{label}] elapsed: {stop - start}ms"
  catch ex =>
    let stop ← IO.monoMsNow
    logInfo m!"[{label}] failed after: {stop - start}ms\n{ex.toMessageData}"
    throw ex

syntax (name := qexpCoeffs) "qexp_coeffs" : tactic

elab_rules : tactic
  | `(tactic| qexp_coeffs) => withElapsedLog "qexp_coeffs" runQexpCoeffsCore

end Tactics
end XYin
