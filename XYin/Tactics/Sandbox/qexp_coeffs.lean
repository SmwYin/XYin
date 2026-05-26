import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Ring.RingNF

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

private partial def emitTruncatedCoeffFacts (stem : String) (qexp : QexpExpr) (n : Nat) :
    TacticM (Array (TSyntax `term)) := do
  if !qexp.hasInv then
    emitDirectCoeffFacts stem qexp n
    return indexedTerms stem (n + 1)
  else
    match qexp with
    | .gen .. => return #[]
    | .add _ lhs rhs | .sub _ lhs rhs | .mul _ lhs rhs =>
        return (← emitTruncatedCoeffFacts (stem ++ "L") lhs n) ++
          (← emitTruncatedCoeffFacts (stem ++ "R") rhs n)
    | .neg _ arg | .pow _ arg _ | .smul _ _ arg | .shift _ arg _ =>
        emitTruncatedCoeffFacts (stem ++ "A") arg n
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
  | .mul _ lhs rhs =>
      if (← isDefEq lhs.expr rhs.expr) then
        emitInvFacts (stem ++ "L") lhs n
      else
        return (← emitInvFacts (stem ++ "L") lhs n) ++ (← emitInvFacts (stem ++ "R") rhs n)
  | .add _ lhs rhs | .sub _ lhs rhs =>
      return (← emitInvFacts (stem ++ "L") lhs n) ++ (← emitInvFacts (stem ++ "R") rhs n)
  | .neg _ arg | .pow _ arg _ | .smul _ _ arg =>
      emitInvFacts (stem ++ "A") arg n
  | .shift _ arg offset =>
      emitInvFacts (stem ++ "S") arg (n + offset)
  | .inv expr base =>
      let child ← emitInvFacts (stem ++ "B") base n
      let here ← emitInvFactsForNode (stem ++ "I") expr base n
      return child ++ here

private def isConstWithSuffix (e : Expr) (suffix : String) : Bool :=
  match e.cleanupAnnotations.getAppFn with
  | .const n _ => n.toString.endsWith suffix
  | _ => false

private def QexpExpr.isGenTag (tag : GeneratorTag) : QexpExpr → Bool
  | .gen spec _ => spec.tag == tag
  | _ => false

private def QexpExpr.isE4Pow3 : QexpExpr → Bool
  | .pow _ base 3 => base.isGenTag .E4
  | _ => false

private def QexpExpr.isE4Pow2 : QexpExpr → Bool
  | .pow _ base 2 => base.isGenTag .E4
  | _ => false

private def QexpExpr.isE6 : QexpExpr → Bool :=
  QexpExpr.isGenTag .E6

private def QexpExpr.isE4SqMulE6 : QexpExpr → Bool
  | .mul _ lhs rhs => lhs.isE4Pow2 && rhs.isE6
  | _ => false

private def QexpExpr.isE4SqAddE6 : QexpExpr → Bool
  | .add _ lhs rhs => lhs.isE4Pow2 && rhs.isE6
  | _ => false

private def QexpExpr.isE4SqSubE6 : QexpExpr → Bool
  | .sub _ lhs rhs => lhs.isE4Pow2 && rhs.isE6
  | _ => false

private def QexpExpr.isE4AddE6 : QexpExpr → Bool
  | .add _ lhs rhs => lhs.isGenTag .E4 && rhs.isE6
  | _ => false

private def QexpExpr.isE4MulE6 : QexpExpr → Bool
  | .mul _ lhs rhs => lhs.isGenTag .E4 && rhs.isE6
  | _ => false

private def QexpExpr.isE6Pow2 : QexpExpr → Bool
  | .pow _ base 2 => base.isE6
  | _ => false

private def QexpExpr.isThreeSmulE4MulE6 : QexpExpr → Bool
  | .smul _ c base => c == 3 && base.isE4MulE6
  | _ => false

private def QexpExpr.isThreeE4E6SubE6Sq : QexpExpr → Bool
  | .sub _ lhs rhs => lhs.isThreeSmulE4MulE6 && rhs.isE6Pow2
  | _ => false

private def QexpExpr.isDeltaOverQ : QexpExpr → Bool
  | .shift expr _ 1 => isConstWithSuffix expr "Deltaoverq_qexpansion"
  | _ => false

private def QexpExpr.isDeltaShift2 : QexpExpr → Bool
  | .shift expr _ 2 => isConstWithSuffix expr "DeltaShift2_qexpansion"
  | _ => false

private def QexpExpr.isInvDeltaOverQ : QexpExpr → Bool
  | .inv _ base => base.isDeltaOverQ
  | _ => false

private def QexpExpr.isInvE4 : QexpExpr → Bool
  | .inv _ base => base.isGenTag .E4
  | _ => false

private def QexpExpr.isInvE6 : QexpExpr → Bool
  | .inv _ base => base.isGenTag .E6
  | _ => false

private def QexpExpr.isInvE4Sq : QexpExpr → Bool
  | .inv _ base => base.isE4Pow2
  | _ => false

private def QexpExpr.isStandardQjProduct : QexpExpr → Bool
  | .mul _ lhs rhs => lhs.isE4Pow3 && rhs.isInvDeltaOverQ
  | _ => false

private inductive StandardFastKind where
  | e4SqAddE6
  | threeE4E6SubE6Sq
  | e4SqSubE6MulE4AddE6
  | e4InvE6
  | e4SqAddE6InvE4
  | e4SqAddE6InvE4Sq
  | e4CubeInvDelta
  | e4SqE6InvDelta
  | invDeltaSquared
  | deltaShift2InvE6

private def QexpExpr.standardFastKind? : QexpExpr → Option StandardFastKind
  | q@(.add ..) =>
      if q.isE4SqAddE6 then some .e4SqAddE6 else none
  | q@(.sub ..) =>
      if q.isThreeE4E6SubE6Sq then some .threeE4E6SubE6Sq else none
  | .mul _ lhs rhs =>
      if lhs.isE4SqSubE6 && rhs.isE4AddE6 then
        some .e4SqSubE6MulE4AddE6
      else if lhs.isGenTag .E4 && rhs.isInvE6 then
        some .e4InvE6
      else if lhs.isE4SqAddE6 && rhs.isInvE4 then
        some .e4SqAddE6InvE4
      else if lhs.isE4SqAddE6 && rhs.isInvE4Sq then
        some .e4SqAddE6InvE4Sq
      else if lhs.isE4Pow3 && rhs.isInvDeltaOverQ then
        some .e4CubeInvDelta
      else if lhs.isE4SqMulE6 && rhs.isInvDeltaOverQ then
        some .e4SqE6InvDelta
      else if lhs.isInvDeltaOverQ && rhs.isInvDeltaOverQ then
        some .invDeltaSquared
      else if lhs.isDeltaShift2 && rhs.isInvE6 then
        some .deltaShift2InvE6
      else
        none
  | _ => none

private structure StandardQexpData where
  e4 : Array Rat
  e6 : Array Rat
  e4Squared : Array Rat
  e4Cubed : Array Rat
  e4E6 : Array Rat
  e4SquaredE6 : Array Rat
  e4SquaredPlusE6 : Array Rat
  e4SquaredMinusE6 : Array Rat
  e4PlusE6 : Array Rat
  threeE4E6MinusE6Squared : Array Rat
  e6Squared : Array Rat
  deltaOverQ : Array Rat
  deltaShift2 : Array Rat
  invE4 : Array Rat
  invE4Squared : Array Rat
  invE6 : Array Rat
  invDeltaOverQ : Array Rat
  qj : Array Rat

private def computeStandardQjData (n : Nat) : StandardQexpData :=
  Id.run do
    let nMax := n + 2
    let e4 := mkCoeffArray nMax e4CoeffRat
    let e6 := mkCoeffArray nMax e6CoeffRat
    let e4Sq := convArray nMax e4 e4
    let e4Cu := convArray nMax e4Sq e4
    let e4E6 := convArray n e4 e6
    let e4SqE6 := convArray n e4Sq e6
    let e4SqPlusE6 := mkCoeffArray n (fun k => e4Sq[k]! + e6[k]!)
    let e4SqMinusE6 := mkCoeffArray n (fun k => e4Sq[k]! - e6[k]!)
    let e4PlusE6 := mkCoeffArray n (fun k => e4[k]! + e6[k]!)
    let e6Sq := convArray nMax e6 e6
    let threeE4E6MinusE6Sq := mkCoeffArray n (fun k => 3 * e4E6[k]! - e6Sq[k]!)
    let delta := mkCoeffArray nMax (fun k => (e4Cu[k]! - e6Sq[k]!) / 1728)
    let deltaOverQ := mkCoeffArray n (fun k => delta[k + 1]!)
    let deltaShift2 := mkCoeffArray n (fun k => delta[k + 2]!)
    let invE4 := invArray n e4
    let invE4Sq := invArray n e4Sq
    let invE6 := invArray n e6
    let invDeltaOverQ := invArray n deltaOverQ
    let qj := convArray n e4Cu invDeltaOverQ
    return {
      e4 := e4
      e6 := e6
      e4Squared := e4Sq
      e4Cubed := e4Cu
      e4E6 := e4E6
      e4SquaredE6 := e4SqE6
      e4SquaredPlusE6 := e4SqPlusE6
      e4SquaredMinusE6 := e4SqMinusE6
      e4PlusE6 := e4PlusE6
      threeE4E6MinusE6Squared := threeE4E6MinusE6Sq
      e6Squared := e6Sq
      deltaOverQ := deltaOverQ
      deltaShift2 := deltaShift2
      invE4 := invE4
      invE4Squared := invE4Sq
      invE6 := invE6
      invDeltaOverQ := invDeltaOverQ
      qj := qj
    }

private structure StandardQexpNames where
  e4 : TSyntax `term
  e6 : TSyntax `term
  delta : TSyntax `term
  deltaOverQ : TSyntax `term

private def mkStandardQexpNames : StandardQexpNames where
  e4 := ⟨mkIdent `E4q⟩
  e6 := ⟨mkIdent `E6q⟩
  delta := ⟨mkIdent `Delta_qexpansion⟩
  deltaOverQ := ⟨mkIdent `Deltaoverq_qexpansion⟩

private def addStandardE4Fact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let e4 := names.e4
  let e4S ← asSimpLemma e4
  let hE4 := indexedIdent "hStdE4" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  evalTactic (← `(tactic|
    have $hE4 : PowerSeries.coeff $kStx $e4 = $v := by
      simp [$e4S, PowerSeries.coeff_mk,
        ArithmeticFunction.sigma, Function.update, Nat.divisors,
        Finset.sum_filter, Finset.sum_Ico_eq_sub, Finset.sum_range_succ]
      all_goals norm_num))

private def addStandardE4Facts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+3] do
    addStandardE4Fact names k (← complexRatTerm data.e4[k]!)

private def addStandardE6Fact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let e6 := names.e6
  let e6S ← asSimpLemma e6
  let hE6 := indexedIdent "hStdE6" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  evalTactic (← `(tactic|
    have $hE6 : PowerSeries.coeff $kStx $e6 = $v := by
      simp [$e6S, PowerSeries.coeff_mk,
        ArithmeticFunction.sigma, Function.update, Nat.divisors,
        Finset.sum_filter, Finset.sum_Ico_eq_sub, Finset.sum_range_succ]
      all_goals norm_num))

private def addStandardE6Facts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+3] do
    addStandardE6Fact names k (← complexRatTerm data.e6[k]!)

private def addStandardE4SqFact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let e4 := names.e4
  let hE4Sq := indexedIdent "hStdE4Sq" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let e4Rules ← indexedRwRules "hStdE4" (k + 1)
  evalTactic (← `(tactic|
    have $hE4Sq : PowerSeries.coeff $kStx ($e4 ^ 2) = $v := by
      rw [pow_two]
      rw [PowerSeries.coeff_mul]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [$[$e4Rules],*]
      all_goals norm_num))

private def addStandardE4SqFacts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+3] do
    addStandardE4SqFact names k (← complexRatTerm data.e4Squared[k]!)

private def addStandardE4CubeFact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let e4 := names.e4
  let hE4Cube := indexedIdent "hStdE4Cube" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let e4SqRules ← indexedRwRules "hStdE4Sq" (k + 1)
  let e4Rules ← indexedRwRules "hStdE4" (k + 1)
  evalTactic (← `(tactic|
    have $hE4Cube : PowerSeries.coeff $kStx ($e4 ^ 3) = $v := by
      rw [show $e4 ^ 3 = $e4 ^ 2 * $e4 by ring]
      rw [PowerSeries.coeff_mul]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [$[$e4SqRules],*, $[$e4Rules],*]
      all_goals norm_num))

private def addStandardE4CubeFacts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+3] do
    addStandardE4CubeFact names k (← complexRatTerm data.e4Cubed[k]!)

private def addStandardE4SqE6Fact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let e4 := names.e4
  let e6 := names.e6
  let hE4SqE6 := indexedIdent "hStdE4SqE6" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let e4SqRules ← indexedRwRules "hStdE4Sq" (k + 1)
  let e6Rules ← indexedRwRules "hStdE6" (k + 1)
  evalTactic (← `(tactic|
    have $hE4SqE6 : PowerSeries.coeff $kStx (($e4 ^ 2) * $e6) = $v := by
      rw [PowerSeries.coeff_mul]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [$[$e4SqRules],*, $[$e6Rules],*]
      all_goals norm_num))

private def addStandardE4SqE6Facts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardE4SqE6Fact names k (← complexRatTerm data.e4SquaredE6[k]!)

private def addStandardE4SqPlusE6Fact (names : StandardQexpNames) (k : Nat)
    (v : TSyntax `term) : TacticM Unit := do
  let e4 := names.e4
  let e6 := names.e6
  let hE4SqPlusE6 := indexedIdent "hStdE4SqPlusE6" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let hE4Sq ← asRwRule (indexedTerm "hStdE4Sq" k)
  let hE6 ← asRwRule (indexedTerm "hStdE6" k)
  evalTactic (← `(tactic|
    have $hE4SqPlusE6 : PowerSeries.coeff $kStx ($e4 ^ 2 + $e6) = $v := by
      simp only [map_add]
      rw [$hE4Sq, $hE6]
      all_goals norm_num))

private def addStandardE4SqPlusE6Facts (names : StandardQexpNames)
    (data : StandardQexpData) (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardE4SqPlusE6Fact names k (← complexRatTerm data.e4SquaredPlusE6[k]!)

private def addStandardE4SqMinusE6Fact (names : StandardQexpNames) (k : Nat)
    (v : TSyntax `term) : TacticM Unit := do
  let e4 := names.e4
  let e6 := names.e6
  let hE4SqMinusE6 := indexedIdent "hStdE4SqMinusE6" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let hE4Sq ← asRwRule (indexedTerm "hStdE4Sq" k)
  let hE6 ← asRwRule (indexedTerm "hStdE6" k)
  evalTactic (← `(tactic|
    have $hE4SqMinusE6 : PowerSeries.coeff $kStx ($e4 ^ 2 - $e6) = $v := by
      simp only [map_sub]
      rw [$hE4Sq, $hE6]
      all_goals norm_num))

private def addStandardE4SqMinusE6Facts (names : StandardQexpNames)
    (data : StandardQexpData) (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardE4SqMinusE6Fact names k (← complexRatTerm data.e4SquaredMinusE6[k]!)

private def addStandardE4PlusE6Fact (names : StandardQexpNames) (k : Nat)
    (v : TSyntax `term) : TacticM Unit := do
  let e4 := names.e4
  let e6 := names.e6
  let hE4PlusE6 := indexedIdent "hStdE4PlusE6" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let hE4 ← asRwRule (indexedTerm "hStdE4" k)
  let hE6 ← asRwRule (indexedTerm "hStdE6" k)
  evalTactic (← `(tactic|
    have $hE4PlusE6 : PowerSeries.coeff $kStx ($e4 + $e6) = $v := by
      simp only [map_add]
      rw [$hE4, $hE6]
      all_goals norm_num))

private def addStandardE4PlusE6Facts (names : StandardQexpNames)
    (data : StandardQexpData) (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardE4PlusE6Fact names k (← complexRatTerm data.e4PlusE6[k]!)

private def addStandardE4E6Fact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let e4 := names.e4
  let e6 := names.e6
  let hE4E6 := indexedIdent "hStdE4E6" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let e4Rules ← indexedRwRules "hStdE4" (k + 1)
  let e6Rules ← indexedRwRules "hStdE6" (k + 1)
  evalTactic (← `(tactic|
    have $hE4E6 : PowerSeries.coeff $kStx ($e4 * $e6) = $v := by
      rw [PowerSeries.coeff_mul]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [$[$e4Rules],*, $[$e6Rules],*]
      all_goals norm_num))

private def addStandardE4E6Facts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardE4E6Fact names k (← complexRatTerm data.e4E6[k]!)

private def addStandardE6SqFact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let e6 := names.e6
  let hE6Sq := indexedIdent "hStdE6Sq" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let e6Rules ← indexedRwRules "hStdE6" (k + 1)
  evalTactic (← `(tactic|
    have $hE6Sq : PowerSeries.coeff $kStx ($e6 ^ 2) = $v := by
      rw [pow_two]
      rw [PowerSeries.coeff_mul]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [$[$e6Rules],*]
      all_goals norm_num))

private def addStandardE6SqFacts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+3] do
    addStandardE6SqFact names k (← complexRatTerm data.e6Squared[k]!)

private def addStandardThreeE4E6SubE6SqFact (names : StandardQexpNames) (k : Nat)
    (v : TSyntax `term) : TacticM Unit := do
  let e4 := names.e4
  let e6 := names.e6
  let hPoly := indexedIdent "hStdThreeE4E6SubE6Sq" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let hE4E6 ← asRwRule (indexedTerm "hStdE4E6" k)
  let hE6Sq ← asRwRule (indexedTerm "hStdE6Sq" k)
  evalTactic (← `(tactic|
    have $hPoly :
        PowerSeries.coeff $kStx ((3 : ℂ) • ($e4 * $e6) - $e6 ^ 2) = $v := by
      simp only [map_sub, PowerSeries.coeff_smul]
      rw [$hE4E6, $hE6Sq]
      all_goals norm_num))

private def addStandardThreeE4E6SubE6SqFacts (names : StandardQexpNames)
    (data : StandardQexpData) (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardThreeE4E6SubE6SqFact names k
      (← complexRatTerm data.threeE4E6MinusE6Squared[k]!)

private def addStandardDeltaFact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let deltaOverQ := names.deltaOverQ
  let delta := names.delta
  let deltaOverQS ← asSimpLemma deltaOverQ
  let deltaS ← asSimpLemma delta
  let hE4Cube ← asRwRule (indexedTerm "hStdE4Cube" (k + 1))
  let hE6Sq ← asRwRule (indexedTerm "hStdE6Sq" (k + 1))
  let hDelta := indexedIdent "hStdDelta" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  evalTactic (← `(tactic|
    have $hDelta : PowerSeries.coeff $kStx $deltaOverQ = $v := by
      simp [$deltaOverQS, $deltaS, PowerSeries.coeff_mk, PowerSeries.coeff_smul]
      rw [$hE4Cube, $hE6Sq]
      all_goals norm_num))

private def addStandardDeltaFacts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardDeltaFact names k (← complexRatTerm data.deltaOverQ[k]!)

private def addStandardDeltaShift2Fact (names : StandardQexpNames) (k : Nat)
    (v : TSyntax `term) : TacticM Unit := do
  let delta := names.delta
  let deltaShift2 := ⟨mkIdent `DeltaShift2_qexpansion⟩
  let deltaShift2S ← asSimpLemma deltaShift2
  let deltaS ← asSimpLemma delta
  let hE4Cube ← asRwRule (indexedTerm "hStdE4Cube" (k + 2))
  let hE6Sq ← asRwRule (indexedTerm "hStdE6Sq" (k + 2))
  let hDeltaShift2 := indexedIdent "hStdDeltaShift2" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  evalTactic (← `(tactic|
    have $hDeltaShift2 : PowerSeries.coeff $kStx $deltaShift2 = $v := by
      simp [$deltaShift2S, $deltaS, PowerSeries.coeff_mk, PowerSeries.coeff_smul]
      rw [$hE4Cube, $hE6Sq]
      all_goals norm_num))

private def addStandardDeltaShift2Facts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardDeltaShift2Fact names k (← complexRatTerm data.deltaShift2[k]!)

private def addStandardDeltaConstFact (names : StandardQexpNames) (data : StandardQexpData) :
    TacticM Unit := do
  let deltaOverQ := names.deltaOverQ
  let hDelta0 := indexedTerm "hStdDelta" 0
  let delta0 ← complexRatTerm data.deltaOverQ[0]!
  evalTactic (← `(tactic|
    have hStdDeltaConst : PowerSeries.constantCoeff $deltaOverQ = $delta0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply $deltaOverQ]
      exact $hDelta0))

private def addStandardE4ConstFact (names : StandardQexpNames) (data : StandardQexpData) :
    TacticM Unit := do
  let e4 := names.e4
  let hE40 := indexedTerm "hStdE4" 0
  let e40 ← complexRatTerm data.e4[0]!
  evalTactic (← `(tactic|
    have hStdE4Const : PowerSeries.constantCoeff $e4 = $e40 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply $e4]
      exact $hE40))

private def addStandardE6ConstFact (names : StandardQexpNames) (data : StandardQexpData) :
    TacticM Unit := do
  let e6 := names.e6
  let hE60 := indexedTerm "hStdE6" 0
  let e60 ← complexRatTerm data.e6[0]!
  evalTactic (← `(tactic|
    have hStdE6Const : PowerSeries.constantCoeff $e6 = $e60 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply $e6]
      exact $hE60))

private def addStandardE4SqConstFact (names : StandardQexpNames) (data : StandardQexpData) :
    TacticM Unit := do
  let e4 := names.e4
  let hE4Sq0 := indexedTerm "hStdE4Sq" 0
  let e4Sq0 ← complexRatTerm data.e4Squared[0]!
  evalTactic (← `(tactic|
    have hStdE4SqConst : PowerSeries.constantCoeff ($e4 ^ 2) = $e4Sq0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply ($e4 ^ 2)]
      exact $hE4Sq0))

private def addStandardInvE4Fact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let e4 := names.e4
  let hInv := indexedIdent "hStdInvE4" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let e4Rules ← indexedRwRules "hStdE4" (k + 1)
  let invRules ← indexedRwRules "hStdInvE4" k
  evalTactic (← `(tactic|
    have $hInv : PowerSeries.coeff $kStx (($e4)⁻¹) = $v := by
      rw [PowerSeries.coeff_inv]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [hStdE4Const]
      try rw [$[$e4Rules],*, $[$invRules],*]
      all_goals norm_num))

private def addStandardInvE4Facts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardInvE4Fact names k (← complexRatTerm data.invE4[k]!)

private def addStandardInvE4SqFact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let e4 := names.e4
  let hInv := indexedIdent "hStdInvE4Sq" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let e4SqRules ← indexedRwRules "hStdE4Sq" (k + 1)
  let invRules ← indexedRwRules "hStdInvE4Sq" k
  evalTactic (← `(tactic|
    have $hInv : PowerSeries.coeff $kStx (($e4 ^ 2)⁻¹) = $v := by
      rw [PowerSeries.coeff_inv]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [hStdE4SqConst]
      try rw [$[$e4SqRules],*, $[$invRules],*]
      all_goals norm_num))

private def addStandardInvE4SqFacts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardInvE4SqFact names k (← complexRatTerm data.invE4Squared[k]!)

private def addStandardInvE6Fact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let e6 := names.e6
  let hInv := indexedIdent "hStdInvE6" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let e6Rules ← indexedRwRules "hStdE6" (k + 1)
  let invRules ← indexedRwRules "hStdInvE6" k
  evalTactic (← `(tactic|
    have $hInv : PowerSeries.coeff $kStx (($e6)⁻¹) = $v := by
      rw [PowerSeries.coeff_inv]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [hStdE6Const]
      try rw [$[$e6Rules],*, $[$invRules],*]
      all_goals norm_num))

private def addStandardInvE6Facts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardInvE6Fact names k (← complexRatTerm data.invE6[k]!)

private def addStandardInvDeltaFact (names : StandardQexpNames) (k : Nat) (v : TSyntax `term) :
    TacticM Unit := do
  let deltaOverQ := names.deltaOverQ
  let hInv := indexedIdent "hStdInvDelta" k
  let kStx : TSyntax `num := ⟨Syntax.mkNatLit k⟩
  let deltaRules ← indexedRwRules "hStdDelta" (k + 1)
  let invRules ← indexedRwRules "hStdInvDelta" k
  evalTactic (← `(tactic|
    have $hInv : PowerSeries.coeff $kStx (($deltaOverQ)⁻¹) = $v := by
      rw [PowerSeries.coeff_inv]
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
      rw [hStdDeltaConst]
      try rw [$[$deltaRules],*, $[$invRules],*]
      all_goals norm_num))

private def addStandardInvDeltaFacts (names : StandardQexpNames) (data : StandardQexpData)
    (n : Nat) : TacticM Unit := do
  for k in [0:n+1] do
    addStandardInvDeltaFact names k (← complexRatTerm data.invDeltaOverQ[k]!)

private def finishStandardQjProductProof (n : Nat) : TacticM Unit := do
  let e4Facts ← indexedSimpLemmas "hStdE4Cube" (n + 1)
  let invFacts ← indexedSimpLemmas "hStdInvDelta" (n + 1)
  evalTactic (← `(tactic| rw [PowerSeries.coeff_mul]))
  evalTactic (← `(tactic| rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]))
  evalTactic (← `(tactic|
    simp only [Finset.sum_range_succ, $[$e4Facts],*, $[$invFacts],*]))
  evalTactic (← `(tactic| all_goals norm_num))

private def finishStandardE4SqSubE6MulE4AddE6Proof (n : Nat) : TacticM Unit := do
  let lhsFacts ← indexedSimpLemmas "hStdE4SqMinusE6" (n + 1)
  let rhsFacts ← indexedSimpLemmas "hStdE4PlusE6" (n + 1)
  evalTactic (← `(tactic| rw [PowerSeries.coeff_mul]))
  evalTactic (← `(tactic| rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]))
  evalTactic (← `(tactic| simp only [Finset.sum_range_succ, $[$lhsFacts],*, $[$rhsFacts],*]))
  evalTactic (← `(tactic| all_goals norm_num))

private def finishStandardExactFact (stem : String) (n : Nat) : TacticM Unit := do
  let h := indexedTerm stem n
  evalTactic (← `(tactic| simpa using $h))

private def finishStandardE4InvE6Proof (n : Nat) : TacticM Unit := do
  let e4Facts ← indexedSimpLemmas "hStdE4" (n + 1)
  let invFacts ← indexedSimpLemmas "hStdInvE6" (n + 1)
  evalTactic (← `(tactic| rw [PowerSeries.coeff_mul]))
  evalTactic (← `(tactic| rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]))
  evalTactic (← `(tactic| simp only [Finset.sum_range_succ, $[$e4Facts],*, $[$invFacts],*]))
  evalTactic (← `(tactic| all_goals norm_num))

private def finishStandardE4SqAddE6InvE4Proof (n : Nat) : TacticM Unit := do
  let numeratorFacts ← indexedSimpLemmas "hStdE4SqPlusE6" (n + 1)
  let invFacts ← indexedSimpLemmas "hStdInvE4" (n + 1)
  evalTactic (← `(tactic| rw [PowerSeries.coeff_mul]))
  evalTactic (← `(tactic| rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]))
  evalTactic (← `(tactic|
    simp only [Finset.sum_range_succ, $[$numeratorFacts],*, $[$invFacts],*]))
  evalTactic (← `(tactic| all_goals norm_num))

private def finishStandardE4SqAddE6InvE4SqProof (n : Nat) : TacticM Unit := do
  let numeratorFacts ← indexedSimpLemmas "hStdE4SqPlusE6" (n + 1)
  let invFacts ← indexedSimpLemmas "hStdInvE4Sq" (n + 1)
  evalTactic (← `(tactic| rw [PowerSeries.coeff_mul]))
  evalTactic (← `(tactic| rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]))
  evalTactic (← `(tactic|
    simp only [Finset.sum_range_succ, $[$numeratorFacts],*, $[$invFacts],*]))
  evalTactic (← `(tactic| all_goals norm_num))

private def finishStandardE4SqE6InvDeltaProof (n : Nat) : TacticM Unit := do
  let numeratorFacts ← indexedSimpLemmas "hStdE4SqE6" (n + 1)
  let invFacts ← indexedSimpLemmas "hStdInvDelta" (n + 1)
  evalTactic (← `(tactic| rw [PowerSeries.coeff_mul]))
  evalTactic (← `(tactic| rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]))
  evalTactic (← `(tactic|
    simp only [Finset.sum_range_succ, $[$numeratorFacts],*, $[$invFacts],*]))
  evalTactic (← `(tactic| all_goals norm_num))

private def finishStandardInvDeltaSquaredProof (n : Nat) : TacticM Unit := do
  let invFacts ← indexedSimpLemmas "hStdInvDelta" (n + 1)
  evalTactic (← `(tactic| rw [PowerSeries.coeff_mul]))
  evalTactic (← `(tactic| rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]))
  evalTactic (← `(tactic| simp only [Finset.sum_range_succ, $[$invFacts],*]))
  evalTactic (← `(tactic| all_goals norm_num))

private def finishStandardDeltaShift2InvE6Proof (n : Nat) : TacticM Unit := do
  let deltaFacts ← indexedSimpLemmas "hStdDeltaShift2" (n + 1)
  let invFacts ← indexedSimpLemmas "hStdInvE6" (n + 1)
  evalTactic (← `(tactic| rw [PowerSeries.coeff_mul]))
  evalTactic (← `(tactic| rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]))
  evalTactic (← `(tactic|
    simp only [Finset.sum_range_succ, $[$deltaFacts],*, $[$invFacts],*]))
  evalTactic (← `(tactic| all_goals norm_num))

private def StandardFastKind.needsDelta : StandardFastKind → Bool
  | .e4CubeInvDelta | .e4SqE6InvDelta | .invDeltaSquared | .deltaShift2InvE6 => true
  | _ => false

private def proveStandardFastProduct (kind : StandardFastKind) (n : Nat) : TacticM Unit := do
  let names := mkStandardQexpNames
  let data := computeStandardQjData n
  addStandardE4Facts names data n
  addStandardE6Facts names data n
  addStandardE4SqFacts names data n
  if kind.needsDelta then
    addStandardE4CubeFacts names data n
    addStandardE6SqFacts names data n
  match kind with
  | .threeE4E6SubE6Sq =>
      addStandardE4E6Facts names data n
      addStandardE6SqFacts names data n
      addStandardThreeE4E6SubE6SqFacts names data n
  | .e4SqSubE6MulE4AddE6 =>
      addStandardE4SqMinusE6Facts names data n
      addStandardE4PlusE6Facts names data n
  | .e4SqE6InvDelta => addStandardE4SqE6Facts names data n
  | .e4SqAddE6 | .e4SqAddE6InvE4 | .e4SqAddE6InvE4Sq =>
      addStandardE4SqPlusE6Facts names data n
  | _ => pure ()
  match kind with
  | .e4InvE6 | .deltaShift2InvE6 =>
      addStandardE6ConstFact names data
      addStandardInvE6Facts names data n
  | _ => pure ()
  match kind with
  | .e4SqAddE6InvE4 =>
      addStandardE4ConstFact names data
      addStandardInvE4Facts names data n
  | _ => pure ()
  match kind with
  | .e4SqAddE6InvE4Sq =>
      addStandardE4SqConstFact names data
      addStandardInvE4SqFacts names data n
  | _ => pure ()
  match kind with
  | .e4CubeInvDelta | .e4SqE6InvDelta | .invDeltaSquared =>
      addStandardDeltaFacts names data n
      addStandardDeltaConstFact names data
      addStandardInvDeltaFacts names data n
  | .deltaShift2InvE6 =>
      addStandardDeltaShift2Facts names data n
  | _ => pure ()
  match kind with
  | .e4SqAddE6 => finishStandardExactFact "hStdE4SqPlusE6" n
  | .threeE4E6SubE6Sq => finishStandardExactFact "hStdThreeE4E6SubE6Sq" n
  | .e4SqSubE6MulE4AddE6 => finishStandardE4SqSubE6MulE4AddE6Proof n
  | .e4InvE6 => finishStandardE4InvE6Proof n
  | .e4SqAddE6InvE4 => finishStandardE4SqAddE6InvE4Proof n
  | .e4SqAddE6InvE4Sq => finishStandardE4SqAddE6InvE4SqProof n
  | .e4CubeInvDelta => finishStandardQjProductProof n
  | .e4SqE6InvDelta => finishStandardE4SqE6InvDeltaProof n
  | .invDeltaSquared => finishStandardInvDeltaSquaredProof n
  | .deltaShift2InvE6 => finishStandardDeltaShift2InvE6Proof n

private def runQexpCoeffsCore : TacticM Unit := withMainContext do
  let target ← getMainTarget
  let some (isExists, parsed) ← parseCoeffTarget? target |
    throwError "qexp_coeffs: expected a coefficient goal with concrete numeral index."
  let workSeriesExpr ← withTransparency .reducible <| whnf parsed.seriesExpr
  let some qexp ← parseQexpExpr? workSeriesExpr |
    throwError "qexp_coeffs: unsupported q-expansion expression."
  let coeffs := qexp.coeffs parsed.n
  let valueRat := coeffs[parsed.n]!
  let witness ← complexRatTerm valueRat
  withTheReader Core.Context (fun ctx =>
      { ctx with maxHeartbeats := max ctx.maxHeartbeats 10000000000 }) do
    if isExists then
      let nStx : TSyntax `num := ⟨Syntax.mkNatLit parsed.n⟩
      let workSeriesTerm ← exprTerm workSeriesExpr
      withStage "refine witness" <| evalTactic (← `(tactic| refine ⟨$witness, ?_⟩))
      withStage "change reducible series" <| evalTactic (← `(tactic|
        change PowerSeries.coeff $nStx $workSeriesTerm = $witness))
    if let some kind := qexp.standardFastKind? then
      withStage "standard q-expansion product fast path" <| proveStandardFastProduct kind parsed.n
      return
    if !qexp.hasInv then
      try
        withStage "direct coefficient fast path" <| do
          proveDirectCoeffFact "hQexpDirect" qexp.expr qexp parsed.n valueRat
          let hDirect := indexedTerm "hQexpDirect" parsed.n
          evalTactic (← `(tactic| simpa using $hDirect))
        return
      catch _ =>
        pure ()
    let genTerms ← qexp.generatorExprs.mapM exprTerm
    let extraSimp ← qexp.generatorSimpNames.mapM nameSimpLemma
    let noInvFacts ←
      if qexp.needsNoInvFacts then
        withStage "truncated coefficient facts" <| emitTruncatedCoeffFacts "hQexpN" qexp parsed.n
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
      withStage "truncated coefficient rewrite" <|
        evalIfGoals (← `(tactic| try simp only [$noInvLemma]))
    if qexp.hasInv then
      withStage "truncated norm_num close" <|
        evalIfGoals (← `(tactic| try norm_num))
      if (← getGoals).isEmpty then
        return
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
