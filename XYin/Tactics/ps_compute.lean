import Mathlib

set_option linter.style.nativeDecide false

open Lean Elab Tactic Meta

namespace XYin.Tactics

private structure ParsedCoeff where
  ringExpr : Expr
  kExpr : Expr
  seriesExpr : Expr
  coeffExpr : Expr

private structure ParsedTarget where
  lhs : Expr
  rhs : Expr
  coeffOnLeft : Bool
  coeff : ParsedCoeff

private structure ParsedTrunc where
  ringExpr : Expr
  nExpr : Expr
  seriesExpr : Expr
  truncExpr : Expr

private structure CoeffKey where
  seriesExpr : Expr
  indexExpr : Expr

private inductive KnownCoeffSource where
  | point
  | forallEq
  | trunc

private structure KnownCoeff where
  key : CoeffKey
  valueExpr : Expr
  proofExpr : Expr
  sourceFVarId : FVarId
  source : KnownCoeffSource

private structure ForallCoeffEntry where
  seriesExpr : Expr
  valueFnExpr : Expr
  proofExpr : Expr
  sourceFVarId : FVarId
  reversed : Bool

private structure TruncCoeffEntry where
  ringExpr : Expr
  nExpr : Expr
  seriesExpr : Expr
  polyExpr : Expr
  proofExpr : Expr
  sourceFVarId : FVarId

private structure CoeffDb where
  points : Array KnownCoeff
  foralls : Array ForallCoeffEntry
  truncs : Array TruncCoeffEntry

private structure LookupReport where
  key : CoeffKey
  hits : Array KnownCoeff

private def sourceDesc : KnownCoeffSource → String
  | .point => "point"
  | .forallEq => "forall"
  | .trunc => "trunc"

private structure ComputeResult where
  valueExpr : Option Expr
  proofExpr : Option Expr
  needed : Array CoeffKey
  used : Array KnownCoeff
  missing : Array CoeffKey
  unsupported : Array Expr

private structure CachedCoeff where
  key : CoeffKey
  result : ComputeResult

initialize psComputeCache : IO.Ref (Array CachedCoeff) ← IO.mkRef #[]

private structure NormalizedCompute where
  proofLhs : Expr
  computedValue : Expr
  normalizedValue : Expr
  coeffProof : Expr

private inductive SeriesClass where
  | mk
  | C
  | X
  | zero
  | one
  | numeral (n : Nat)
  | XPow (m : Nat)
  | unsupported

private def ppExprStr (e : Expr) : MetaM String := do
  return toString (← ppExpr e)

private partial def catalanValue : Nat → Nat
  | 0 => 1
  | n + 1 => (List.range (n + 1)).foldl (fun acc i => acc + catalanValue i * catalanValue (n - i)) 0

private partial def largeSchroderValue : Nat → Nat
  | 0 => 1
  | n + 1 =>
      largeSchroderValue n +
        (List.range (n + 1)).foldl
          (fun acc i => acc + largeSchroderValue i * largeSchroderValue (n - i)) 0

private partial def evalNatExpr? (e : Expr) : MetaM (Option Nat) := do
  if let some n := e.cleanupAnnotations.numeral? then
    return some n
  let (fn, args) := e.cleanupAnnotations.getAppFnArgs
  match fn with
  | ``Nat.choose =>
      if args.size == 2 then
        match (← evalNatExpr? args[0]!), (← evalNatExpr? args[1]!) with
        | some n, some k => return some (Nat.choose n k)
        | _, _ => pure ()
  | ``catalan =>
      if args.size == 1 then
        if let some n ← evalNatExpr? args[0]! then
          return some (catalanValue n)
  | ``Nat.largeSchroder =>
      if args.size == 1 then
        if let some n ← evalNatExpr? args[0]! then
          return some (largeSchroderValue n)
  | _ => pure ()
  match (← (Lean.Meta.evalNat e).run) with
  | some n => return some n
  | none =>
      try
        let r ← withTransparency .default <| reduce e
        match r.numeral? with
        | some n => return some n
        | none =>
            match r with
            | .lit (.natVal n) => return some n
            | _ => return none
      catch _ =>
        return none

private def natLitExpr? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ => none

private def ppComputedValueStr (e : Expr) : MetaM String := do
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  if fn == ``OfNat.ofNat && args.size >= 2 then
    if let some n := args[1]!.numeral? then
      return toString n
  if fn == ``Nat.cast && args.size == 3 then
    if let some n ← evalNatExpr? args[2]! then
      return toString n
  ppExprStr e

private def parseCoeffExpr? (e : Expr) : Option ParsedCoeff :=
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  match fn, args with
  | ``PowerSeries.coeff, _ =>
      if args.size >= 4 then
        let ringExpr := args[0]!
        let kExpr := args[2]!
        let seriesExpr := args[3]!
        some { ringExpr, kExpr, seriesExpr, coeffExpr := e }
      else
        none
  | ``DFunLike.coe, #[_, _, _, _, coeffPart, seriesExpr] =>
      let (cfn, cargs) := coeffPart.getAppFnArgs
      match cfn, cargs with
      | ``PowerSeries.coeff, #[ringExpr, _, kExpr] =>
          some { ringExpr, kExpr, seriesExpr, coeffExpr := e }
      | _, _ => none
  | _, _ => none

private def parseTruncExpr? (e : Expr) : Option ParsedTrunc :=
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  match fn, args with
  | ``DFunLike.coe, #[_, _, _, _, truncPart, seriesExpr] =>
      let (tfn, targs) := truncPart.getAppFnArgs
      match tfn, targs with
      | ``PowerSeries.trunc, #[ringExpr, _, nExpr] =>
          some { ringExpr, nExpr, seriesExpr, truncExpr := e }
      | _, _ => none
  | _, _ => none

private def changeCoeffToCForm (parsed : ParsedTarget) (n : Nat) : TacticM Unit :=
    withMainContext do
  let ringStx ← PrettyPrinter.delab parsed.coeff.ringExpr
  let kStx ← PrettyPrinter.delab parsed.coeff.kExpr
  let lhsStx ← PrettyPrinter.delab parsed.lhs
  let rhsStx ← PrettyPrinter.delab parsed.rhs
  let nStx : TSyntax `num := ⟨Syntax.mkNatLit n⟩
  if parsed.coeffOnLeft then
    evalTactic (← `(tactic|
      change PowerSeries.coeff (R := $ringStx) $kStx (PowerSeries.C (($nStx : Nat) : $ringStx)) =
        $rhsStx))
  else
    evalTactic (← `(tactic|
      change $lhsStx = PowerSeries.coeff (R := $ringStx) $kStx
        (PowerSeries.C (($nStx : Nat) : $ringStx))))

private def parseTarget? (target : Expr) : Option ParsedTarget :=
  match target.eq? with
  | none => none
  | some (_, lhs, rhs) =>
      match parseCoeffExpr? lhs, parseCoeffExpr? rhs with
      | some coeff, _ => some { lhs, rhs, coeffOnLeft := true, coeff }
      | _, some coeff => some { lhs, rhs, coeffOnLeft := false, coeff }
      | _, _ => none

private def targetKey (parsed : ParsedTarget) : CoeffKey :=
  { seriesExpr := parsed.coeff.seriesExpr, indexExpr := parsed.coeff.kExpr }

private def coeffKeyDefEq (k₁ k₂ : CoeffKey) : MetaM Bool := do
  return (← isDefEq k₁.seriesExpr k₂.seriesExpr) &&
    (← isDefEq k₁.indexExpr k₂.indexExpr)

private def parsePointCoeffFromEqHyp (h : Expr) (hTy : Expr) :
    TacticM (Array KnownCoeff) := withMainContext do
  let some sourceFVarId := h.fvarId? | return #[]
  let mut out : Array KnownCoeff := #[]
  if let some (_, lhs, rhs) := hTy.eq? then
    if let some pc := parseCoeffExpr? lhs then
      out := out.push {
        key := { seriesExpr := pc.seriesExpr, indexExpr := pc.kExpr }
        valueExpr := rhs
        proofExpr := h
        sourceFVarId := sourceFVarId
        source := .point
      }
    if let some pc := parseCoeffExpr? rhs then
      let hsymm ← mkAppM ``Eq.symm #[h]
      out := out.push {
        key := { seriesExpr := pc.seriesExpr, indexExpr := pc.kExpr }
        valueExpr := lhs
        proofExpr := hsymm
        sourceFVarId := sourceFVarId
        source := .point
      }
  return out

private def parseForallCoeffEntry? (h : Expr) (hTy : Expr) : TacticM (Option ForallCoeffEntry) :=
  withMainContext do
    let some sourceFVarId := h.fvarId? | return none
    match hTy.cleanupAnnotations with
    | .forallE n nTy body _ =>
        if !nTy.isConstOf ``Nat then
          return none
        withLocalDeclD n nTy fun nVar => do
          let bodyInst := body.instantiate1 nVar
          if let some (_, lhs, rhs) := bodyInst.eq? then
            if let some pc := parseCoeffExpr? lhs then
              if (← isDefEq pc.kExpr nVar) then
                let valueFnExpr ← mkLambdaFVars #[nVar] rhs
                let entry : ForallCoeffEntry := {
                  seriesExpr := pc.seriesExpr
                  valueFnExpr := valueFnExpr
                  proofExpr := h
                  sourceFVarId := sourceFVarId
                  reversed := false
                }
                return some entry
            if let some pc := parseCoeffExpr? rhs then
              if (← isDefEq pc.kExpr nVar) then
                let valueFnExpr ← mkLambdaFVars #[nVar] lhs
                let entry : ForallCoeffEntry := {
                  seriesExpr := pc.seriesExpr
                  valueFnExpr := valueFnExpr
                  proofExpr := h
                  sourceFVarId := sourceFVarId
                  reversed := true
                }
                return some entry
          return none
    | _ => return none

private def parseTruncCoeffEntry? (h : Expr) (hTy : Expr) : TacticM (Option TruncCoeffEntry) :=
  withMainContext do
    let some sourceFVarId := h.fvarId? | return none
    if let some (_, lhs, rhs) := hTy.eq? then
      if let some tr := parseTruncExpr? lhs then
        return some {
          ringExpr := tr.ringExpr
          nExpr := tr.nExpr
          seriesExpr := tr.seriesExpr
          polyExpr := rhs
          proofExpr := h
          sourceFVarId := sourceFVarId
        }
      if let some tr := parseTruncExpr? rhs then
        let hsymm ← mkAppM ``Eq.symm #[h]
        return some {
          ringExpr := tr.ringExpr
          nExpr := tr.nExpr
          seriesExpr := tr.seriesExpr
          polyExpr := lhs
          proofExpr := hsymm
          sourceFVarId := sourceFVarId
        }
    return none

private def buildCoeffDb : TacticM CoeffDb := withMainContext do
  let mut points : Array KnownCoeff := #[]
  let mut foralls : Array ForallCoeffEntry := #[]
  let mut truncs : Array TruncCoeffEntry := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then
      continue
    let h := mkFVar ldecl.fvarId
    let hTy ← inferType h
    points := points ++ (← parsePointCoeffFromEqHyp h hTy)
    if let some entry ← parseForallCoeffEntry? h hTy then
      foralls := foralls.push entry
    if let some entry ← parseTruncCoeffEntry? h hTy then
      truncs := truncs.push entry
  return { points, foralls, truncs }

private def fvarUserName (fid : FVarId) : TacticM Name := withMainContext do
  let ldecl ← fid.getDecl
  return ldecl.userName

private def mergeKeys (xs ys : Array CoeffKey) : Array CoeffKey :=
  xs ++ ys

private def mergeKnown (xs ys : Array KnownCoeff) : Array KnownCoeff :=
  xs ++ ys

private def mergeExprs (xs ys : Array Expr) : Array Expr :=
  xs ++ ys

private def mergeResultInfo (a b : ComputeResult) : ComputeResult := {
  valueExpr := none
  proofExpr := none
  needed := mergeKeys a.needed b.needed
  used := mergeKnown a.used b.used
  missing := mergeKeys a.missing b.missing
  unsupported := mergeExprs a.unsupported b.unsupported
}

private def successResult (valueExpr proofExpr : Expr) (needed : Array CoeffKey)
    (used : Array KnownCoeff) : ComputeResult := {
  valueExpr := some valueExpr
  proofExpr := some proofExpr
  needed
  used
  missing := #[]
  unsupported := #[]
}

private def failureResult (needed missing : Array CoeffKey) (unsupported : Array Expr)
    (used : Array KnownCoeff := #[]) : ComputeResult := {
  valueExpr := none
  proofExpr := none
  needed
  used
  missing
  unsupported
}

private def isSuccess (r : ComputeResult) : Bool :=
  r.valueExpr.isSome && r.proofExpr.isSome && r.missing.isEmpty && r.unsupported.isEmpty

private def resetComputeCache : TacticM Unit := do
  psComputeCache.set #[]

private def getCachedCoeff? (key : CoeffKey) : TacticM (Option ComputeResult) :=
    withMainContext do
  for entry in (← psComputeCache.get) do
    if (← coeffKeyDefEq entry.key key) then
      return some entry.result
  return none

private def cacheCoeff (key : CoeffKey) (r : ComputeResult) : TacticM Unit := do
  if isSuccess r then
    psComputeCache.modify fun xs => xs.push { key, result := r }

private def ringExprOfSeries? (seriesExpr : Expr) : MetaM (Option Expr) := do
  let ty ← whnf (← inferType seriesExpr)
  let ty := ty.cleanupAnnotations
  let (fn, args) := ty.getAppFnArgs
  if fn == ``PowerSeries && args.size == 1 then
    return some args[0]!
  if fn == ``MvPowerSeries && args.size == 2 then
    return some args[1]!
  match ty with
  | .forallE _ domain body _ =>
      withLocalDeclD `i domain fun i => do
        return some (← whnf (body.instantiate1 i))
  | _ => return none

private def mkCoeffMapExpr (ringExpr kExpr : Expr) : MetaM Expr :=
  mkAppOptM ``PowerSeries.coeff #[some ringExpr, none, some kExpr]

private def mkCoeffApplyExpr (ringExpr kExpr seriesExpr : Expr) : MetaM Expr := do
  let coeffMap ← mkCoeffMapExpr ringExpr kExpr
  mkAppM ``DFunLike.coe #[coeffMap, seriesExpr]

private def retargetResultToSeries (ringExpr kExpr seriesExpr : Expr) (r : ComputeResult) :
    TacticM ComputeResult := withMainContext do
  let some valueExpr := r.valueExpr | return r
  let some proofExpr := r.proofExpr | return r
  unless isSuccess r do
    return r
  let lhsExpr ← mkCoeffApplyExpr ringExpr kExpr seriesExpr
  let targetTy ← mkEq lhsExpr valueExpr
  let proofExpr ← mkExpectedTypeHint proofExpr targetTy
  return { r with proofExpr := some proofExpr }

private def parseCArg? (e : Expr) : Option Expr :=
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  match fn, args with
  | ``DFunLike.coe, #[_, _, _, _, f, a] =>
      let (fFn, _) := f.getAppFnArgs
      if fFn == ``PowerSeries.C then some a else none
  | _, _ => none

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

private def parsePowArgs? (e : Expr) : MetaM (Option (Expr × Nat)) := do
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  match fn, args with
  | ``HPow.hPow, #[_, _, _, _, base, exp] =>
      match (← evalNatExpr? exp) with
      | some m => return some (base, m)
      | none => return none
  | ``Pow.pow, #[_, _, base, exp] =>
      match (← evalNatExpr? exp) with
      | some m => return some (base, m)
      | none => return none
  | _, _ => return none

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

private def lookupCoeffData (db : CoeffDb) (key : CoeffKey) : TacticM LookupReport :=
    withMainContext do
  let mut hits : Array KnownCoeff := #[]
  for pt in db.points do
    if (← coeffKeyDefEq pt.key key) then
      hits := hits.push pt
  for entry in db.foralls do
    if (← isDefEq entry.seriesExpr key.seriesExpr) then
      let valueExpr := mkApp entry.valueFnExpr key.indexExpr
      let mut proofExpr := mkApp entry.proofExpr key.indexExpr
      if entry.reversed then
        proofExpr ← mkAppM ``Eq.symm #[proofExpr]
      hits := hits.push {
        key := key
        valueExpr := valueExpr
        proofExpr := proofExpr
        sourceFVarId := entry.sourceFVarId
        source := .forallEq
      }
  let kNat? ← evalNatExpr? key.indexExpr
  for entry in db.truncs do
    if (← isDefEq entry.seriesExpr key.seriesExpr) then
      let nNat? ← evalNatExpr? entry.nExpr
      match kNat?, nNat? with
      | some kNat, some nNat =>
          if kNat < nNat then
            let coeffMap ← mkAppOptM ``PowerSeries.coeff
              #[some entry.ringExpr, none, some key.indexExpr]
            let lhsExpr ← mkAppM ``DFunLike.coe #[coeffMap, key.seriesExpr]
            let rhsExpr ← mkAppM ``Polynomial.coeff #[entry.polyExpr, key.indexExpr]
            let goalTy ← mkEq lhsExpr rhsExpr
            let pTy ← inferType entry.polyExpr
            let congrProof ← withLocalDeclD `q pTy fun qVar => do
              let body ← mkAppM ``Polynomial.coeff #[qVar, key.indexExpr]
              let lam ← mkLambdaFVars #[qVar] body
              mkAppM ``congrArg #[lam, entry.proofExpr]
            let congrStx : TSyntax `term := ⟨(← PrettyPrinter.delab congrProof)⟩
            let tac ← `(tactic|
              have hcoeff := ($congrStx);
              dsimp at hcoeff;
              rw [PowerSeries.coeff_trunc] at hcoeff;
              norm_num at hcoeff;
              simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hcoeff)
            let save ← saveState
            let mvar ← mkFreshExprMVar goalTy
            let (goals, _) ← Elab.runTactic mvar.mvarId! tac
            if goals.isEmpty then
              let proofExpr ← instantiateMVars mvar
              hits := hits.push {
                key := key
                valueExpr := rhsExpr
                proofExpr := proofExpr
                sourceFVarId := entry.sourceFVarId
                source := .trunc
              }
            else
              restoreState save
      | _, _ => pure ()
  return { key := key, hits := hits }

private def proveGoalByTactic (goalTy : Expr) (tac : Syntax) : TacticM (Option Expr) := do
  let save ← saveState
  try
    let lctx ← getLCtx
    let localInsts ← getLocalInstances
    let mvar ← mkFreshExprMVarAt lctx localInsts goalTy
    let (goals, _) ← Term.withoutErrToSorry <| withoutRecover do
      Elab.runTactic mvar.mvarId! tac
    if goals.isEmpty then
      return some (← instantiateMVars mvar)
    restoreState save
    return none
  catch _ =>
    restoreState save
    return none

private def coeffFactUserName (total i : Nat) : Name :=
  if total == 1 then `hcoeff else Name.mkSimple s!"hcoeff{i}"

private def proveGoalByTacticWithFacts (goalTy : Expr) (facts : Array Expr)
    (tac : Syntax) : TacticM (Option Expr) := do
  let save ← saveState
  try
    let lctx ← getLCtx
    let localInsts ← getLocalInstances
    let mvar ← mkFreshExprMVarAt lctx localInsts goalTy
    let mut goalId := mvar.mvarId!
    for i in List.range facts.size do
      let fact := facts[i]!
      let goalIdNext ← goalId.withContext do
        let factTy ← inferType fact
        let goalId' ← goalId.assert (coeffFactUserName facts.size i) factTy fact
        let (_, goalId'') ← goalId'.intro1P
        pure goalId''
      goalId := goalIdNext
    let (goals, _) ← Term.withoutErrToSorry <| withoutRecover do
      Elab.runTactic goalId tac
    if goals.isEmpty then
      return some (← instantiateMVars mvar)
    restoreState save
    return none
  catch _ =>
    restoreState save
    return none

private partial def evalIntLikeValue? (e : Expr) : MetaM (Option Int) := do
  let e := e.cleanupAnnotations
  if let some n := e.numeral? then
    return some (Int.ofNat n)
  let (fn, args) := e.getAppFnArgs
  if fn == ``Nat.cast && args.size == 3 then
    if let some n ← evalNatExpr? args[2]! then
      return some (Int.ofNat n)
  if let some a := parseNegArg? e then
    return (← evalIntLikeValue? a).map (fun z => -z)
  if let some (a, b) := parseAddArgs? e then
    match (← evalIntLikeValue? a), (← evalIntLikeValue? b) with
    | some x, some y => return some (x + y)
    | _, _ => return none
  if let some (a, b) := parseSubArgs? e then
    match (← evalIntLikeValue? a), (← evalIntLikeValue? b) with
    | some x, some y => return some (x - y)
    | _, _ => return none
  if let some (a, b) := parseMulArgs? e then
    match (← evalIntLikeValue? a), (← evalIntLikeValue? b) with
    | some x, some y => return some (x * y)
    | _, _ => return none
  return none

private def mkIntLikeValueExpr (valueTy : Expr) (z : Int) : MetaM Expr := do
  if 0 <= z then
    mkAppOptM ``OfNat.ofNat #[some valueTy, some (mkNatLit z.toNat), none]
  else
    let nExpr ← mkAppOptM ``OfNat.ofNat #[some valueTy, some (mkNatLit z.natAbs), none]
    mkAppM ``Neg.neg #[nExpr]

private def tryNormalizeValue (valueExpr : Expr) : TacticM (Expr × Expr) := withMainContext do
  let valueTy ← inferType valueExpr
  let valueExprForNative ← Core.betaReduce valueExpr
  let nativeNat? ←
    if valueTy.isConstOf ``Nat then
      evalNatExpr? valueExprForNative
    else
      let (fn, args) := valueExprForNative.cleanupAnnotations.getAppFnArgs
      if fn == ``Nat.cast && args.size == 3 then
        evalNatExpr? args[2]!
      else
        pure none
  if let some n := nativeNat? then
    try
      let rhsNative ←
        if valueTy.isConstOf ``Nat then
          pure (mkNatLit n)
        else
          mkAppOptM ``OfNat.ofNat #[some valueTy, some (mkNatLit n), none]
      let nativeGoal ← mkEq valueExpr rhsNative
      if let some proofExpr ← proveGoalByTactic nativeGoal (← `(tactic| native_decide)) then
        return (rhsNative, proofExpr)
    catch _ =>
      pure ()
  if (← isDefEq valueTy (mkConst ``Rat)) then
    if let some z ← evalIntLikeValue? valueExprForNative then
      try
        let rhsNative ← mkIntLikeValueExpr valueTy z
        let nativeGoal ← mkEq valueExpr rhsNative
        if let some proofExpr ← proveGoalByTactic nativeGoal (← `(tactic| native_decide)) then
          return (rhsNative, proofExpr)
      catch _ =>
        pure ()
  let rhs ← mkFreshExprMVar valueTy
  let goalTy ← mkEq valueExpr rhs
  let tacs : Array Syntax := #[
    (← `(tactic|
      norm_num [Nat.choose, ArithmeticFunction.sigma, Function.update, Nat.divisors,
        Finset.sum_filter, Finset.sum_Ico_eq_sub, Finset.sum_range_succ]; rfl)),
    (← `(tactic|
      ring_nf; norm_num [Nat.choose, ArithmeticFunction.sigma, Function.update, Nat.divisors,
        Finset.sum_filter, Finset.sum_Ico_eq_sub, Finset.sum_range_succ]; rfl)),
    (← `(tactic|
      simp [Nat.choose, ArithmeticFunction.sigma, Function.update, Nat.divisors, Finset.sum_filter,
        Finset.sum_Ico_eq_sub, Finset.sum_range_succ];
      norm_num; rfl))
  ]
  for tac in tacs do
    let save ← saveState
    if let some proofExpr ← proveGoalByTactic goalTy tac then
      let rhsValue ← instantiateMVars rhs
      if !rhsValue.hasMVar then
        return (rhsValue, proofExpr)
    restoreState save
  return (valueExpr, ← mkEqRefl valueExpr)

private def mkAddValue (a b : Expr) : MetaM Expr :=
  mkAppM ``HAdd.hAdd #[a, b]

private def mkSubValue (a b : Expr) : MetaM Expr :=
  mkAppM ``HSub.hSub #[a, b]

private def mkNegValue (a : Expr) : MetaM Expr :=
  mkAppM ``Neg.neg #[a]

private def mkMulValue (a b : Expr) : MetaM Expr :=
  mkAppM ``HMul.hMul #[a, b]

private def mkInvValue (a : Expr) : MetaM Expr :=
  mkAppM ``Inv.inv #[a]

private def mkLeftAssocPowMul (base : Expr) (m : Nat) : MetaM Expr := do
  let mut acc := base
  for _ in List.range (m - 1) do
    acc ← mkMulValue acc base
  return acc

private def buildAddProof (ringExpr kExpr f g vF vG hF hG : Expr) : TacticM Expr :=
    withMainContext do
  let sumExpr ← mkAddValue f g
  let lhsExpr ← mkCoeffApplyExpr ringExpr kExpr sumExpr
  let valueExpr ← mkAddValue vF vG
  let goalTy ← mkEq lhsExpr valueExpr
  let tac ← `(tactic| simp_all only [map_add])
  let some proofExpr ← proveGoalByTacticWithFacts goalTy #[hF, hG] tac |
    throwError "ps_compute: failed to build add proof."
  return proofExpr

private def buildSubProof (ringExpr kExpr f g vF vG hF hG : Expr) : TacticM Expr :=
    withMainContext do
  let subExpr ← mkSubValue f g
  let lhsExpr ← mkCoeffApplyExpr ringExpr kExpr subExpr
  let valueExpr ← mkSubValue vF vG
  let goalTy ← mkEq lhsExpr valueExpr
  let tac ← `(tactic| simp_all only [map_sub])
  let some proofExpr ← proveGoalByTacticWithFacts goalTy #[hF, hG] tac |
    throwError "ps_compute: failed to build sub proof."
  return proofExpr

private def buildNegProof (ringExpr kExpr f vF hF : Expr) : TacticM Expr := withMainContext do
  let negExpr ← mkNegValue f
  let lhsExpr ← mkCoeffApplyExpr ringExpr kExpr negExpr
  let valueExpr ← mkNegValue vF
  let goalTy ← mkEq lhsExpr valueExpr
  let tac ← `(tactic| simp_all only [map_neg])
  let some proofExpr ← proveGoalByTacticWithFacts goalTy #[hF] tac |
    throwError "ps_compute: failed to build neg proof."
  return proofExpr

private def buildSmulProof (ringExpr kExpr smulExpr a vF hF : Expr) : TacticM Expr :=
    withMainContext do
  let lhsExpr ← mkCoeffApplyExpr ringExpr kExpr smulExpr
  let valueExpr ← mkMulValue a vF
  let goalTy ← mkEq lhsExpr valueExpr
  let tac ← `(tactic| simp_all [smul_eq_mul])
  let some proofExpr ← proveGoalByTacticWithFacts goalTy #[hF] tac |
    throwError "ps_compute: failed to build smul proof."
  return proofExpr

private def tryCloseByCoeffLookup (parsed : ParsedTarget) : TacticM Bool := withMainContext do
  let db ← withoutModifyingState buildCoeffDb
  let report ← withoutModifyingState (lookupCoeffData db (targetKey parsed))
  let goal ← getMainGoal
  let target ← goal.getType
  for hit in report.hits do
    let lhsOk ← isDefEq hit.valueExpr parsed.rhs
    if parsed.coeffOnLeft && lhsOk then
      if (← isDefEq (← inferType hit.proofExpr) target) then
        goal.assign hit.proofExpr
        replaceMainGoal []
        return true
    let rhsOk ← isDefEq hit.valueExpr parsed.lhs
    if (!parsed.coeffOnLeft) && rhsOk then
      let hsymm ← mkAppM ``Eq.symm #[hit.proofExpr]
      if (← isDefEq (← inferType hsymm) target) then
        goal.assign hsymm
        replaceMainGoal []
        return true
  return false

private def isPowerSeriesX (e : Expr) : Bool :=
  let (fn, _) := e.cleanupAnnotations.getAppFnArgs
  fn == ``PowerSeries.X

private def classifySeries (e : Expr) : MetaM SeriesClass := do
  let e := e.cleanupAnnotations
  let (fn, args) := e.getAppFnArgs
  match fn, args with
  | ``PowerSeries.mk, _ => return .mk
  | ``PowerSeries.X, _ => return .X
  | ``Zero.zero, _ => return .zero
  | ``One.one, _ => return .one
  | ``OfNat.ofNat, #[_, nExpr, _] =>
      let n? := natLitExpr? nExpr
      let n? ← match n? with
        | some n => pure (some n)
        | none => evalNatExpr? nExpr
      match n? with
      | some 0 => return .zero
      | some 1 => return .one
      | some n => return .numeral n
      | none => return .unsupported
  | ``OfNat.ofNat, _ =>
      if args.size < 2 then
        return .unsupported
      let nExpr := args[args.size - 2]!
      let n? := natLitExpr? nExpr
      let n? ← match n? with
        | some n => pure (some n)
        | none => evalNatExpr? nExpr
      match n? with
      | some 0 => return .zero
      | some 1 => return .one
      | some n => return .numeral n
      | none => return .unsupported
  | ``HPow.hPow, #[_, _, _, _, base, exp] =>
      match (← evalNatExpr? exp) with
      | some m =>
          return if isPowerSeriesX base then .XPow m else .unsupported
      | none => return .unsupported
  | ``Pow.pow, #[_, _, base, exp] =>
      match (← evalNatExpr? exp) with
      | some m =>
          return if isPowerSeriesX base then .XPow m else .unsupported
      | none => return .unsupported
  | _, _ =>
      if (parseCArg? e).isSome then
        return .C
      return .unsupported

private def seriesClassDesc : SeriesClass → String
  | .mk => "PowerSeries.mk"
  | .C => "PowerSeries.C"
  | .X => "PowerSeries.X"
  | .zero => "0"
  | .one => "1"
  | .numeral n => s!"numeral {n}"
  | .XPow m => s!"X^{m}"
  | .unsupported => "unsupported"

private def computeBuiltinCoeff (ringExpr kExpr : Expr) (kNat : Nat) (seriesExpr : Expr) :
    TacticM (Option ComputeResult) := withMainContext do
  let cls ← classifySeries seriesExpr
  let lhsExpr ← mkCoeffApplyExpr ringExpr kExpr seriesExpr
  let ringStx ← PrettyPrinter.delab ringExpr
  let kStx ← PrettyPrinter.delab kExpr
  let zeroExpr ← Term.elabTerm (← `((0 : $ringStx))) (some ringExpr)
  let oneExpr ← Term.elabTerm (← `((1 : $ringStx))) (some ringExpr)
  let mkResultFromGoal (valueExpr : Expr) (tac : Syntax) : TacticM (Option ComputeResult) := do
    let goalTy ← mkEq lhsExpr valueExpr
    if let some proofExpr ← proveGoalByTactic goalTy tac then
      return some (successResult valueExpr proofExpr #[] #[])
    return none
  match cls with
  | .mk =>
      let (fn, args) := seriesExpr.cleanupAnnotations.getAppFnArgs
      if fn == ``PowerSeries.mk && args.size >= 1 then
        let f := args[args.size - 1]!
        let valueExpr := mkApp f kExpr
        let tac ← `(tactic|
          simp [PowerSeries.coeff_mk])
        mkResultFromGoal valueExpr tac
      else
        return none
  | .C =>
      if let some a := parseCArg? seriesExpr then
        let valueExpr := if kNat == 0 then a else zeroExpr
        let aStx ← PrettyPrinter.delab a
        let valueStx ← PrettyPrinter.delab valueExpr
        let tac ← `(tactic|
          change PowerSeries.coeff (R := $ringStx) $kStx (PowerSeries.C $aStx) = $valueStx;
          rw [PowerSeries.coeff_C];
          first | simp | rfl)
        mkResultFromGoal valueExpr tac
      else
        return none
  | .X =>
      let valueExpr := if kNat == 1 then oneExpr else zeroExpr
      let tac ← `(tactic|
        rw [PowerSeries.coeff_X];
        first | simp | rfl)
      mkResultFromGoal valueExpr tac
  | .zero =>
      let valueExpr := zeroExpr
      let tac ← `(tactic|
        first | simp | rfl)
      mkResultFromGoal valueExpr tac
  | .one =>
      let valueExpr := if kNat == 0 then oneExpr else zeroExpr
      let tac ← `(tactic|
        rw [PowerSeries.coeff_one];
        first | simp | rfl)
      mkResultFromGoal valueExpr tac
  | .numeral n =>
      let nStx : TSyntax `num := ⟨Syntax.mkNatLit n⟩
      let valueExpr ←
        if kNat == 0 then
          let castStx : TSyntax `term ← `( (($nStx : Nat) : $ringStx) )
          Term.elabTerm castStx (some ringExpr)
        else
          pure zeroExpr
      let valueStx ← PrettyPrinter.delab valueExpr
      let tac ← `(tactic|
        change PowerSeries.coeff (R := $ringStx) $kStx
          (PowerSeries.C (($nStx : Nat) : $ringStx)) = $valueStx;
        rw [PowerSeries.coeff_C];
        simp)
      mkResultFromGoal valueExpr tac
  | .XPow m =>
      let valueExpr := if kNat == m then oneExpr else zeroExpr
      let tac ← `(tactic|
        rw [PowerSeries.coeff_X_pow];
        first | simp | rfl)
      mkResultFromGoal valueExpr tac
  | .unsupported =>
      return none

partial def computeCoeff (db : CoeffDb) (kExpr : Expr) (kNat : Nat) (seriesExpr : Expr) :
    TacticM ComputeResult := withMainContext do
  let key : CoeffKey := { seriesExpr := seriesExpr, indexExpr := kExpr }
  let (seriesFn, seriesArgs) := seriesExpr.cleanupAnnotations.getAppFnArgs
  if (parseInvArg? seriesExpr).isSome || seriesFn == ``PowerSeries.mk then
    if let some cached ← getCachedCoeff? key then
      return cached
  let report ← withoutModifyingState <| lookupCoeffData db key
  if let some hit := report.hits[0]? then
    return successResult hit.valueExpr hit.proofExpr #[key] #[hit]
  let some ringExpr ← ringExprOfSeries? seriesExpr |
    return failureResult #[key] #[key] #[]
  if seriesFn == ``PowerSeries.mk && seriesArgs.size >= 1 then
    let f := seriesArgs[seriesArgs.size - 1]!
    let valueExpr := (mkApp f kExpr).headBeta
    if let some innerCoeff := parseCoeffExpr? valueExpr then
      if let some innerNat ← evalNatExpr? innerCoeff.kExpr then
        let rInner ← computeCoeff db innerCoeff.kExpr innerNat innerCoeff.seriesExpr
        if isSuccess rInner then
          let some innerValue := rInner.valueExpr | return rInner
          let some innerProof := rInner.proofExpr | return rInner
          let lhsExpr ← mkCoeffApplyExpr ringExpr kExpr seriesExpr
          let mkGoalTy ← mkEq lhsExpr valueExpr
          let mkTac ← `(tactic| simp [PowerSeries.coeff_mk])
          if let some mkProof ← proveGoalByTactic mkGoalTy mkTac then
            let proofExpr ← mkAppM ``Eq.trans #[mkProof, innerProof]
            let (innerValueNorm, innerNormProof) ← tryNormalizeValue innerValue
            let proofExpr ← mkAppM ``Eq.trans #[proofExpr, innerNormProof]
            let r := successResult innerValueNorm proofExpr rInner.needed rInner.used
            cacheCoeff key r
            return r
        return rInner
  if let some builtin ← computeBuiltinCoeff ringExpr kExpr kNat seriesExpr then
    return builtin
  if let some f := parseInvArg? seriesExpr then
    let rConst ← computeCoeff db (mkNatLit 0) 0 f
    if isSuccess rConst then
      let some vConst := rConst.valueExpr | return rConst
      let some hConst := rConst.proofExpr | return rConst
      let (vConstNorm, hConstNorm) ← tryNormalizeValue vConst
      let zeroExpr ← mkAppOptM ``OfNat.ofNat #[some ringExpr, some (mkNatLit 0), none]
      let hCoeff0Raw ← mkAppM ``Eq.trans #[hConst, hConstNorm]
      let constLhs ← mkCoeffApplyExpr ringExpr (mkNatLit 0) f
      let constGoalTy ← mkEq constLhs vConstNorm
      let hCoeff0 ← mkExpectedTypeHint hCoeff0Raw constGoalTy
      if (← isDefEq vConstNorm zeroExpr) then
        let lhsExpr ← mkCoeffApplyExpr ringExpr kExpr seriesExpr
        let goalTy ← mkEq lhsExpr zeroExpr
        let coeffConst ← mkAppM ``PowerSeries.coeff_zero_eq_constantCoeff_apply #[f]
        let coeffConstSymm ← mkAppM ``Eq.symm #[coeffConst]
        let hzero ← mkAppM ``Eq.trans #[coeffConstSymm, hCoeff0]
        let invEqZeroIff ← mkAppOptM ``PowerSeries.inv_eq_zero #[none, none, some f]
        let invEqZero ← mkAppM ``Iff.mpr #[invEqZeroIff, hzero]
        let coeffEq ← withLocalDeclD `q (← inferType seriesExpr) fun qVar => do
          let body ← mkCoeffApplyExpr ringExpr kExpr qVar
          let lam ← mkLambdaFVars #[qVar] body
          mkAppM ``congrArg #[lam, invEqZero]
        let some (_, _, coeffZeroExpr) := (← inferType coeffEq).eq? |
          return failureResult rConst.needed rConst.missing
            (rConst.unsupported.push seriesExpr) rConst.used
        let zeroCoeffGoal ← mkEq coeffZeroExpr zeroExpr
        let zeroCoeffTac ← `(tactic| simp)
        if let some zeroCoeffProof ← proveGoalByTactic zeroCoeffGoal zeroCoeffTac then
          let proofExpr ← mkAppM ``Eq.trans #[coeffEq, zeroCoeffProof]
          let proofExpr ← mkExpectedTypeHint proofExpr goalTy
          let proofExpr ← mkAuxTheorem goalTy proofExpr (zetaDelta := true)
          let r := successResult zeroExpr proofExpr rConst.needed rConst.used
          cacheCoeff key r
          return r
      let invConst ← mkInvValue vConstNorm
      let mut needed := rConst.needed
      let mut used := rConst.used
      let mut proofExprs : Array Expr := #[hCoeff0]
      let lhsExpr ← mkCoeffApplyExpr ringExpr kExpr seriesExpr
      if kNat == 0 then
        let goalTy ← mkEq lhsExpr invConst
        let tac ← `(tactic|
          rw [PowerSeries.coeff_inv];
          simp_all [PowerSeries.coeff_zero_eq_constantCoeff_apply])
        if let some proofExpr ← proveGoalByTacticWithFacts goalTy proofExprs tac then
          let (invConstNorm, invConstNormProof) ← tryNormalizeValue invConst
          let proofExpr ← mkAppM ``Eq.trans #[proofExpr, invConstNormProof]
          let finalTy ← mkEq lhsExpr invConstNorm
          let proofExpr ← mkExpectedTypeHint proofExpr finalTy
          let proofExpr ← mkAuxTheorem finalTy proofExpr (zetaDelta := true)
          let r := successResult invConstNorm proofExpr needed used
          cacheCoeff key r
          return r
        return failureResult needed rConst.missing (rConst.unsupported.push seriesExpr) used
      let mut termVals : Array Expr := #[]
      for i0 in List.range kNat do
        let i := i0 + 1
        let j := kNat - i
        let iExpr := mkNatLit i
        let jExpr := mkNatLit j
        let rF ← computeCoeff db iExpr i f
        if !isSuccess rF then
          return failureResult (needed ++ rF.needed) rF.missing
            (rF.unsupported.push seriesExpr) (used ++ rF.used)
        let some vF := rF.valueExpr | return rF
        let some hF := rF.proofExpr | return rF
        let (vFNorm, hFNorm) ← tryNormalizeValue vF
        let hF ← mkAppM ``Eq.trans #[hF, hFNorm]
        let rInv ← computeCoeff db jExpr j seriesExpr
        if !isSuccess rInv then
          return failureResult (needed ++ rF.needed ++ rInv.needed) rInv.missing
            (rInv.unsupported.push seriesExpr) (used ++ rF.used ++ rInv.used)
        let some vInv := rInv.valueExpr | return rInv
        let some hInv := rInv.proofExpr | return rInv
        let (vInvNorm, hInvNorm) ← tryNormalizeValue vInv
        let hInv ← mkAppM ``Eq.trans #[hInv, hInvNorm]
        needed := needed ++ rF.needed ++ rInv.needed
        used := used ++ rF.used ++ rInv.used
        proofExprs := proofExprs.push hF
        proofExprs := proofExprs.push hInv
        termVals := termVals.push (← mkMulValue vFNorm vInvNorm)
      let sumExpr ←
        match termVals[0]? with
        | none => pure zeroExpr
        | some t0 => do
            let mut acc := t0
            for t in termVals.toList.drop 1 do
              acc ← mkAddValue acc t
            pure acc
      let valueExpr ← mkMulValue (← mkNegValue invConst) sumExpr
      let goalTy ← mkEq lhsExpr valueExpr
      let tac ← `(tactic|
        rw [PowerSeries.coeff_inv];
        simp_all [Finset.antidiagonal, PowerSeries.coeff_zero_eq_constantCoeff_apply];
        try ring_nf)
      if let some proofExpr ← proveGoalByTacticWithFacts goalTy proofExprs tac then
        let (valueNorm, valueNormProof) ← tryNormalizeValue valueExpr
        let proofExpr ← mkAppM ``Eq.trans #[proofExpr, valueNormProof]
        let finalTy ← mkEq lhsExpr valueNorm
        let proofExpr ← mkExpectedTypeHint proofExpr finalTy
        let proofExpr ← mkAuxTheorem finalTy proofExpr (zetaDelta := true)
        let r := successResult valueNorm proofExpr needed used
        cacheCoeff key r
        return r
      return failureResult needed rConst.missing (rConst.unsupported.push seriesExpr) used
    return rConst
  if let some f := parseNegArg? seriesExpr then
    let rF ← computeCoeff db kExpr kNat f
    if isSuccess rF then
      let some vF := rF.valueExpr | return rF
      let some hF := rF.proofExpr | return rF
      let valueExpr ← mkNegValue vF
      let proofExpr ← buildNegProof ringExpr kExpr f vF hF
      return {
        valueExpr := some valueExpr
        proofExpr := some proofExpr
        needed := rF.needed
        used := rF.used
        missing := rF.missing
        unsupported := rF.unsupported
      }
    return rF
  if let some (a, f) := parseSmulArgs? seriesExpr then
    unless (← isDefEq (← inferType a) ringExpr) do
      return failureResult #[key] #[key] #[seriesExpr]
    let rF ← computeCoeff db kExpr kNat f
    if isSuccess rF then
      let some vF := rF.valueExpr | return rF
      let some hF := rF.proofExpr | return rF
      let valueExpr ← mkMulValue a vF
      let proofExpr ← buildSmulProof ringExpr kExpr seriesExpr a vF hF
      return {
        valueExpr := some valueExpr
        proofExpr := some proofExpr
        needed := rF.needed
        used := rF.used
        missing := rF.missing
        unsupported := rF.unsupported
      }
    return rF
  if let some (f, g) := parseAddArgs? seriesExpr then
    let rF ← computeCoeff db kExpr kNat f
    let rG ← computeCoeff db kExpr kNat g
    if isSuccess rF && isSuccess rG then
      let some vF := rF.valueExpr | return mergeResultInfo rF rG
      let some hF := rF.proofExpr | return mergeResultInfo rF rG
      let some vG := rG.valueExpr | return mergeResultInfo rF rG
      let some hG := rG.proofExpr | return mergeResultInfo rF rG
      let valueExpr ← mkAddValue vF vG
      let proofExpr ← buildAddProof ringExpr kExpr f g vF vG hF hG
      return {
        valueExpr := some valueExpr
        proofExpr := some proofExpr
        needed := mergeKeys rF.needed rG.needed
        used := mergeKnown rF.used rG.used
        missing := mergeKeys rF.missing rG.missing
        unsupported := mergeExprs rF.unsupported rG.unsupported
      }
    return mergeResultInfo rF rG
  if let some (f, g) := parseSubArgs? seriesExpr then
    let rF ← computeCoeff db kExpr kNat f
    let rG ← computeCoeff db kExpr kNat g
    if isSuccess rF && isSuccess rG then
      let some vF := rF.valueExpr | return mergeResultInfo rF rG
      let some hF := rF.proofExpr | return mergeResultInfo rF rG
      let some vG := rG.valueExpr | return mergeResultInfo rF rG
      let some hG := rG.proofExpr | return mergeResultInfo rF rG
      let valueExpr ← mkSubValue vF vG
      let proofExpr ← buildSubProof ringExpr kExpr f g vF vG hF hG
      return {
        valueExpr := some valueExpr
        proofExpr := some proofExpr
        needed := mergeKeys rF.needed rG.needed
        used := mergeKnown rF.used rG.used
        missing := mergeKeys rF.missing rG.missing
        unsupported := mergeExprs rF.unsupported rG.unsupported
      }
    return mergeResultInfo rF rG
  if let some (f, g) := parseMulArgs? seriesExpr then
    let zeroExpr ← mkAppOptM ``OfNat.ofNat #[some ringExpr, some (mkNatLit 0), none]
    let mut needed : Array CoeffKey := #[]
    let mut used : Array KnownCoeff := #[]
    let mut missing : Array CoeffKey := #[]
    let mut unsupported : Array Expr := #[]
    let mut termVals : Array Expr := #[]
    let mut proofExprs : Array Expr := #[]
    for i in List.range (kNat + 1) do
      let j := kNat - i
      let iExpr := mkNatLit i
      let jExpr := mkNatLit j
      let rL ← computeCoeff db iExpr i f
      if isSuccess rL then
        let some vL := rL.valueExpr |
          return mergeResultInfo rL (failureResult #[] #[] #[seriesExpr])
        let lZero ← isDefEq vL zeroExpr
        if lZero then
          needed := needed ++ rL.needed
          used := used ++ rL.used
          missing := missing ++ rL.missing
          unsupported := unsupported ++ rL.unsupported
          if let some p := rL.proofExpr then
            proofExprs := proofExprs.push p
        else
          let rR ← computeCoeff db jExpr j g
          if isSuccess rR then
            let some vR := rR.valueExpr | return mergeResultInfo rL rR
            needed := needed ++ rL.needed ++ rR.needed
            used := used ++ rL.used ++ rR.used
            missing := missing ++ rL.missing ++ rR.missing
            unsupported := unsupported ++ rL.unsupported ++ rR.unsupported
            if let some p := rL.proofExpr then
              proofExprs := proofExprs.push p
            if let some p := rR.proofExpr then
              proofExprs := proofExprs.push p
            let rZero ← isDefEq vR zeroExpr
            if !rZero then
              termVals := termVals.push (← mkMulValue vL vR)
          else
            needed := needed ++ rL.needed ++ rR.needed
            used := used ++ rL.used ++ rR.used
            missing := missing ++ rL.missing ++ rR.missing
            unsupported := unsupported ++ rL.unsupported ++ rR.unsupported
      else
        let rR ← computeCoeff db jExpr j g
        if isSuccess rR then
          let some vR := rR.valueExpr | return mergeResultInfo rL rR
          let rZero ← isDefEq vR zeroExpr
          if rZero then
            needed := needed ++ rR.needed
            used := used ++ rR.used
            missing := missing ++ rR.missing
            unsupported := unsupported ++ rR.unsupported
            if let some p := rR.proofExpr then
              proofExprs := proofExprs.push p
          else
            needed := needed ++ rL.needed ++ rR.needed
            used := used ++ rL.used ++ rR.used
            missing := missing ++ rL.missing ++ rR.missing
            unsupported := unsupported ++ rL.unsupported ++ rR.unsupported
        else
          needed := needed ++ rL.needed ++ rR.needed
          used := used ++ rL.used ++ rR.used
          missing := missing ++ rL.missing ++ rR.missing
          unsupported := unsupported ++ rL.unsupported ++ rR.unsupported
    if !missing.isEmpty || !unsupported.isEmpty then
      return failureResult needed missing unsupported used
    let valueExpr ←
      match termVals[0]? with
      | none => pure zeroExpr
      | some t0 => do
          let mut acc := t0
          for t in termVals.toList.drop 1 do
            acc ← mkAddValue acc t
          pure acc
    let lhsExpr ← mkCoeffApplyExpr ringExpr kExpr (← mkMulValue f g)
    let goalTy ← mkEq lhsExpr valueExpr
    let tac ← `(tactic|
      rw [PowerSeries.coeff_mul];
      simp_all [Finset.antidiagonal, PowerSeries.coeff_C, PowerSeries.coeff_X,
        PowerSeries.coeff_X_pow];
      (try ring_nf))
    if let some proofExpr ← proveGoalByTacticWithFacts goalTy proofExprs tac then
      return successResult valueExpr proofExpr needed used
    return failureResult needed missing (unsupported.push seriesExpr) used
  if let some (base, m) ← parsePowArgs? seriesExpr then
    let zeroExpr ← mkAppOptM ``OfNat.ofNat #[some ringExpr, some (mkNatLit 0), none]
    let oneExpr ← mkAppOptM ``OfNat.ofNat #[some ringExpr, some (mkNatLit 1), none]
    if m == 0 then
      let valueExpr := if kNat == 0 then oneExpr else zeroExpr
      let lhsExpr ← mkCoeffApplyExpr ringExpr kExpr seriesExpr
      let goalTy ← mkEq lhsExpr valueExpr
      let tac ← `(tactic|
        rw [pow_zero, PowerSeries.coeff_one];
        first | simp | rfl)
      if let some proofExpr ← proveGoalByTactic goalTy tac then
        return successResult valueExpr proofExpr #[] #[]
      return failureResult #[key] #[key] #[seriesExpr]
    if m == 1 then
      let rBase ← computeCoeff db kExpr kNat base
      if isSuccess rBase then
        let some valueExpr := rBase.valueExpr | return rBase
        let some hBase := rBase.proofExpr | return rBase
        let seriesEqGoal ← mkEq seriesExpr base
        let tac ← `(tactic| simp [pow_one])
        if let some seriesEqProof ← proveGoalByTactic seriesEqGoal tac then
          let coeffEqProof ← withLocalDeclD `q (← inferType seriesExpr) fun qVar => do
            let body ← mkCoeffApplyExpr ringExpr kExpr qVar
            let lam ← mkLambdaFVars #[qVar] body
            mkAppM ``congrArg #[lam, seriesEqProof]
          let proofExpr ← mkAppM ``Eq.trans #[coeffEqProof, hBase]
          return successResult valueExpr proofExpr rBase.needed rBase.used
        return failureResult rBase.needed rBase.missing
          (rBase.unsupported.push seriesExpr) rBase.used
      return rBase
    let expandedExpr ← mkLeftAssocPowMul base m
    let rExpanded ← computeCoeff db kExpr kNat expandedExpr
    if isSuccess rExpanded then
      let some valueExpr := rExpanded.valueExpr | return rExpanded
      let some hExpanded := rExpanded.proofExpr | return rExpanded
      let seriesEqGoal ← mkEq seriesExpr expandedExpr
      let tac ← `(tactic| simp [pow_succ, pow_two])
      if let some seriesEqProof ← proveGoalByTactic seriesEqGoal tac then
        let coeffEqProof ← withLocalDeclD `q (← inferType seriesExpr) fun qVar => do
          let body ← mkCoeffApplyExpr ringExpr kExpr qVar
          let lam ← mkLambdaFVars #[qVar] body
          mkAppM ``congrArg #[lam, seriesEqProof]
        let proofExpr ← mkAppM ``Eq.trans #[coeffEqProof, hExpanded]
        return successResult valueExpr proofExpr rExpanded.needed rExpanded.used
      return failureResult rExpanded.needed rExpanded.missing
        (rExpanded.unsupported.push seriesExpr) rExpanded.used
    return rExpanded
  if let some seriesUnfolded ← withTransparency .all <| unfoldDefinition? seriesExpr then
    let seriesUnfolded ← Mathlib.Tactic.etaReduceAll seriesUnfolded.headBeta
    if seriesUnfolded != seriesExpr then
      let rUnfolded ← computeCoeff db kExpr kNat seriesUnfolded
      return (← retargetResultToSeries ringExpr kExpr seriesExpr rUnfolded)
  let seriesReduced ← withTransparency .all <| whnf seriesExpr
  let seriesReduced ← Mathlib.Tactic.etaReduceAll seriesReduced.headBeta
  if seriesReduced != seriesExpr then
    let rReduced ← computeCoeff db kExpr kNat seriesReduced
    return (← retargetResultToSeries ringExpr kExpr seriesExpr rReduced)
  let isAtom := !seriesExpr.cleanupAnnotations.isApp
  if isAtom then
    return failureResult #[key] #[key] #[]
  return failureResult #[key] #[key] #[seriesExpr]

private def tryCloseByLocalDirectEq (parsed : ParsedTarget) : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then
      continue
    let h := mkFVar ldecl.fvarId
    let hTy ← inferType h
    if (← isDefEq hTy target) then
      goal.assign h
      replaceMainGoal []
      return true
    if let some (_, hl, hr) := hTy.eq? then
      if (← isDefEq hl parsed.rhs) && (← isDefEq hr parsed.lhs) then
        let hsymm ← mkAppM ``Eq.symm #[h]
        if (← isDefEq (← inferType hsymm) target) then
          goal.assign hsymm
          replaceMainGoal []
          return true
  return false

private def ppCoeffKeyStr (key : CoeffKey) : MetaM String := do
  let s ← ppExprStr key.seriesExpr
  let k ← ppExprStr key.indexExpr
  return s!"coeff[{k}] ({s})"

private def reportDiag : TacticM Unit := withMainContext do
  resetComputeCache
  let g ← getMainGoal
  let target ← g.getType
  logInfo m!"[ps_compute?] target: {(← ppExprStr target)}"
  let parsed? := parseTarget? target
  match parsed? with
  | none =>
      logInfo "[ps_compute?] coeff-goal: missing (expect `PowerSeries.coeff k E = rhs` or reverse)."
  | some parsed =>
      let side := if parsed.coeffOnLeft then "lhs" else "rhs"
      logInfo m!"[ps_compute?] coeff-goal: found on {side}"
      match (← evalNatExpr? parsed.coeff.kExpr) with
      | some k => logInfo m!"[ps_compute?] index numeral: found ({k})"
      | none => logInfo "[ps_compute?] index numeral: missing (k is not a concrete Nat numeral)"
      match (← evalNatExpr? parsed.coeff.kExpr) with
      | none => pure ()
      | some kNat =>
          let db ← withoutModifyingState buildCoeffDb
          let result ← withoutModifyingState
            (computeCoeff db parsed.coeff.kExpr kNat parsed.coeff.seriesExpr)
          if result.needed.isEmpty then
            logInfo "[ps_compute?] sufficient coefficient data: none required"
          else
            logInfo "[ps_compute?] sufficient coefficient data: requires"
            for key in result.needed do
              logInfo m!"[ps_compute?]   {← ppCoeffKeyStr key}"
          if result.missing.isEmpty then
            logInfo "[ps_compute?] sufficient coefficient data: found"
          else
            logInfo "[ps_compute?] sufficient coefficient data: missing"
            for key in result.missing do
              logInfo m!"[ps_compute?]   missing {← ppCoeffKeyStr key}"
          if result.used.isEmpty then
            logInfo "[ps_compute?] source hypothesis: none"
          else
            for hit in result.used do
              let srcName ← fvarUserName hit.sourceFVarId
              logInfo m!"[ps_compute?] source hypothesis: {srcName} ({sourceDesc hit.source})"
          if result.unsupported.isEmpty then
            pure ()
          else
            for e in result.unsupported do
              logInfo m!"[ps_compute?] unsupported: {(← ppExprStr e)}"
          if result.missing.isEmpty && result.unsupported.isEmpty then
            match result.valueExpr with
            | some valueExpr =>
                let (normalizedValue, _) ← tryNormalizeValue valueExpr
                logInfo m!"[ps_compute?] computed result: {(← ppComputedValueStr normalizedValue)}"
            | none =>
                logInfo "[ps_compute?] computed result: unavailable"
          else
            logInfo "[ps_compute?] computed result: unavailable (partial data)"

private def computeNormalizedCoeff (parsed : ParsedTarget) : TacticM NormalizedCompute :=
    withMainContext do
  let some kNat ← evalNatExpr? parsed.coeff.kExpr |
    throwError "ps_compute: index `k` must be a concrete Nat numeral."
  let db ← withoutModifyingState buildCoeffDb
  let result ← computeCoeff db parsed.coeff.kExpr kNat parsed.coeff.seriesExpr
  if !result.unsupported.isEmpty then
    let mut msg := "ps_compute: unsupported coefficient sources:"
    for e in result.unsupported do
      msg := msg ++ s!" {(← ppExprStr e)};"
    throwError m!"{msg} try `ps_compute?`."
  if !result.missing.isEmpty then
    let mut msg := "ps_compute: missing coeff data:"
    for key in result.missing do
      msg := msg ++ s!" {(← ppCoeffKeyStr key)};"
    throwError m!"{msg} try `ps_compute?`."
  let some proofExpr := result.proofExpr |
    throwError "ps_compute: internal failure (missing proof)."
  let proofTy ← inferType proofExpr
  let some (_, proofLhs, computedValue) := proofTy.eq? |
    throwError "ps_compute: internal failure (computed proof is not an equality)."
  let (normalizedValue, normalizedProof) ← tryNormalizeValue computedValue
  let coeffProof ← mkAppM ``Eq.trans #[proofExpr, normalizedProof]
  return { proofLhs, computedValue, normalizedValue, coeffProof }

private def proveSideEq (lhs rhs : Expr) : TacticM Expr := do
  if (← isDefEq lhs rhs) then
    return (← mkEqRefl lhs)
  let sideGoal ← mkEq lhs rhs
  let tacs : Array Syntax := #[
    (← `(tactic|
      norm_num [ArithmeticFunction.sigma, Function.update, Nat.divisors, Finset.sum_filter,
        Finset.sum_Ico_eq_sub, Finset.sum_range_succ])),
    (← `(tactic|
      ring_nf; norm_num [ArithmeticFunction.sigma, Function.update, Nat.divisors,
        Finset.sum_filter, Finset.sum_Ico_eq_sub, Finset.sum_range_succ])),
    (← `(tactic| ring_nf)),
    (← `(tactic| ring_nf; norm_num)),
    (← `(tactic| norm_num))
  ]
  for tac in tacs do
    if let some sideProof ← proveGoalByTactic sideGoal tac then
      return sideProof
  throwError "ps_compute: failed to prove computed value equals goal side."

private def tryCloseExistsByCompute : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let (fn, args) := target.cleanupAnnotations.getAppFnArgs
  if fn != ``Exists || args.size != 2 then
    return false
  let domain := args[0]!
  let pred := args[1]!
  withLocalDeclD `x domain fun x => do
    let body ← whnf (mkApp pred x)
    let some parsed := parseTarget? body | return false
    if parsed.coeffOnLeft then
      unless (← isDefEq parsed.rhs x) do
        return false
    else
      unless (← isDefEq parsed.lhs x) do
        return false
    let norm ← computeNormalizedCoeff parsed
    let coeffSide := if parsed.coeffOnLeft then parsed.lhs else parsed.rhs
    unless (← isDefEq norm.proofLhs coeffSide) do
      throwError "ps_compute: internal failure (proof lhs mismatch)."
    let bodyProof ←
      if parsed.coeffOnLeft then
        pure norm.coeffProof
      else
        mkAppM ``Eq.symm #[norm.coeffProof]
    let existsProof ← mkAppM ``Exists.intro #[norm.normalizedValue, bodyProof]
    if (← isDefEq (← inferType existsProof) target) then
      logInfo m!"[ps_compute] computed result: {(← ppComputedValueStr norm.normalizedValue)}"
      goal.assign existsProof
      replaceMainGoal []
      return true
    return false

private def runCompute : TacticM Unit := withMainContext do
  resetComputeCache
  let target ← getMainTarget
  let some parsed := parseTarget? target |
    if (← tryCloseExistsByCompute) then
      return
    else
      throwError "ps_compute: goal must be `PowerSeries.coeff k E = rhs`, reversed, or `∃ x, ...`."
  let some _ ← evalNatExpr? parsed.coeff.kExpr |
    throwError "ps_compute: index `k` must be a concrete Nat numeral."
  if (← tryCloseByLocalDirectEq parsed) then
    return
  let norm ← computeNormalizedCoeff parsed
  let finalProof ←
    if parsed.coeffOnLeft then
      unless (← isDefEq norm.proofLhs parsed.lhs) do
        throwError "ps_compute: internal failure (proof lhs mismatch)."
      if let .mvar rhsMVarId := parsed.rhs then
        unless (← rhsMVarId.isAssigned) do
          rhsMVarId.assign norm.normalizedValue
        pure norm.coeffProof
      else if (← isDefEq norm.normalizedValue parsed.rhs) then
        pure norm.coeffProof
      else
        let proof2 ← proveSideEq norm.normalizedValue parsed.rhs
        mkAppM ``Eq.trans #[norm.coeffProof, proof2]
    else
      unless (← isDefEq norm.proofLhs parsed.rhs) do
        throwError "ps_compute: internal failure (proof lhs mismatch)."
      let hsymm ← mkAppM ``Eq.symm #[norm.coeffProof]
      if let .mvar lhsMVarId := parsed.lhs then
        unless (← lhsMVarId.isAssigned) do
          lhsMVarId.assign norm.normalizedValue
        pure hsymm
      else if (← isDefEq parsed.lhs norm.normalizedValue) then
        pure hsymm
      else
        let proof2 ← proveSideEq parsed.lhs norm.normalizedValue
        mkAppM ``Eq.trans #[proof2, hsymm]
  let goal ← getMainGoal
  if (← isDefEq (← inferType finalProof) target) then
    logInfo m!"[ps_compute] computed result: {(← ppComputedValueStr norm.normalizedValue)}"
    goal.assign finalProof
    replaceMainGoal []
    return
  throwError "ps_compute: failed to close goal from computed coefficient."

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

syntax (name := psCompute) "ps_compute" : tactic
syntax (name := psComputeDiag) "ps_compute?" : tactic

elab_rules : tactic
  | `(tactic| ps_compute) => withElapsedLog "ps_compute" runCompute
  | `(tactic| ps_compute?) => reportDiag

end Tactics

end XYin
