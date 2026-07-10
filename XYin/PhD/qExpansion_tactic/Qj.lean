import Lean
import Lean.Meta.Native
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Util.Qq

open PowerSeries
open scoped Qq

namespace XYin.PhD.qExpansion_tactic

def reportTiming : Bool := true

/-- Sum of `d^k` over positive divisors `d` of `n`, computed by finite search. -/
def sigmaPow (k n : Nat) : Int :=
  (List.range n).foldl
    (fun acc i =>
      let d := i + 1
      if n % d = 0 then acc + (d : Int) ^ k else acc)
    0

def e4CoeffInt (n : Nat) : Int :=
  if n = 0 then 1 else 240 * sigmaPow 3 n

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

def deltaCoeffsArrayUpTo (n : Nat) : Array Int :=
  let e4 := coeffArray e4CoeffInt n
  let e6 := coeffArray e6CoeffInt n
  let e4Sq := convArrayUpTo e4 e4 n
  let e4Cube := convArrayUpTo e4Sq e4 n
  let e6Sq := convArrayUpTo e6 e6 n
  (List.range (n + 1)).foldl
    (fun acc i => acc.push ((e4Cube.getD i 0 - e6Sq.getD i 0) / 1728))
    #[]

def deltaCoeffInt (n : Nat) : Int := (deltaCoeffsArrayUpTo n).getD n 0

def deltaCoeffsUpTo (n : Nat) : List Int := (deltaCoeffsArrayUpTo n).toList

def deltaOverQCoeffInt (n : Nat) : Int := deltaCoeffInt (n + 1)

def qoverDeltaCoeffsArrayUpTo (n : Nat) : Array Int :=
  let top := n + 1
  let e4 := coeffArray e4CoeffInt top
  let e6 := coeffArray e6CoeffInt top
  let e4Sq := convArrayUpTo e4 e4 top
  let e4Cube := convArrayUpTo e4Sq e4 top
  let e6Sq := convArrayUpTo e6 e6 top
  let delta :=
    (List.range (top + 1)).foldl
      (fun acc i => acc.push ((e4Cube.getD i 0 - e6Sq.getD i 0) / 1728))
      #[]
  let deltaOverQ :=
    (List.range (n + 1)).foldl
      (fun acc i => acc.push (delta.getD (i + 1) 0))
      #[]
  inverseOnePlusCoeffsUpTo deltaOverQ n

def qoverDeltaCoeffInt (n : Nat) : Int :=
  (qoverDeltaCoeffsArrayUpTo n).getD n 0

def qjCoeffsArrayUpTo (n : Nat) : Array Int :=
  let top := n + 1
  let e4 := coeffArray e4CoeffInt top
  let e6 := coeffArray e6CoeffInt top
  let e4Sq := convArrayUpTo e4 e4 top
  let e4Cube := convArrayUpTo e4Sq e4 top
  let e6Sq := convArrayUpTo e6 e6 top
  let delta :=
    (List.range (top + 1)).foldl
      (fun acc i => acc.push ((e4Cube.getD i 0 - e6Sq.getD i 0) / 1728))
      #[]
  let deltaOverQ :=
    (List.range (n + 1)).foldl
      (fun acc i => acc.push (delta.getD (i + 1) 0))
      #[]
  let qoverDelta := inverseOnePlusCoeffsUpTo deltaOverQ n
  convArrayUpTo e4Cube qoverDelta n

def qjCoeffInt (n : Nat) : Int := (qjCoeffsArrayUpTo n).getD n 0

def qjCoeffsUpTo (n : Nat) : List Int := (qjCoeffsArrayUpTo n).toList

syntax (name := qexpCoeffCmd) "#qexp" ident "coeff" num : command
syntax (name := qexpPrecisionCmd) "#qexp" ident "precision" num : command

open Lean Elab Command in
elab_rules : command
  | `(command| #qexp $which:ident coeff $n:num) => do
      let nVal := n.getNat
      let t0 ← liftIO IO.monoMsNow
      let value ←
        match which.getId with
        | `qj => pure (qjCoeffInt nVal)
        | `Delta => pure (deltaCoeffInt nVal)
        | _ => throwErrorAt which "unknown q-expansion target; expected `qj` or `Delta`"
      let valueStr := toString value
      let valueStrLen := valueStr.length
      if valueStrLen == 0 then
        throwError "internal error: empty q-expansion coefficient output"
      let t1 ← liftIO IO.monoMsNow
      logInfoAt n valueStr
      if reportTiming then
        logInfoAt n m!"[qexp time: {t1 - t0}ms]"
  | `(command| #qexp $which:ident precision $n:num) => do
      let nVal := n.getNat
      let t0 ← liftIO IO.monoMsNow
      let valueStr ←
        match which.getId with
        | `qj => pure (toString (qjCoeffsUpTo nVal))
        | `Delta => pure (toString (deltaCoeffsUpTo nVal))
        | _ => throwErrorAt which "unknown q-expansion target; expected `qj` or `Delta`"
      let valueStrLen := valueStr.length
      if valueStrLen == 0 then
        throwError "internal error: empty q-expansion precision output"
      let t1 ← liftIO IO.monoMsNow
      logInfoAt n valueStr
      if reportTiming then
        logInfoAt n m!"[qexp time: {t1 - t0}ms]"

def qj_qexpansion : PowerSeries ℤ :=
  PowerSeries.mk qjCoeffInt

theorem qj_qexpansion_coeff_eq (n : Nat) :
    qj_qexpansion.coeff n = qjCoeffInt n := by
  simp [qj_qexpansion]

def Delta_qexpansion : PowerSeries ℤ :=
  PowerSeries.mk deltaCoeffInt

theorem Delta_qexpansion_coeff_eq (n : Nat) :
    Delta_qexpansion.coeff n = deltaCoeffInt n := by
  simp [Delta_qexpansion]

open Lean Meta in
def mkNativeDecideProofFor (p : Expr) : MetaM Expr := do
  let d ← mkDecide p
  match (← nativeEqTrue `qexp_coeff d) with
  | .notTrue =>
      throwError "native_decide evaluated proposition as false{indentExpr p}"
  | .success prf =>
      let inst := d.appArg!
      return mkApp3 (mkConst ``of_decide_eq_true) p inst prf

open Lean Meta Qq in
def foo (n : Nat) :
    Lean.MetaM (Int × (nQ : Q(Nat)) ×
      (ex : Q(ℤ)) ×
      Q(qj_qexpansion.coeff $nQ = $ex)) := do
  let x := qjCoeffInt n
  let nQ : Q(Nat) := Qq.mkNatLitQ n
  let xQ : Q(ℤ) := Qq.mkIntLitQ x
  let ex : Q(ℤ) := xQ
  let propExpr ← mkEq (← mkAppM ``qjCoeffInt #[nQ]) xQ
  let hval ← mkNativeDecideProofFor propExpr
  let proof0 ← mkAppM ``qj_qexpansion_coeff_eq #[nQ]
  let proofExpr ← mkAppM ``Eq.trans #[proof0, hval]
  let target : Q(Prop) := q(qj_qexpansion.coeff $nQ = $ex)
  let proof ← mkExpectedTypeHint proofExpr target
  pure ⟨x, nQ, ex, proof⟩

open Lean Meta Qq in
def fooWithValue (n : Nat) (xQ : Q(ℤ)) :
    Lean.MetaM ((nQ : Q(Nat)) ×
      Q(qj_qexpansion.coeff $nQ = $xQ)) := do
  let nQ : Q(Nat) := Qq.mkNatLitQ n
  let propExpr ← mkEq (← mkAppM ``qjCoeffInt #[nQ]) xQ
  let hval ← mkNativeDecideProofFor propExpr
  let proof0 ← mkAppM ``qj_qexpansion_coeff_eq #[nQ]
  let proofExpr ← mkAppM ``Eq.trans #[proof0, hval]
  let target : Q(Prop) := q(qj_qexpansion.coeff $nQ = $xQ)
  let proof ← mkExpectedTypeHint proofExpr target
  pure ⟨nQ, proof⟩

open Lean Meta Qq in
def deltaFoo (n : Nat) :
    Lean.MetaM (Int × (nQ : Q(Nat)) ×
      (ex : Q(ℤ)) ×
      Q(Delta_qexpansion.coeff $nQ = $ex)) := do
  let x := deltaCoeffInt n
  let nQ : Q(Nat) := Qq.mkNatLitQ n
  let xQ : Q(ℤ) := Qq.mkIntLitQ x
  let ex : Q(ℤ) := xQ
  let propExpr ← mkEq (← mkAppM ``deltaCoeffInt #[nQ]) xQ
  let hval ← mkNativeDecideProofFor propExpr
  let proof0 ← mkAppM ``Delta_qexpansion_coeff_eq #[nQ]
  let proofExpr ← mkAppM ``Eq.trans #[proof0, hval]
  let target : Q(Prop) := q(Delta_qexpansion.coeff $nQ = $ex)
  let proof ← mkExpectedTypeHint proofExpr target
  pure ⟨x, nQ, ex, proof⟩

open Lean Meta Qq in
def deltaFooWithValue (n : Nat) (xQ : Q(ℤ)) :
    Lean.MetaM ((nQ : Q(Nat)) ×
      Q(Delta_qexpansion.coeff $nQ = $xQ)) := do
  let nQ : Q(Nat) := Qq.mkNatLitQ n
  let propExpr ← mkEq (← mkAppM ``deltaCoeffInt #[nQ]) xQ
  let hval ← mkNativeDecideProofFor propExpr
  let proof0 ← mkAppM ``Delta_qexpansion_coeff_eq #[nQ]
  let proofExpr ← mkAppM ``Eq.trans #[proof0, hval]
  let target : Q(Prop) := q(Delta_qexpansion.coeff $nQ = $xQ)
  let proof ← mkExpectedTypeHint proofExpr target
  pure ⟨nQ, proof⟩

end XYin.PhD.qExpansion_tactic

syntax (name := qexpCoeffAuto) "qexp_coeff" ident num : term
syntax (name := qexpCoeffManual) "qexp_coeff" ident num term : term

open Lean Elab Term in
elab_rules : term
  | `(qexp_coeff $which:ident $n:num) => do
      let nVal := n.getNat
      let t0 ← IO.monoMsNow
      let proof ←
        match which.getId with
        | `qj => do
            let ⟨_, _, _, proof⟩ ← Lean.Meta.liftMetaM <| XYin.PhD.qExpansion_tactic.foo nVal
            pure proof
        | `Delta => do
            let ⟨_, _, _, proof⟩ ← Lean.Meta.liftMetaM <| XYin.PhD.qExpansion_tactic.deltaFoo nVal
            pure proof
        | _ => throwErrorAt which "unknown q-expansion target; expected `qj` or `Delta`"
      let t1 ← IO.monoMsNow
      if XYin.PhD.qExpansion_tactic.reportTiming then
        logInfoAt n m!"[qexp_coeff time: {t1 - t0}ms]"
      pure proof
  | `(qexp_coeff $which:ident $n:num $x:term) => do
      let nVal := n.getNat
      let xExpr ← elabTermEnsuringType x q(ℤ)
      synthesizeSyntheticMVarsNoPostponing
      let xQ : Q(ℤ) ← instantiateMVars xExpr
      let t0 ← IO.monoMsNow
      let proof ←
        match which.getId with
        | `qj => do
            let ⟨_, proof⟩ ← Lean.Meta.liftMetaM <| XYin.PhD.qExpansion_tactic.fooWithValue nVal xQ
            pure proof
        | `Delta => do
            let ⟨_, proof⟩ ← Lean.Meta.liftMetaM <|
              XYin.PhD.qExpansion_tactic.deltaFooWithValue nVal xQ
            pure proof
        | _ => throwErrorAt which "unknown q-expansion target; expected `qj` or `Delta`"
      let t1 ← IO.monoMsNow
      if XYin.PhD.qExpansion_tactic.reportTiming then
        logInfoAt n m!"[qexp_coeff time: {t1 - t0}ms]"
      pure proof
