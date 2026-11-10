-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import Lean

/-!
# The decoder-arity check

`#assert_decoder_arities` holds the truncation table (`truncationMinimum`) to
the decoders it guards, so the two cannot drift.  It reads each listed
decoder's elaborated body and fails the build unless:

* the decoder's first action is the truncation check (`requireMessageLength`)
  at the syscall's own minimum;
* every other use of the decoded record is a word read (`requireMsgReg` of its
  message registers at a literal index), so no argument is read any other way;
* the words it reads are exactly `0, …, minimum - 1`: a decoder that reads a
  word at or past its minimum, or a minimum past the words it reads, fails;
* every syscall whose minimum is nonzero is listed, once.

A decoder whose body is a call of another decoder on the same record is read
through that call.  Anything the check cannot classify fails it.
-/

namespace SeLe4n.Kernel.Architecture.DecoderArity

open Lean Meta Elab Command Term

/-- What one decoder's body shows: the truncation check's minimum, if its
first action is one, and the word indices it reads. -/
structure DecoderReads where
  header : Option Nat
  reads : Array Nat

/-- The natural number an expression reduces to, or a failure. -/
def evalNatExpr (e : Expr) : MetaM Nat := do
  if let some n ← (evalNat e).run then return n
  let r ← reduce e
  if let some n ← (evalNat r).run then return n
  throwError "decoder arity: {e} does not reduce to a numeral"

/-- Is `e` the decoded record's message registers? -/
def isMsgRegsOf (msgRegs : Name) (d : FVarId) (e : Expr) : Bool :=
  match e with
  | .app (.const n _) (.fvar x) => n == msgRegs && x == d
  | .proj _ _ (.fvar x) => x == d
  | _ => false

/-- The word reads in `e`, failing on any other use of the record `d`. -/
partial def collectReads (read msgRegs check : Name) (d : FVarId) (e : Expr) :
    StateT (Array Nat) MetaM Unit := do
  match e with
  | .fvar x =>
    if x == d then
      throwError "decoder arity: the decoded record is used other than by a word read"
  | .mdata _ b => collectReads read msgRegs check d b
  | .lam _ t b _ | .forallE _ t b _ =>
    collectReads read msgRegs check d t; collectReads read msgRegs check d b
  | .letE _ t v b _ =>
    collectReads read msgRegs check d t; collectReads read msgRegs check d v
    collectReads read msgRegs check d b
  | .proj _ _ b => collectReads read msgRegs check d b
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf read && args.size == 2 && isMsgRegsOf msgRegs d args[0]! then
      let some k ← ((evalNat args[1]!).run : MetaM (Option Nat))
        | throwError "decoder arity: word index {args[1]!} is not a literal"
      modify (fun (ks : Array Nat) => ks.push k)
    else if fn.isConstOf check then
      throwError "decoder arity: a truncation check that is not the first action"
    else
      collectReads read msgRegs check d fn
      for a in args do collectReads read msgRegs check d a
  | _ => pure ()

/-- Read a decoder's body: its leading truncation check and its word reads,
through a decoder it delegates to. -/
partial def decoderReads (read msgRegs check : Name) (decl : Name) : MetaM DecoderReads := do
  let info ← getConstInfo decl
  let some value := info.value?
    | throwError "decoder arity: {decl} has no definition to read"
  lambdaTelescope value fun xs body => do
    let some dExpr := xs[0]?
      | throwError "decoder arity: {decl} takes no decoded record"
    let d := dExpr.fvarId!
    let body := body.consumeMData
    -- A decoder that is a call of another on the same record.
    let fn := body.getAppFn
    let args := body.getAppArgs
    if let .const callee _ := fn then
      if args[0]? == some dExpr && callee != read && callee != check
          && !(← isMatcher callee) && callee != ``Bind.bind then
        for a in args[1:] do
          let (_, rs) ← (collectReads read msgRegs check d a).run #[]
          unless rs.isEmpty do throwError "decoder arity: {decl} reads words past its delegate"
        return ← decoderReads read msgRegs check callee
    -- The first action, a truncation check.
    if fn.isConstOf ``Bind.bind && args.size == 6 then
      let x := args[4]!.consumeMData
      if x.getAppFn.isConstOf check && x.getAppNumArgs == 2
          && x.getAppArgs[0]! == dExpr then
        let n ← evalNatExpr x.getAppArgs[1]!
        let (_, rs) ← (collectReads read msgRegs check d args[5]!).run #[]
        return { header := some n, reads := rs }
    let (_, rs) ← (collectReads read msgRegs check d body).run #[]
    return { header := none, reads := rs }

/-- Whether a declaration's first action on its record is the truncation check. -/
def hasTruncationHeader (check : Name) (decl : Name) : MetaM Bool := do
  let some value := (← getConstInfo decl).value? | return false
  lambdaTelescope value fun xs body => do
    let some dExpr := xs[0]? | return false
    let body := body.consumeMData
    let args := body.getAppArgs
    if body.getAppFn.isConstOf ``Bind.bind && args.size == 6 then
      let x := args[4]!.consumeMData
      return x.getAppFn.isConstOf check && x.getAppArgs[0]? == some dExpr
    return false

/-- Replace the record's syscall field by the constructor `c`. -/
def fixSyscall (sidProj : Name) (d : FVarId) (c : Expr) (e : Expr) : Expr :=
  e.replace fun x =>
    match x with
    | .app (.const n _) (.fvar y) => if n == sidProj && y == d then some c else none
    | _ => none

/-- The decoders a dispatcher's arm for one syscall calls on the decoded record
`d`, its syscall field fixed (`fixSyscall`): a match on a constructor is
reduced to its arm, a listed decoder or one whose first action is the
truncation check is recorded, and any other declaration handed the whole
record is read through its body.  Every other subterm is walked, so an arm the
walk cannot reduce is over-approximated. -/
partial def armDecoders (listed : Array Name) (check sidProj : Name) (c : Expr) (d : FVarId)
    (e : Expr) : StateT (Array Name × NameSet) MetaM Unit := do
  let e := fixSyscall sidProj d c e
  match e with
  | .mdata _ b => armDecoders listed check sidProj c d b
  | .proj _ _ b => armDecoders listed check sidProj c d b
  | .lam n t b bi | .forallE n t b bi =>
    armDecoders listed check sidProj c d t
    withLocalDecl n bi t fun x => armDecoders listed check sidProj c d (b.instantiate1 x)
  | .letE n t v b _ =>
    armDecoders listed check sidProj c d t
    armDecoders listed check sidProj c d v
    withLetDecl n t v fun x => armDecoders listed check sidProj c d (b.instantiate1 x)
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .const f us := fn then
      if (← isMatcher f) then
        let r ← try some <$> reduceMatcher? e catch _ => pure none
        if let some (.reduced e') := r then
          return ← armDecoders listed check sidProj c d e'
      if args.any (· == .fvar d) then
        if listed.contains f || (← hasTruncationHeader check f) then
          modify fun (ds, seen) => (if ds.contains f then ds else ds.push f, seen)
          for a in args do armDecoders listed check sidProj c d a
          return
        let (_, seen) ← get
        unless seen.contains f do
          modify fun (ds, seen) => (ds, seen.insert f)
          if let some value := (← getConstInfo f).value? then
            let v := (value.instantiateLevelParams (← getConstInfo f).levelParams us).beta args
            armDecoders listed check sidProj c d v
        for a in args do armDecoders listed check sidProj c d a
        return
    armDecoders listed check sidProj c d fn
    for a in args do armDecoders listed check sidProj c d a
  | _ => pure ()

/-- The decoders `dispatcher`'s arm for the syscall `c` calls. -/
def dispatcherDecoders (listed : Array Name) (check sidProj recordTy dispatcher : Name)
    (c : Expr) : MetaM (Array Name) := do
  let some value := (← getConstInfo dispatcher).value?
    | throwError "decoder arity: {dispatcher} has no definition to read"
  lambdaTelescope value fun xs body => do
    let mut d? : Option FVarId := none
    for x in xs do
      if (← inferType x).isConstOf recordTy then d? := some x.fvarId!
    let some d := d? | throwError "decoder arity: {dispatcher} takes no decoded record"
    let ((), (ds, _)) ← (armDecoders listed check sidProj c d body).run (#[], {})
    return ds

syntax (name := assertDecoderArities)
  "#assert_decoder_arities " ident ident ident ident ident ident
    " [" sepBy(("(" term ", " ident ")"), ", ") "]" : command

/-- `#assert_decoder_arities minimum check read msgRegs syscallId dispatcher
[(sid, decoder), …]`: the table, the truncation check, the word read, the
record's message-register and syscall fields, and the dispatcher whose arms
the pairing is pinned against. -/
@[command_elab assertDecoderArities] def elabAssertDecoderArities : CommandElab
  | `(#assert_decoder_arities $minimum $check $read $msgRegs $sidField $dispatcher
      [$[($sids, $decs)],*]) =>
    liftTermElabM do
      let minimumN ← realizeGlobalConstNoOverloadWithInfo minimum
      let checkN ← realizeGlobalConstNoOverloadWithInfo check
      let readN ← realizeGlobalConstNoOverloadWithInfo read
      let msgRegsN ← realizeGlobalConstNoOverloadWithInfo msgRegs
      let sidFieldN ← realizeGlobalConstNoOverloadWithInfo sidField
      let dispatcherN ← realizeGlobalConstNoOverloadWithInfo dispatcher
      let recordTy ← forallTelescope (← getConstInfo msgRegsN).type fun ys _ => do
        let some y := ys[0]? | throwError "decoder arity: {msgRegsN} is not a field"
        let .const n _ := (← inferType y).getAppFn | throwError "decoder arity: unknown record"
        pure n
      let minInfo ← getConstInfo minimumN
      let sidTy ← forallTelescope minInfo.type fun ys _ => do
        let some y := ys[0]? | throwError "decoder arity: {minimumN} takes no syscall"
        inferType y
      let .const sidTyN _ := sidTy.getAppFn | throwError "decoder arity: unknown syscall type"
      let ind ← getConstInfoInduct sidTyN
      let minOf (sid : Expr) : MetaM Nat :=
        evalNatExpr (mkApp (mkConst minimumN) sid)
      let mut listed : Array Name := #[]
      let mut pairs : Array (Name × Name) := #[]
      for sidStx in sids, decStx in decs do
        let sid ← instantiateMVars (← elabTermEnsuringType sidStx sidTy)
        let .const sidN _ := sid | throwError "decoder arity: {sid} is not a syscall constructor"
        if listed.contains sidN then throwError "decoder arity: {sidN} is listed twice"
        listed := listed.push sidN
        let decN ← realizeGlobalConstNoOverloadWithInfo decStx
        pairs := pairs.push (sidN, decN)
        let n ← minOf sid
        if n == 0 then
          throwError "decoder arity: {sidN} has minimum 0 and is not listed"
        let r ← decoderReads readN msgRegsN checkN decN
        if r.header != some n then
          throwError "decoder arity: {decN}'s first action is not the truncation check at \
            {sidN}'s minimum {n} (found {r.header})"
        let expected := (List.range n).toArray
        let got := (r.reads.toList.eraseDups.mergeSort (· ≤ ·)).toArray
        unless got == expected do
          throwError "decoder arity: {decN} reads words {got}, but {sidN}'s minimum {n} \
            needs exactly {expected}"
      for c in ind.ctors do
        let n ← minOf (mkConst c)
        if n != 0 && !listed.contains c then
          throwError "decoder arity: {c} has minimum {n} and no decoder listed"
      -- The pairing, pinned against the dispatcher: each syscall's arm calls
      -- exactly its listed decoder, and an unlisted syscall's arm none.
      let decoders := pairs.map (·.2)
      for c in ind.ctors do
        let found ← dispatcherDecoders decoders checkN sidFieldN recordTy dispatcherN (mkConst c)
        match pairs.find? (·.1 == c) with
        | some (_, dec) =>
          unless found == #[dec] do
            throwError "decoder arity: {dispatcherN}'s arm for {c} calls {found}, not {dec}"
        | none =>
          unless found.isEmpty do
            throwError "decoder arity: {dispatcherN}'s arm for {c}, which has minimum 0, calls \
              {found}"
  | _ => throwUnsupportedSyntax

end SeLe4n.Kernel.Architecture.DecoderArity
