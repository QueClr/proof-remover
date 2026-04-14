import Lean
import Lean.DeclarationRange
import Lean.Util.FoldConsts
import ProofRemover.Frontend

namespace ProofRemover

open Lean

private def lemmaCmdKind : Name := Name.mkSimple "lemma"

private def scopedCmdKind : Name := ``Lean.Parser.Command.in

private def nestedScopedCmd? (cmd : Syntax) : Option Syntax :=
  if cmd.getKind == scopedCmdKind && cmd.getNumArgs > 0 then
    some cmd[cmd.getNumArgs - 1]
  else
    none

private partial def isTheoremDeclCmd (cmd : Syntax) : Bool :=
  if cmd.isOfKind ``Lean.Parser.Command.declaration then
    if cmd.getNumArgs > 1 then
      let inner := cmd[1]
      inner.isOfKind ``Lean.Parser.Command.theorem
    else
      false
  else if let some inner := nestedScopedCmd? cmd then
    isTheoremDeclCmd inner
  else
    false

private partial def isLemmaCmd (cmd : Syntax) : Bool :=
  if cmd.getKind == lemmaCmdKind then
    true
  else if let some inner := nestedScopedCmd? cmd then
    isLemmaCmd inner
  else
    false

private partial def isInstanceCmd (cmd : Syntax) : Bool :=
  if cmd.isOfKind ``Lean.Parser.Command.declaration then
    cmd.getNumArgs > 1 && cmd[1].isOfKind ``Lean.Parser.Command.instance
  else if let some inner := nestedScopedCmd? cmd then
    isInstanceCmd inner
  else
    false

def isTheoremLikeCmd (cmd : Syntax) : Bool :=
  isTheoremDeclCmd cmd || isLemmaCmd cmd

def isDeclarationLikeCmd (cmd : Syntax) : Bool :=
  cmd.isOfKind ``Lean.Parser.Command.declaration || isLemmaCmd cmd || isTheoremDeclCmd cmd

private def isInteractiveCmd (cmd : Syntax) : Bool :=
  -- A small conservative denylist. These can fail if they reference dropped decls.
  cmd.isOfKind ``Lean.Parser.Command.check ||
  cmd.isOfKind ``Lean.Parser.Command.check_failure ||
  cmd.isOfKind ``Lean.Parser.Command.eval ||
  cmd.isOfKind ``Lean.Parser.Command.evalBang

private def isScopeStartCmd (cmd : Syntax) : Bool :=
  cmd.isOfKind ``Lean.Parser.Command.section ||
  cmd.isOfKind ``Lean.Parser.Command.namespace

private def isScopeEndCmd (cmd : Syntax) : Bool :=
  cmd.isOfKind ``Lean.Parser.Command.end

private def cmdRange? (cmd : Syntax) : Option Lean.Syntax.Range :=
  cmd.getRange? (canonicalOnly := true)

private def posInRange (p : String.Pos.Raw) (r : Lean.Syntax.Range) : Bool :=
  r.start <= p && p <= r.stop

private def originalCommandText? (pf : ParsedFile) (cmd : Syntax) : Option String :=
  cmdRange? cmd |>.map fun r =>
    String.Pos.Raw.extract pf.input r.start r.stop

private def isHashCommand (pf : ParsedFile) (cmd : Syntax) : Bool :=
  match originalCommandText? pf cmd with
  | some text => text.trimAsciiStart.toString.startsWith "#"
  | none => false

private def isDroppedNonDeclCmd (pf : ParsedFile) (cmd : Syntax) : Bool :=
  isInteractiveCmd cmd || isHashCommand pf cmd

structure DeclMaps where
  declPos    : Std.HashMap Name String.Pos.Raw
  declToCmd  : Std.HashMap Name Nat
  cmdToDecls : Std.HashMap Nat (Array Name)

structure ScopeMaps where
  startToEnd : Std.HashMap Nat Nat
  endToStart : Std.HashMap Nat Nat
  cmdScopeEnd : Array Nat

inductive RetainedCmdKind where
  | decl
  | scopeStart
  | scopeEnd
  | context
  deriving DecidableEq, Inhabited, Repr

structure RetainedCmd where
  originalIdx : Nat
  kind : RetainedCmdKind
  cmd : Syntax
  deriving Inhabited

def buildDeclMaps (pf : ParsedFile) : DeclMaps := Id.run do
  let ranges := declRangeExt.getState pf.env
  let cmdRanges : Array (Option Lean.Syntax.Range) := pf.commands.map cmdRange?

  let mut declPos : Std.HashMap Name String.Pos.Raw := {}
  let mut declToCmd : Std.HashMap Name Nat := {}
  let mut cmdToDecls : Std.HashMap Nat (Array Name) := {}

  for (declName, rs) in ranges do
    if pf.env.isImportedConst declName then
      continue
    let p : String.Pos.Raw := pf.fileMap.ofPosition rs.selectionRange.pos
    declPos := declPos.insert declName p

    let mut found : Option Nat := none
    for i in [0:pf.commands.size] do
      match cmdRanges[i]! with
      | some r =>
          if posInRange p r then
            found := some i
            break
      | none => continue

    if let some i := found then
      declToCmd := declToCmd.insert declName i
      let prev := cmdToDecls.getD i #[]
      cmdToDecls := cmdToDecls.insert i (prev.push declName)

  return { declPos, declToCmd, cmdToDecls }

def buildScopeMaps (pf : ParsedFile) : ScopeMaps := Id.run do
  let n := pf.commands.size
  let mut startToEnd : Std.HashMap Nat Nat := {}
  let mut endToStart : Std.HashMap Nat Nat := {}
  let mut stack : List Nat := []

  for i in [0:n] do
    let cmd := pf.commands[i]!
    if isScopeEndCmd cmd then
      match stack with
      | startIdx :: rest =>
          startToEnd := startToEnd.insert startIdx i
          endToStart := endToStart.insert i startIdx
          stack := rest
      | [] => pure ()
    else if isScopeStartCmd cmd then
      stack := i :: stack

  for startIdx in stack do
    startToEnd := startToEnd.insert startIdx n

  let mut cmdScopeEnd : Array Nat := Array.mkEmpty n
  let mut active : List Nat := []
  for i in [0:n] do
    if endToStart.contains i then
      match active with
      | _ :: rest => active := rest
      | [] => pure ()

    let scopeEnd :=
      match active with
      | startIdx :: _ => startToEnd.getD startIdx n
      | [] => n
    cmdScopeEnd := cmdScopeEnd.push scopeEnd

    let cmd := pf.commands[i]!
    if isScopeStartCmd cmd then
      active := i :: active

  return { startToEnd, endToStart, cmdScopeEnd }

def findLastTheoremLike? (pf : ParsedFile) (maps : DeclMaps) : Option Name := Id.run do
  -- Map command index -> local theorem names defined at that command.
  let mut cmdToThms : Std.HashMap Nat (Array Name) := {}
  for (n, i) in maps.declToCmd.toList do
    match pf.env.find? n with
    | some (.thmInfo ..) =>
        let prev := cmdToThms.getD i #[]
        cmdToThms := cmdToThms.insert i (prev.push n)
    | _ => continue

  let mut best : Option (Nat × String.Pos.Raw × Name) := none
  for i in [0:pf.commands.size] do
    let cmd := pf.commands[i]!
    if !isTheoremLikeCmd cmd then
      continue
    let thms := cmdToThms.getD i #[]
    if thms.isEmpty then
      continue
    let p : String.Pos.Raw := (cmd.getPos? (canonicalOnly := true)).getD (cmdRange? cmd |>.map (·.start) |>.getD 0)
    -- pick the theorem in this command with the smallest declaration position (heuristic = main decl)
    let pick :=
      thms.foldl (init := thms[0]!) fun acc n =>
        let pa := maps.declPos.getD acc 0
        let pn := maps.declPos.getD n 0
        if pn < pa then n else acc
    match best with
    | none => best := some (i, p, pick)
    | some (_, q, _) =>
        if q < p then
          best := some (i, p, pick)

  match best with
  | some (_, _, n) => some n
  | none =>
      -- Fallback: last local theorem constant by source position.
      let mut bestThm : Option (Name × String.Pos.Raw) := none
      for (n, p) in maps.declPos.toList do
        match pf.env.find? n with
        | some (.thmInfo ..) =>
            match bestThm with
            | none => bestThm := some (n, p)
            | some (_, q) => if q < p then bestThm := some (n, p)
        | _ => continue
      bestThm.map (·.1)

private def includeValueDeps (maps : DeclMaps) (targets : Std.HashSet Name) (n : Name) (c : ConstantInfo) : Bool :=
  match c with
  | .defnInfo _   => true
  | .opaqueInfo _ => true
  -- Elaborated definitions often depend on generated local proof constants such as `_proof_1`.
  -- Those auxiliaries have no source command mapping, so we descend through their proof terms to
  -- recover the source lemmas they mention (for example a helper lemma used in a `where` proof).
  | .thmInfo _    => !targets.contains n && !maps.declToCmd.contains n
  | _             => false

def computeNeededDecls (pf : ParsedFile) (maps : DeclMaps) (targets : Array Name) : Std.HashSet Name := Id.run do
  let mut needed : Std.HashSet Name := {}
  let mut neededCmds : Std.HashSet Nat := {}
  let targetSet := targets.foldl (init := ({} : Std.HashSet Name)) fun acc n => acc.insert n
  let mut work : List Name := targets.toList

  let pushAll (ns : NameSet) (work : List Name) : List Name :=
    ns.foldl (fun w n => n :: w) work

  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if needed.contains n then
      continue
    needed := needed.insert n

    if pf.env.isImportedConst n then
      continue

    if let some cmdIdx := maps.declToCmd.get? n then
      if !neededCmds.contains cmdIdx then
        neededCmds := neededCmds.insert cmdIdx
        -- Include all declarations produced by this command (constructors, recursors, eqn theorems, etc.).
        if let some decls := maps.cmdToDecls.get? cmdIdx then
          for m in decls do
            if !needed.contains m then
              work := m :: work

    if let some cinfo := pf.env.find? n then
      work := pushAll cinfo.type.getUsedConstantsAsSet work
      if includeValueDeps maps targetSet n cinfo then
        match cinfo with
        | .defnInfo v   => work := pushAll v.value.getUsedConstantsAsSet work
        | .opaqueInfo v => work := pushAll v.value.getUsedConstantsAsSet work
        | .thmInfo v    => work := pushAll v.value.getUsedConstantsAsSet work
        | _             => pure ()

  return needed

private partial def findFirst? (stx : Syntax) (p : Syntax → Bool) : Option Syntax :=
  if p stx then
    some stx
  else
    stx.getArgs.findSome? fun arg => findFirst? arg p

def mkSorryDeclVal (env : Environment) : IO Syntax := do
  let dummy := "theorem _tmp : True := by\n  sorry\n"
  match Parser.runParserCategory env `command dummy with
  | Except.error err =>
      throw <| IO.userError s!"failed to parse dummy stub command:\n{err}"
  | Except.ok cmd =>
      match findFirst? cmd (fun stx => stx.isOfKind ``Lean.Parser.Command.declValSimple) with
      | some stx => pure stx
      | none => throw <| IO.userError "internal error: could not find declValSimple in dummy stub command"

def mkSorryInstanceVal (env : Environment) : IO Syntax := do
  let dummy := "instance : Nat := by\n  sorry\n"
  match Parser.runParserCategory env `command dummy with
  | Except.error err =>
      throw <| IO.userError s!"failed to parse dummy instance stub command:\n{err}"
  | Except.ok cmd =>
      if cmd.isOfKind ``Lean.Parser.Command.declaration && cmd.getNumArgs > 1 then
        let inner := cmd[1]
        if inner.isOfKind ``Lean.Parser.Command.instance && inner.getNumArgs > 0 then
          pure <| inner[inner.getNumArgs - 1]
        else
          throw <| IO.userError "internal error: could not find instance body in dummy stub command"
      else
        throw <| IO.userError "internal error: malformed dummy instance stub command"

partial def stubProof (sorryDeclVal sorryInstanceVal : Syntax) (cmd : Syntax) : Syntax :=
  if cmd.isOfKind ``Lean.Parser.Command.declaration then
    if cmd.getNumArgs > 1 then
      let inner := cmd[1]
      if inner.isOfKind ``Lean.Parser.Command.theorem && inner.getNumArgs > 0 then
        -- The `theorem` parser includes the keyword token as an argument, so don't hardcode indices.
        -- The declaration value is always the last argument.
        let inner' := inner.modifyArg (inner.getNumArgs - 1) (fun _ => sorryDeclVal)
        cmd.modifyArg 1 (fun _ => inner')
      else if inner.isOfKind ``Lean.Parser.Command.instance && inner.getNumArgs > 0 then
        let inner' := inner.modifyArg (inner.getNumArgs - 1) (fun _ => sorryInstanceVal)
        cmd.modifyArg 1 (fun _ => inner')
      else
        cmd
    else
      cmd
  else if isLemmaCmd cmd then
    if cmd.getNumArgs > 1 then
      let g := cmd[1]
      if g.getNumArgs > 0 then
        -- `lemma` is a Mathlib macro, but its `declVal` is also the last argument.
        let g' := g.modifyArg (g.getNumArgs - 1) (fun _ => sorryDeclVal)
        cmd.modifyArg 1 (fun _ => g')
      else
        cmd
    else
      cmd
  else if let some inner := nestedScopedCmd? cmd then
    cmd.modifyArg (cmd.getNumArgs - 1) (fun _ => stubProof sorryDeclVal sorryInstanceVal inner)
  else
    cmd

def sliceCommands (pf : ParsedFile) (maps : DeclMaps) (needed : Std.HashSet Name)
    (targets : Array Name) (keepTargets : Bool) (sorryDeclVal sorryInstanceVal : Syntax) : Array RetainedCmd := Id.run do
  let scopes := buildScopeMaps pf
  let mut keepIdx : Std.HashSet Nat := {}
  for n in needed do
    if let some i := maps.declToCmd.get? n then
      keepIdx := keepIdx.insert i

  if !keepTargets then
    for n in targets do
      if let some i := maps.declToCmd.get? n then
        keepIdx := keepIdx.erase i

  let mut keptDeclSuffix : Array Nat := Array.replicate (pf.commands.size + 1) 0
  for off in [0:pf.commands.size] do
    let i := pf.commands.size - 1 - off
    let keepHere := if keepIdx.contains i then 1 else 0
    keptDeclSuffix := keptDeclSuffix.set! i (keptDeclSuffix[i + 1]! + keepHere)

  let hasKeptDeclBefore (afterIdx scopeEnd : Nat) : Bool :=
    keptDeclSuffix[afterIdx + 1]! > keptDeclSuffix[scopeEnd]!

  let mut keepScopeStarts : Std.HashSet Nat := {}
  for i in [0:pf.commands.size] do
    let cmd := pf.commands[i]!
    if isScopeStartCmd cmd then
      let scopeEnd := scopes.startToEnd.getD i pf.commands.size
      if hasKeptDeclBefore i scopeEnd then
        keepScopeStarts := keepScopeStarts.insert i

  let mut out : Array RetainedCmd := #[]
  for i in [0:pf.commands.size] do
    let cmd := pf.commands[i]!
    if isDeclarationLikeCmd cmd then
      if keepIdx.contains i then
        let cmd := if isTheoremLikeCmd cmd || isInstanceCmd cmd then
          stubProof sorryDeclVal sorryInstanceVal cmd
        else
          cmd
        out := out.push { originalIdx := i, kind := .decl, cmd := cmd }
    else
      if isScopeStartCmd cmd then
        if keepScopeStarts.contains i then
          out := out.push { originalIdx := i, kind := .scopeStart, cmd := cmd }
      else if isScopeEndCmd cmd then
        if let some startIdx := scopes.endToStart.get? i then
          if keepScopeStarts.contains startIdx then
            out := out.push { originalIdx := i, kind := .scopeEnd, cmd := cmd }
      else if !isDroppedNonDeclCmd pf cmd then
        let scopeEnd := scopes.cmdScopeEnd[i]!
        if hasKeptDeclBefore i scopeEnd then
          out := out.push { originalIdx := i, kind := .context, cmd := cmd }

  return out

end ProofRemover
