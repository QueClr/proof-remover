import Lean
import Lean.Util.Path
import ProofRemover.Frontend
import ProofRemover.Slice
import ProofRemover.Emit

namespace ProofRemover

open Lean

private def usage : String :=
  "usage: proof-remover <input.lean> [--out <output.lean>] [--keep <declName>]... [--no-verify]\n"

structure CliConfig where
  inputPath  : System.FilePath
  outPath    : System.FilePath := "out.lean"
  keepDecls  : Array String := #[]
  verify     : Bool := true

private def parseDeclName (s : String) : Name :=
  let parts := s.splitOn "." |>.filter (fun p => !p.isEmpty && p != "_root_")
  parts.foldl (init := Name.anonymous) fun n part => Name.str n part

private def resolveKeepTargets (pf : ParsedFile) (maps : DeclMaps) (cfg : CliConfig) : IO (Array Name) := do
  if cfg.keepDecls.isEmpty then
    let some target := findLastTheoremLike? pf maps
      | throw <| IO.userError "could not find a theorem-like declaration in the file"
    return #[target]

  let mut seen : Std.HashSet Name := {}
  let mut targets : Array Name := #[]
  for raw in cfg.keepDecls do
    let target := parseDeclName raw
    let some cinfo := pf.env.find? target
      | throw <| IO.userError s!"unknown declaration passed to --keep: {raw}"
    if pf.env.isImportedConst target || !maps.declToCmd.contains target then
      throw <| IO.userError s!"--keep target is not a local declaration in this file: {raw}"
    match cinfo with
    | .thmInfo _ =>
        if !seen.contains target then
          seen := seen.insert target
          targets := targets.push target
    | _ =>
        throw <| IO.userError s!"--keep target is not theorem-like: {raw}"
  return targets

private def parseArgs (args : List String) : IO CliConfig := do
  let some input := args.head? | throw <| IO.userError usage
  let mut cfg : CliConfig := { inputPath := input }
  let mut rest := args.tail!
  while !rest.isEmpty do
    let a := rest.head!
    rest := rest.tail!
    match a with
    | "--out" =>
        let some p := rest.head? | throw <| IO.userError "missing value for --out"
        rest := rest.tail!
        cfg := { cfg with outPath := p }
    | "--keep" =>
        let some n := rest.head? | throw <| IO.userError "missing value for --keep"
        rest := rest.tail!
        cfg := { cfg with keepDecls := cfg.keepDecls.push n }
    | "--no-verify" =>
        cfg := { cfg with verify := false }
    | "--help" | "-h" =>
        throw <| IO.userError usage
    | _ =>
        throw <| IO.userError s!"unknown arg: {a}\n{usage}"
  return cfg

def run (args : List String) : IO Unit := do
  let cfg ← parseArgs args
  let pf ← parseAndElab cfg.inputPath
  let maps := buildDeclMaps pf
  let targets ← resolveKeepTargets pf maps cfg

  let needed := computeNeededDecls pf maps targets
  let sorryDeclVal ← mkSorryDeclVal pf.env
  let sorryInstanceVal ← mkSorryInstanceVal pf.env
  let cmds := sliceCommands pf maps needed sorryDeclVal sorryInstanceVal
  let parts := headerParts pf

  emitSlicedFile pf cmds cfg.outPath parts

  if cfg.verify then
    verifyWithLean cfg.outPath

end ProofRemover

def main (args : List String) : IO Unit :=
  do
    Lean.initSearchPath (← Lean.findSysroot)
    -- By default, Lean does *not* execute `initialize` code when importing `.olean` files.
    -- Many Mathlib tactics/options rely on those initializers having run.
    unsafe Lean.enableInitializersExecution
    ProofRemover.run args
