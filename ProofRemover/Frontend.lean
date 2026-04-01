import Lean
import Lean.Parser.Module
import Lean.Elab.Import
import Lean.Elab.Frontend
import Lean.Util.Path

namespace ProofRemover

open Lean

structure ParsedFile where
  input        : String
  path         : System.FilePath
  fileName     : String
  fileMap      : FileMap
  header       : TSyntax ``Parser.Module.header
  headerEndPos : String.Pos.Raw
  commands     : Array Syntax
  env          : Environment
  opts         : Options

def parseAndElab (path : System.FilePath) (opts : Options := {}) : IO ParsedFile := do
  let input ← IO.FS.readFile path
  let fileName := path.toString
  let inputCtx := Parser.mkInputContext input fileName

  let (header, parserState, headerMsgs) ← Parser.parseHeader inputCtx
  if headerMsgs.hasErrors then
    let lines ← headerMsgs.toList.mapM fun m => MessageData.toString m.data
    throw <| IO.userError s!"header parse failed:\n{String.intercalate "\n" lines}"

  -- Match Lean's module naming as closely as we can. This matters for private name mangling.
  let mainModuleName ←
    try
      Lean.moduleNameOfFileName path none
    catch _ =>
      pure <| Name.mkSimple <| (path.fileStem.getD "Main")

  let (env0, msgs0) ← Elab.processHeader header opts headerMsgs inputCtx (mainModule := mainModuleName)
  if msgs0.hasErrors then
    let lines ← msgs0.toList.mapM fun m => MessageData.toString m.data
    throw <| IO.userError s!"import/elab header failed:\n{String.intercalate "\n" lines}"

  let cmdState0 := Elab.Command.mkState env0 msgs0 opts
  let frontendCtx : Lean.Elab.Frontend.Context := { inputCtx := inputCtx }
  let frontendSt : Lean.Elab.Frontend.State := {
    commandState := cmdState0
    parserState  := parserState
    cmdPos       := parserState.pos
    commands     := #[]
  }
  let (_, st) ← (Lean.Elab.Frontend.processCommands).run frontendCtx |>.run frontendSt
  let env := st.commandState.env
  let msgs := st.commandState.messages
  if msgs.hasErrors then
    let lines ← msgs.toList.mapM fun m => MessageData.toString m.data
    throw <| IO.userError s!"command elaboration failed:\n{String.intercalate "\n" lines}"

  let finalOpts := st.commandState.scopes.head!.opts
  return {
    input
    path
    fileName
    fileMap := inputCtx.fileMap
    header
    headerEndPos := parserState.pos
    commands := st.commands
    env
    opts := finalOpts
  }

end ProofRemover
