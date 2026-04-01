import Lean
import ProofRemover.Frontend
import ProofRemover.Slice

namespace ProofRemover

open Lean

structure HeaderParts where
  fixedLines  : Array String
  importLines : Array String

/-- Remove all Lean comments from a string: block comments `/- ... -/` (nested) and
    line comments `-- ...`. Handles string literals to avoid false matches. -/
partial def stripLeanComments (s : String) : String := Id.run do
  let mut out : String := ""
  let mut i : String.Pos.Raw := 0
  let len := s.rawEndPos
  while i < len do
    let c := i.get s
    let next := i.next s
    -- String literal: skip to closing quote
    if c == '\"' then
      out := out.push c
      let mut j := next
      while j < len do
        let d := j.get s
        out := out.push d
        if d == '\\' then
          let j2 := j.next s
          if j2 < len then
            out := out.push (j2.get s)
            j := j2.next s
          else
            j := j2
        else if d == '\"' then
          j := j.next s
          break
        else
          j := j.next s
      i := j
    -- Block comment: skip including nested
    else if c == '/' && next < len && next.get s == '-' then
      let mut j := next.next s  -- past "/-"
      let mut depth : Nat := 1
      while j < len && depth > 0 do
        let d := j.get s
        let jn := j.next s
        if d == '/' && jn < len && jn.get s == '-' then
          depth := depth + 1
          j := jn.next s
        else if d == '-' && jn < len && jn.get s == '/' then
          depth := depth - 1
          j := jn.next s
        else
          j := jn
      i := j
    -- Line comment: skip to end of line
    else if c == '-' && next < len && next.get s == '-' then
      let mut j := next.next s
      while j < len && j.get s != '\n' do
        j := j.next s
      i := j
    else
      out := out.push c
      i := next
  return out

/-- Collapse runs of 3+ newlines into exactly 2 (one blank line) and trim trailing
    whitespace on each line. -/
def collapseBlankLines (s : String) : String := Id.run do
  let lines := s.splitOn "\n"
  let trimmed := lines.map (fun line => line.trimAsciiEnd.toString)
  let joined := "\n".intercalate trimmed
  -- Collapse runs of 3+ newlines into 2
  let mut out : String := ""
  let mut nlCount : Nat := 0
  for c in joined.toList do
    if c == '\n' then
      nlCount := nlCount + 1
      if nlCount <= 2 then
        out := out.push c
    else
      nlCount := 0
      out := out.push c
  return out

def ppCommandToString (pf : ParsedFile) (cmd : Syntax) : IO String := do
  let core : CoreM String := do
    let fmt ← PrettyPrinter.ppCommand (⟨cmd⟩ : Syntax.Command)
    return fmt.pretty
  let ctx : Core.Context := { fileName := pf.fileName, fileMap := pf.fileMap, options := pf.opts }
  let st : Core.State := { env := pf.env }
  let (s, _) ← core.toIO ctx st
  return s

private def originalCommandText? (pf : ParsedFile) (cmd : Syntax) : Option String :=
  cmd.getRange? (canonicalOnly := true) |>.map fun r =>
    stripLeanComments (String.Pos.Raw.extract pf.input r.start r.stop)

def commandText (pf : ParsedFile) (cmd : Syntax) : IO String := do
  try
    stripLeanComments <$> ppCommandToString pf cmd
  catch e =>
    if !isTheoremLikeCmd cmd then
      if let some text := originalCommandText? pf cmd then
        return text
    throw e

def headerParts (pf : ParsedFile) : HeaderParts := Id.run do
  let headerText := stripLeanComments (String.Pos.Raw.extract pf.input 0 pf.headerEndPos)
  let mut fixedLines : Array String := #[]
  let mut importLines : Array String := #[]
  for line in headerText.splitOn "\n" do
    let trimmed := line.trimAscii
    if trimmed.isEmpty then
      continue
    let lineText := trimmed.toString
    if lineText.startsWith "import " then
      importLines := importLines.push lineText
    else
      fixedLines := fixedLines.push lineText
  return { fixedLines, importLines }

def headerTextFromParts (parts : HeaderParts) : String :=
  "\n".intercalate <| (parts.fixedLines ++ parts.importLines).toList

def renderCommandTexts (pf : ParsedFile) (cmds : Array RetainedCmd) : IO (Array String) := do
  let mut parts : Array String := #[]
  for i in [0:cmds.size] do
    let retained := cmds[i]!
    let cmd := retained.cmd
    try
      let s ← commandText pf cmd
      parts := parts.push s
    catch e =>
      throw <| IO.userError s!"pretty printing failed at retained command #{i} (source #{retained.originalIdx}, kind `{cmd.getKind}`): {e}"
  return parts

def buildOutputText (headerText : String) (bodyParts : Array String) : String :=
  let bodyText := "\n\n".intercalate bodyParts.toList
  let outText :=
    if headerText.isEmpty then
      bodyText ++ "\n"
    else if bodyText.isEmpty then
      headerText ++ "\n"
    else
      headerText ++ "\n\n" ++ bodyText ++ "\n"
  (collapseBlankLines outText).trimAsciiStart.toString

def writeOutputText (outPath : System.FilePath) (text : String) : IO Unit :=
  IO.FS.writeFile outPath text

def emitSlicedFile (pf : ParsedFile) (cmds : Array RetainedCmd) (outPath : System.FilePath)
    (parts : HeaderParts := headerParts pf) : IO Unit := do
  let bodyParts ← renderCommandTexts pf cmds
  writeOutputText outPath <| buildOutputText (headerTextFromParts parts) bodyParts

private def leanCmdPath : IO System.FilePath := do
  return (← Lean.findSysroot) / "bin" / "lean"

def verifyWithLean? (outPath : System.FilePath) : IO (Option String) := do
  let leanCmd ← leanCmdPath
  let r ← IO.Process.output { cmd := leanCmd.toString, args := #[outPath.toString] }
  if r.exitCode != 0 then
    let details :=
      if !r.stderr.trimAscii.toString.isEmpty then r.stderr
      else r.stdout
    return some s!"Lean failed on {outPath}:\n{details}"
  return none

def verifyWithLean (outPath : System.FilePath) : IO Unit := do
  if let some details ← verifyWithLean? outPath then
    throw <| IO.userError details

end ProofRemover
