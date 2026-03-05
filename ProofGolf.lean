/-
# Proof Golf — Measuring Proof Complexity

Custom `#golf` command that wraps `example` or `theorem` declarations and reports:
1. **Source score**: non-whitespace characters in the proof body
2. **Heartbeats**: deterministic measure of elaboration cost
3. **Term score**: Expr node count of the elaborated proof term
4. **PP length**: character count of the pretty-printed proof term
5. **Axioms**: foundational axioms transitively used by the proof
-/

import Lean

open Lean Elab Command Term Meta

/-- Count non-whitespace characters, ignoring `;` (tactic separator) but keeping `<;>` (combinator) -/
def golfScore (s : String) : Nat :=
  go s.toList 0
where
  go : List Char → Nat → Nat
    | '<' :: ';' :: '>' :: rest, n => go rest (n + 3)
    | ';' :: rest, n => go rest n
    | c :: rest, n => go rest (if c.isWhitespace then n else n + 1)
    | [], n => n

/-- Recursively find a syntax node of a given kind -/
partial def Lean.Syntax.findKind (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == k then some stx
  else match stx with
    | .node _ _ args => args.findSome? (·.findKind k)
    | _ => none

/-- Try to extract a declaration name from a command syntax -/
def getDeclName? (cmd : Syntax) : Option Name :=
  if let some declId := cmd.findKind ``Lean.Parser.Command.declId then
    if declId.getNumArgs > 0 then
      let nameStx := declId.getArg 0
      if nameStx.isIdent then some nameStx.getId else none
    else none
  else none

/-- Format term-level measurements as a suffix string -/
def formatTermInfo (val : Expr) (axioms : Array Name) : CommandElabM String := do
  let nodes := val.sizeWithoutSharing
  let ppLen ← liftTermElabM do
    let fmt ← ppExpr val
    return fmt.pretty.length
  let axiomStr := if axioms.isEmpty then "none"
    else s!"{axioms.size} ({", ".intercalate (axioms.map (·.toString)).toList})"
  return s!" | term: {nodes} nodes | pp: {ppLen} chars | axioms: {axiomStr}"

/-- `#golf` wraps a declaration and reports proof complexity.

- Source score: non-whitespace characters in the proof (after `:= by` or `:=`)
- Heartbeats: deterministic elaboration cost (matches `maxHeartbeats` units)
- Term score: Expr nodes in the elaborated proof term
- PP length: character count of the pretty-printed proof term
- Axioms: foundational axioms transitively used by the proof

Works for both `example` and named declarations (`theorem`, `def`).

```
#golf example (P : Prop) : P → P := by exact id
-- Golf: 7 chars | 3 heartbeats | term: 5 nodes | pp: 11 chars | axioms: none

#golf theorem myThm (P : Prop) : P → P := by exact id
-- Golf: 7 chars | 3 heartbeats | term: 5 nodes | pp: 11 chars | axioms: none
```
-/
elab "#golf " cmd:command : command => do
  let (_, heartbeats) ← withHeartbeats (elabCommand cmd)
  let hb := heartbeats / 1000
  -- Source-level measurement
  let some valStx := cmd.raw.findKind ``Lean.Parser.Command.declValSimple
    | logInfo "Could not find proof body"; return
  let proofStx :=
    match valStx.findKind ``Lean.Parser.Tactic.tacticSeq with
    | some tseq => tseq
    | none => if valStx.getNumArgs > 1 then valStx.getArg 1 else valStx
  let fileMap ← getFileMap
  let some startPos := proofStx.getPos?
    | logInfo "Could not get start position"; return
  let some endPos := proofStx.getTailPos?
    | logInfo "Could not get end position"; return
  let src := (Substring.Raw.mk fileMap.source startPos endPos).toString
  let charScore := golfScore src
  -- Term-level measurement
  let termInfo ← do
    if let some declName := getDeclName? cmd.raw then
      -- Named declaration: look up term directly
      let env ← getEnv
      if let some ci := env.find? declName then
        if let some val := ci.value? then
          let axioms ← collectAxioms declName
          formatTermInfo val axioms
        else pure ""
      else pure ""
    else if let some exNode := cmd.raw.findKind ``Lean.Parser.Command.example then
      -- Example: elaborate a synthetic def to capture the proof term
      let some exStart := exNode.getPos? | pure ""
      let some exEnd := exNode.getTailPos? | pure ""
      let exSrc := (Substring.Raw.mk fileMap.source exStart exEnd).toString
      if !exSrc.startsWith "example" then pure ""
      else
        let defSrc := "noncomputable def _golf_tmp" ++ exSrc.drop 7
        let env ← getEnv
        match Parser.runParserCategory env `command defSrc "<golf>" with
        | .error _ => pure ""
        | .ok stx =>
          withoutModifyingEnv do
            try
              elabCommand stx
              let env ← getEnv
              let ns ← getCurrNamespace
              let qualName := if ns.isAnonymous then `_golf_tmp else ns ++ `_golf_tmp
              if let some ci := env.find? qualName then
                if let some val := ci.value? then
                  let axioms ← collectAxioms qualName
                  formatTermInfo val axioms
                else pure ""
              else pure ""
            catch _ => pure ""
    else pure ""
  logInfo m!"Golf: {charScore} chars | {hb} heartbeats{termInfo}"
