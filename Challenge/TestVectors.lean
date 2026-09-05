import Lean.Data.Json
import EvmSemantics.Data.Hex

set_option warningAsError true

namespace Challenge.TestVectors

structure Vector where
  label : String
  input : ByteArray

private def parseHex (text : String) : Except String ByteArray := do
  let text := if text.startsWith "0x" then (text.drop 2).copy else text
  unless text.length % 2 == 0 && text.all (fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) do
    throw "expected an even-length hex string (optional 0x prefix)"
  return EvmSemantics.Hex.hexToBytes text

/-- Load a fixed suite and check its expected outputs against the pinned specification. -/
def load (path precompile : String) (spec : ByteArray → ByteArray)
    (valid : ByteArray → Bool := fun _ => true) : IO (List Vector) := do
  let text ← IO.FS.readFile path
  let parsed : Except String (List Vector) := do
    let root ← Lean.Json.parse text
    unless (← root.getObjValAs? String "precompile") == precompile do
      throw s!"expected precompile '{precompile}'"
    let rows ← root.getObjValAs? (Array Lean.Json) "vectors"
    if rows.isEmpty then throw "vectors must not be empty"
    let mut result : List Vector := []
    for row in rows do
      let label ← row.getObjValAs? String "label"
      if label.isEmpty || label.any (fun c => c == '\n' || c == '\r') then
        throw "label must be nonempty and single-line"
      if result.any (fun v : Vector => v.label == label) then throw s!"duplicate label '{label}'"
      let input ← parseHex (← row.getObjValAs? String "input")
      let expected ← parseHex (← row.getObjValAs? String "expected")
      unless valid input do throw s!"{label}: input outside supported challenge domain"
      unless expected == spec input do throw s!"{label}: expected output disagrees with pinned specification"
      result := { label, input } :: result
    return result.reverse
  match parsed with
    | .ok rows => pure rows
    | .error e => throw (IO.userError s!"{path}: {e}")

def csvLabel (label : String) : String :=
  if label.contains ',' || label.contains '"' then
    "\"" ++ label.replace "\"" "\"\"" ++ "\""
  else label

end Challenge.TestVectors
