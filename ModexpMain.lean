import Challenge.Modexp.Scorer
import YulParser.Compile
set_option warningAsError true

open EvmSemantics
open Challenge.Modexp
open Challenge.Modexp.Scorer

private def hexToBytes? (text : String) : Option ByteArray :=
  let text := (if text.startsWith "0x" then text.drop 2 else text).trimAscii.copy
  let text := text.replace "\n" "" |>.replace " " ""
  if text.length % 2 != 0 then none
  else if !text.all fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') then none
  else some (Hex.hexToBytes text)

def main (args : List String) : IO UInt32 := do
  if args = ["--print-reference-hex"] then
    IO.println (Hex.bytesToHex referenceBytecode)
    return 0
  let hexPath := args.findSome? fun arg =>
    if arg.startsWith "--hex=" then some (arg.drop 6).copy else none
  let yulPath := args.findSome? fun arg =>
    if arg.startsWith "--yul=" then some (arg.drop 6).copy else none
  let (name, code) : System.FilePath × ByteArray ← match hexPath, yulPath with
    | some _, some _ => do IO.eprintln "choose one of --hex or --yul"; return 64
    | some path, none =>
        match hexToBytes? (← IO.FS.readFile path) with
        | some bytes => pure (path, bytes)
        | none => do IO.eprintln s!"{path}: invalid hex"; return 64
    | none, maybePath =>
        let path := maybePath.getD referenceSourcePath
        match YulParser.compileSource (← IO.FS.readFile path) with
        | some bytes => pure (System.FilePath.mk path, bytes)
        | none => do IO.eprintln s!"{path}: compiler rejected source"; return 2

  IO.println s!"== {name} ==\nbytecode: {code.size} bytes"
  let mut failures := 0
  for vector in vectors do
    match score code vector.input with
    | .ok gas => IO.println s!"{vector.label}: ok ({gas} gas)"
    | .wrongResult got expected gas =>
        failures := failures + 1
        IO.println s!"{vector.label}: WRONG ({gas} gas)\n  got {got}\n  expected {expected}"
    | .badHalt halt gas =>
        failures := failures + 1
        IO.println s!"{vector.label}: HALTED {halt} ({gas} gas)"
    | .outOfFuel =>
        failures := failures + 1
        IO.println s!"{vector.label}: OUT OF FUEL"
  IO.println (if failures = 0 then "Tier 1: PASS" else s!"Tier 1: FAIL — {failures} vector(s)")
  return if failures = 0 then 0 else 1
