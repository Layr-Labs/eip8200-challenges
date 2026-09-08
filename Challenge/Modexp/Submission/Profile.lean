import Challenge.Modexp.Scorer

open EvmSemantics Challenge.Modexp Challenge.Modexp.Scorer

/-- Diagnostic opcode profile using the same pinned executable semantics as the scorer. -/
def main (args : List String) : IO Unit := do
  let code := Hex.hexToBytes (← IO.FS.readFile "Challenge/Modexp/Submission/bytecode.hex").trimAscii.copy
  let mut costs := Array.replicate code.size 0
  let mut counts := Array.replicate code.size 0
  for vector in vectors do
    let mut state := initialState code vector.input scoringGas
    if args.contains "--dirty" then
      let account := state.accountMap deployAddress
      let accounts := state.accountMap.set deployAddress
        { account with storage := account.storage.set 0 0xdeadbeef
                       tstorage := account.tstorage.set 0 7 }
      state := { state with accountMap := accounts
                            substate := { state.substate with originalAccountMap := accounts }
                            executionEnv := { state.executionEnv with weiValue := 0x1234 } }
    let mut fuel := scoringFuel
    while !state.isDone && fuel > 0 do
      let next := EVM.stepF state
      let pc := state.pc.toNat
      costs := costs.modify pc (· + (state.gasAvailable - next.gasAvailable))
      counts := counts.modify pc (· + 1)
      state := next
      fuel := fuel - 1
    unless state.halt == .Returned && state.hReturn == spec vector.input do
      throw (IO.userError s!"execution failed: {vector.label}")
  let ranked := (Array.range code.size).qsort (fun a b => costs[a]! > costs[b]!)
  IO.println "pc,opcode,count,gas"
  for pc in ranked[:40] do
    IO.println s!"{pc},{code[pc]!},{counts[pc]!},{costs[pc]!}"
  IO.println s!"totalGas={costs.foldl (· + ·) 0},vectors={vectors.length}"
