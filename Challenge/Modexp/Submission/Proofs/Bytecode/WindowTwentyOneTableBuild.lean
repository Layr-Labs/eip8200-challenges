import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTablePrelude

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTableBuild

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def width (power : Nat) : Fin 33 := if power < 7 then 1 else 2

def tablePC (power : Nat) : Nat :=
  if power ≤ 7 then 2283 + 6 * power else 2276 + 7 * power

private theorem updatePC (power : Nat) (hlo : 2 ≤ power) (hhi : power < 15) :
    WindowTwentyOneTable.storePC (width power) (advancePC 2 (UInt256.ofNat (tablePC power))) =
      UInt256.ofNat (tablePC (power + 1)) := by
  interval_cases power <;> decide

theorem run_one (template : State) (base modulus exponent : UInt256)
    (power : Nat) (hlo : 2 ≤ power) (hhi : power < 15)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (WindowTwentyOneTable.updateProgram power hlo (width power))
      (WindowTwentyOneTable.state template (UInt256.ofNat (tablePC power)) base modulus exponent power rest) =
    some (WindowTwentyOneTable.state template (UInt256.ofNat (tablePC (power + 1)))
      base modulus exponent (power + 1) rest) := by
  have hw : 0 < (width power).val := by unfold width; split <;> decide
  have h := WindowTwentyOneTable.run_update template (UInt256.ofNat (tablePC power))
    base modulus exponent power hlo hhi (width power) hw rest hrest
  simpa only [updatePC power hlo hhi] using h

def buildProgram : Nat → List Instr
  | 0 => []
  | count + 1 => buildProgram count ++
      WindowTwentyOneTable.updateProgram (count + 2) (by omega) (width (count + 2))

theorem run_build (template : State) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count ≤ 13)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (buildProgram count)
      (WindowTwentyOneTable.state template (UInt256.ofNat 2295) base modulus exponent 2 rest) =
    some (WindowTwentyOneTable.state template (UInt256.ofNat (tablePC (count + 2)))
      base modulus exponent (count + 2) rest) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have h := run_one template base modulus exponent (count + 2) (by omega) (by omega) rest hrest
      have both := runInstructions_append_some _ _ _ _ _ (ih (by omega)) h
      simpa only [buildProgram, show count + 2 + 1 = count + 1 + 2 by omega] using both

def program : List Instr :=
  WindowTwentyOneTablePrelude.program ++ buildProgram 12 ++ WindowTwentyOneTable.lastUpdateProgram

/-- The complete 117-byte table construction, including the exponent load. -/
theorem run_all (template : State) (base modulus exponentOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hoffset : rest[4]? = some exponentOffset) :
    runInstructions program
      (WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 2264) base modulus rest) =
    some (WindowTwentyOneTable.framed template (UInt256.ofNat 2380) base modulus 16
      ([base, MachineState.readWord template.executionEnv.calldata exponentOffset.toNat] ++ rest)) := by
  have hp := WindowTwentyOneTablePrelude.run_prelude template (UInt256.ofNat 2264)
    base modulus exponentOffset rest hrest hoffset
  have hpc : WindowTwentyOneTablePrelude.endPC (UInt256.ofNat 2264) = UInt256.ofNat 2295 := by decide
  rw [hpc] at hp
  have hb := run_build template base modulus
    (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat) 12 (by decide) rest hrest
  have hl := WindowTwentyOneTable.run_last_update template (UInt256.ofNat (tablePC 14))
    base modulus (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat) rest hrest
  have hlastPC : WindowTwentyOneTable.lastStorePC 2 (advancePC 2 (UInt256.ofNat (tablePC 14))) =
      UInt256.ofNat 2380 := by decide
  rw [hlastPC] at hl
  exact runInstructions_append_some _ _ _ _ _ (runInstructions_append_some _ _ _ _ _ hp hb) hl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTableBuild
