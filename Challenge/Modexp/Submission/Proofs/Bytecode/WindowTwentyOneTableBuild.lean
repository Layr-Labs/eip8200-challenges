import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTablePrelude

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTableBuild

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel WindowTwentyOneMsize

/-- Every `MSIZE`-addressed update is five bytes: `DUPk MULMOD DUP1 MSIZE MSTORE`. -/
def tablePC (power : Nat) : Nat := 858 + 5 * power

private theorem updatePC (power : Nat) (hlo : 2 ≤ power) (hhi : power < 15) :
    WindowTwentyOneTable.storePCM (advancePC 2 (UInt256.ofNat (tablePC power))) =
      UInt256.ofNat (tablePC (power + 1)) := by
  interval_cases power <;> decide

theorem run_one (template : State) (base modulus exponent : UInt256)
    (power : Nat) (hlo : 2 ≤ power) (hhi : power < 15)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX (WindowTwentyOneTable.updateProgramM power hlo)
      (WindowTwentyOneTable.state template (UInt256.ofNat (tablePC power)) base modulus exponent power rest) =
    some (WindowTwentyOneTable.state template (UInt256.ofNat (tablePC (power + 1)))
      base modulus exponent (power + 1) rest) := by
  have h := WindowTwentyOneTable.run_updateM template (UInt256.ofNat (tablePC power))
    base modulus exponent power hlo hhi rest hrest
  simpa only [updatePC power hlo hhi] using h

def buildProgram : Nat → List Instr
  | 0 => []
  | count + 1 => buildProgram count ++
      WindowTwentyOneTable.updateProgramM (count + 2) (by omega)

theorem run_build (template : State) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count ≤ 13)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX (buildProgram count)
      (WindowTwentyOneTable.state template (UInt256.ofNat 868) base modulus exponent 2 rest) =
    some (WindowTwentyOneTable.state template (UInt256.ofNat (tablePC (count + 2)))
      base modulus exponent (count + 2) rest) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have h := run_one template base modulus exponent (count + 2) (by omega) (by omega) rest hrest
      have both := runInstructionsX_append_some _ _ _ _ _ (ih (by omega)) h
      simpa only [buildProgram, show count + 2 + 1 = count + 1 + 2 by omega] using both

def program : List Instr :=
  WindowTwentyOneTablePrelude.program ++ buildProgram 12 ++ WindowTwentyOneTable.lastUpdateProgramM

/-- The complete table construction from 1792 to 1884, including the exponent load. -/
theorem run_all (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hexp : rest[1]? = some exponent) :
    runInstructionsX program
      (WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 840) base modulus rest) =
    some (WindowTwentyOneTable.framed template (UInt256.ofNat 932) base modulus 16
      ([base, exponent] ++ rest)) := by
  have hp := WindowTwentyOneTablePrelude.run_prelude template (UInt256.ofNat 840)
    base modulus exponent rest hrest hexp
  have hpc : WindowTwentyOneTablePrelude.endPC (UInt256.ofNat 840) = UInt256.ofNat 868 := by decide
  rw [hpc] at hp
  have hb := run_build template base modulus exponent 12 (by decide) rest hrest
  have hl := WindowTwentyOneTable.run_last_updateM template (UInt256.ofNat (tablePC 14))
    base modulus exponent rest hrest
  have hlastPC : WindowTwentyOneTable.lastStorePCM (advancePC 2 (UInt256.ofNat (tablePC 14))) =
      UInt256.ofNat 932 := by decide
  rw [hlastPC] at hl
  exact runInstructionsX_append_some _ _ _ _ _ (runInstructionsX_append_some _ _ _ _ _ hp hb) hl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTableBuild
