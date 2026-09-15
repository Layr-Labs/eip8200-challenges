import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace RootE3PhaseRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel

/-- Generic carrier: memory is arbitrary, including arbitrary bytes outside the copied region. -/
def frame (s : State) (mem : ByteArray) (pc : Nat) (stack : List UInt256) : State :=
  { s with memory := mem, pc := UInt256.ofNat pc, stack := stack }

def phaseGuardProgram : List Instr :=
  [.push 2 1760, .op .MLOAD, .op .ISZERO, .push 2 3332, .op .JUMPI]

def phaseExitHeadProgram : List Instr := [.op .JUMPDEST, .op .POP]

def phaseSwitchProgram : List Instr :=
  [.push 0 0, .push 2 1760, .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩), .push 2 2112, .push 2 256, .op .MCOPY,
   .op (.Dup ⟨1, by decide⟩), .push 1 2, .op .SHR, .push 2 2836, .op .JUMP]

/-- The flag is cleared before MCOPY reads the retained accumulator at 2112. -/
def phaseSwitchMemory (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.mcopyMem (Exp.storeWord mem 1760 (UInt256.ofNat 0)) 256 2112 (32 * n)

private theorem run_phaseGuard (s : State) (mem : ByteArray) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 3332 = true) :
    runInstructions phaseGuardProgram (frame s mem 3302 rest) =
      some (frame s mem (if (MachineState.readWord mem 1760).toNat = 0 then 3332 else 3311) rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hactive := Exp.activeWords_fix s 1760 32 (by decide) (by decide) hact
  by_cases hv : (MachineState.readWord mem 1760).toNat = 0 <;>
    simp [runInstructions, phaseGuardProgram, frame, Challenge.EvmProof.Stepper.runInstr,
      hcap0, hcap1, hcap2, State.activeWordsAfterUInt256, hactive,
      WindowTwentyOneEntry.isTrue_isZero, hv, hdest,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_phaseGuardZero (s : State) (mem : ByteArray) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 0)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 3332 = true) :
    runInstructions phaseGuardProgram (frame s mem 3302 rest) =
      some (frame s mem 3332 rest) := by
  simpa [hflag] using run_phaseGuard s mem rest hrest hact hdest

theorem run_phaseGuardOne (s : State) (mem : ByteArray) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 1)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 3332 = true) :
    runInstructions phaseGuardProgram (frame s mem 3302 rest) =
      some (frame s mem 3311 rest) := by
  simpa [hflag] using run_phaseGuard s mem rest hrest hact hdest

theorem run_phaseExitHead (s : State) (mem : ByteArray) (value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions phaseExitHeadProgram (frame s mem 3300 (value :: rest)) =
      some (frame s mem 3302 rest) := by
  have hcap : rest.length + 1 < 1024 := by omega
  simp [runInstructions, phaseExitHeadProgram, frame, Challenge.EvmProof.Stepper.runInstr,
    hcap, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_phaseSwitch (s : State) (mem : ByteArray) (n : Nat) (rest : List UInt256)
    (hn : n = 4 ∨ n = 8) (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 2836 = true) :
    runInstructions phaseSwitchProgram
      (frame s mem 3311 ([UInt256.ofNat (32 * n), UInt256.ofNat n] ++ rest)) =
      some (frame s (phaseSwitchMemory mem n) 2836
        ([UInt256.ofNat (n / 4), UInt256.ofNat (32 * n), UInt256.ofNat n] ++ rest)) := by
  have hn1 : 1 ≤ n := by omega
  have hn8 : n ≤ 8 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hs32 : (UInt256.ofNat (32 * n)).toNat = 32 * n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hquarter : UInt256.shiftRight (UInt256.ofNat n) (UInt256.ofNat 2) =
      UInt256.ofNat (n / 4) := by
    rcases hn with rfl | rfl <;> decide
  have hactive1 := Exp.activeWords_fix s 1760 32 (by decide) (by decide) hact
  have hactive2 := Exp.activeWords_fix2 s 256 (32 * n) 2112 (32 * n)
    (by omega) (by omega) (by omega) (by omega) hact
  simp [runInstructions, phaseSwitchProgram, phaseSwitchMemory, frame,
    Challenge.EvmProof.Stepper.runInstr, Exp.storeWord, Exp.mcopyMem,
    hcap2, hcap3, hcap4, hcap5, hs32, hquarter, hdest, Exp.push0_word,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, hactive1, hactive2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

#print axioms run_phaseGuardZero
#print axioms run_phaseGuardOne
#print axioms run_phaseExitHead
#print axioms run_phaseSwitch

/-- Exact relocated guard bytes at PCs 3495 through 3503. -/
theorem phaseGuardProgram_assembly : assemble phaseGuardProgram =
    ByteArray.mk #[0x61, 0x06, 0xe0, 0x51, 0x15, 0x61, 0x0d, 0x04, 0x57] := by rfl

/-- Exact relocated switch bytes at PCs 3515 through 3526; PUSH0 uses Instr.push0. -/
theorem phaseSwitchProgram_assembly : assemble phaseSwitchProgram =
    ByteArray.mk #[0x5f, 0x61, 0x06, 0xe0, 0x52, 0x80, 0x61, 0x08, 0x40, 0x61, 0x01, 0x00, 0x5e, 0x81, 0x60, 0x02, 0x1c, 0x61, 0x0b, 0x14, 0x56] := by rfl

def phaseDoneProgram : List Instr := [.op .JUMPDEST]

theorem run_phaseDone (s : State) (mem : ByteArray) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions phaseDoneProgram (frame s mem 3332 rest) =
      some (frame s mem 3333 rest) := by
  have hcap : rest.length < 1024 := by omega
  simp [runInstructions, phaseDoneProgram, frame, Challenge.EvmProof.Stepper.runInstr,
    hcap, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_phaseExitZero (s : State) (mem : ByteArray) (value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 0)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 3332 = true) :
    runInstructions (phaseExitHeadProgram ++ phaseGuardProgram)
      (frame s mem 3300 (value :: rest)) = some (frame s mem 3332 rest) := by
  rw [runInstructions_append, run_phaseExitHead s mem value rest hrest]
  exact run_phaseGuardZero s mem rest hrest hact hflag hdest

theorem run_phaseExitOne (s : State) (mem : ByteArray) (value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 1)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 3332 = true) :
    runInstructions (phaseExitHeadProgram ++ phaseGuardProgram)
      (frame s mem 3300 (value :: rest)) = some (frame s mem 3311 rest) := by
  rw [runInstructions_append, run_phaseExitHead s mem value rest hrest]
  exact run_phaseGuardOne s mem rest hrest hact hflag hdest

open Challenge.EvmProof WindowTwentyOneBinding

/-- MAIN supplies only these four artifact-location certificates.
The instruction indices are 2627/2629/2634/2646 respectively (exit head 3493, guard 3495, switch 3504, done 3525). -/
structure PhaseBlocks (artifact : ProgramArtifact) (fork : Fork) where
  exitHead : Block artifact fork 3300 phaseExitHeadProgram
  guard : Block artifact fork 3302 phaseGuardProgram
  switch : Block artifact fork 3311 phaseSwitchProgram
  done : Block artifact fork 3332 phaseDoneProgram

def PhaseBlocks.guardZeroSteps {artifact : ProgramArtifact} {fork : Fork}
    (blocks : PhaseBlocks artifact fork) (s : State) (mem : ByteArray)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 0)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 3332 = true)
    (env : Environment artifact fork (frame s mem 3302 rest)) :
    GasSteps (frame s mem 3302 rest) (frame s mem 3332 rest) :=
  blocks.guard.steps env rfl (run_phaseGuardZero s mem rest hrest hact hflag hdest)

def PhaseBlocks.guardOneSteps {artifact : ProgramArtifact} {fork : Fork}
    (blocks : PhaseBlocks artifact fork) (s : State) (mem : ByteArray)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 1)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 3332 = true)
    (env : Environment artifact fork (frame s mem 3302 rest)) :
    GasSteps (frame s mem 3302 rest) (frame s mem 3311 rest) :=
  blocks.guard.steps env rfl (run_phaseGuardOne s mem rest hrest hact hflag hdest)

def PhaseBlocks.switchSteps {artifact : ProgramArtifact} {fork : Fork}
    (blocks : PhaseBlocks artifact fork) (s : State) (mem : ByteArray)
    (n : Nat) (rest : List UInt256) (hn : n = 4 ∨ n = 8)
    (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 2836 = true)
    (env : Environment artifact fork
      (frame s mem 3311 ([UInt256.ofNat (32 * n), UInt256.ofNat n] ++ rest))) :
    GasSteps (frame s mem 3311 ([UInt256.ofNat (32 * n), UInt256.ofNat n] ++ rest))
      (frame s (phaseSwitchMemory mem n) 2836
        ([UInt256.ofNat (n / 4), UInt256.ofNat (32 * n), UInt256.ofNat n] ++ rest)) :=
  blocks.switch.steps env rfl (run_phaseSwitch s mem n rest hn hrest hact hdest)

#print axioms phaseGuardProgram_assembly
#print axioms phaseSwitchProgram_assembly
#print axioms run_phaseExitZero
#print axioms run_phaseExitOne
#print axioms PhaseBlocks.guardZeroSteps
#print axioms PhaseBlocks.guardOneSteps
#print axioms PhaseBlocks.switchSteps
end RootE3PhaseRun
