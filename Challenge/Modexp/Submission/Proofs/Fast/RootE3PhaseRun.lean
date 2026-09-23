import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Fast.ShiftStates

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

/-- The phase-exit head at pc 3346 (idx 2696): drop the spent loop counter. -/
def phaseExitHeadProgram : List Instr := [.op .JUMPDEST, .op .POP]

/-- The phase test at pc 3348 (idx 2698): with the squaring flag clear the guard
jumps straight to the cleanup tail at 5444; otherwise it falls through into the
switch at 3357. -/
def phaseGuardProgram : List Instr :=
  [.push 2 1760, .op .MLOAD, .op .ISZERO, .push 2 5444, .op .JUMPI]

/-- The phase switch at pc 3357 (idx 2703): clear the flag, publish the retained
accumulator into `ACC` (`MCOPY 256 <- 2112`, length the `bsize` ride slot via
`DUP15`), then take the loop counter from the `n` ride slot (`DUP14`) shifted
down two bits and jump back to the shift loop head at 2811. -/
def phaseSwitchProgram : List Instr :=
  [.push 0 0, .push 2 1760, .op .MSTORE,
   .op (.Dup ⟨14, by decide⟩), .push 2 2112, .push 2 256, .op .MCOPY,
   .op (.Dup ⟨13, by decide⟩), .push 1 2, .op .SHR, .push 2 2811, .op .JUMP]

/-- The flag is cleared before MCOPY reads the retained accumulator at 2112. -/
def phaseSwitchMemory (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.mcopyMem (Exp.storeWord mem 1760 (UInt256.ofNat 0)) 256 2112 (32 * n)

private theorem run_phaseGuard (s : State) (mem : ByteArray) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 5444 = true) :
    runInstructions phaseGuardProgram (frame s mem 3348 rest) =
      some (frame s mem (if (MachineState.readWord mem 1760).toNat = 0 then 5444 else 3357) rest) := by
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
    (hdest : Decode.isValidJumpDest s.executionEnv.code 5444 = true) :
    runInstructions phaseGuardProgram (frame s mem 3348 rest) =
      some (frame s mem 5444 rest) := by
  simpa [hflag] using run_phaseGuard s mem rest hrest hact hdest

theorem run_phaseGuardOne (s : State) (mem : ByteArray) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 1)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 5444 = true) :
    runInstructions phaseGuardProgram (frame s mem 3348 rest) =
      some (frame s mem 3357 rest) := by
  simpa [hflag] using run_phaseGuard s mem rest hrest hact hdest

theorem run_phaseExitHead (s : State) (mem : ByteArray) (value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions phaseExitHeadProgram (frame s mem 3346 (value :: rest)) =
      some (frame s mem 3348 rest) := by
  have hcap : rest.length + 1 < 1024 := by omega
  simp [runInstructions, phaseExitHeadProgram, frame, Challenge.EvmProof.Stepper.runInstr,
    hcap, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_phaseSwitch (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (rest : List UInt256)
    (hn : n = 4 ∨ n = 8) (hbs : bsize = 32 * n)
    (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hstack : rest =
      Shift.entrySlots mem n bsize esize ++ Exp.outer n bsize esize msize)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 2811 = true) :
    runInstructions phaseSwitchProgram
      (frame s mem 3357 rest) =
      some (frame s (phaseSwitchMemory mem n) 2811
        (UInt256.ofNat (n / 4) :: Shift.entrySlots mem n bsize esize ++
          Exp.outer n bsize esize msize)) := by
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
  have ha2 : 32 * n ≠ 0 := by omega
  have ha3 : 256 + 32 * n ≤ 2848 := by omega
  have ha4 : 2112 + 32 * n ≤ 2848 := by omega
  have hactive2 := Exp.activeWords_fix2 s 256 (32 * n) 2112 (32 * n) ha2 ha2 ha3 ha4 hact
  simp [runInstructions, phaseSwitchProgram, phaseSwitchMemory, frame,
    Challenge.EvmProof.Stepper.runInstr, Exp.storeWord, Exp.mcopyMem,
    hstack, hbs, Shift.entrySlots, Shift.rideSlots, Exp.outer,
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

open Challenge.EvmProof WindowTwentyOneBinding

/-- MAIN supplies only these three artifact-location certificates: the exit
head at idx 2696 (pc 3346), the guard at idx 2698 (pc 3348) and the switch at
idx 2703 (pc 3357). -/
structure PhaseBlocks (artifact : ProgramArtifact) (fork : Fork) where
  exitHead : Block artifact fork 3346 phaseExitHeadProgram
  guard : Block artifact fork 3348 phaseGuardProgram
  switch : Block artifact fork 3357 phaseSwitchProgram

def PhaseBlocks.guardZeroSteps {artifact : ProgramArtifact} {fork : Fork}
    (blocks : PhaseBlocks artifact fork) (s : State) (mem : ByteArray)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 0)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 5444 = true)
    (env : Environment artifact fork (frame s mem 3348 rest)) :
    GasSteps (frame s mem 3348 rest) (frame s mem 5444 rest) :=
  blocks.guard.steps env rfl (run_phaseGuardZero s mem rest hrest hact hflag hdest)

def PhaseBlocks.guardOneSteps {artifact : ProgramArtifact} {fork : Fork}
    (blocks : PhaseBlocks artifact fork) (s : State) (mem : ByteArray)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 1)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 5444 = true)
    (env : Environment artifact fork (frame s mem 3348 rest)) :
    GasSteps (frame s mem 3348 rest) (frame s mem 3357 rest) :=
  blocks.guard.steps env rfl (run_phaseGuardOne s mem rest hrest hact hflag hdest)

def PhaseBlocks.switchSteps {artifact : ProgramArtifact} {fork : Fork}
    (blocks : PhaseBlocks artifact fork) (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) (rest : List UInt256) (hn : n = 4 ∨ n = 8)
    (hbs : bsize = 32 * n)
    (hrest : rest.length ≤ 1000) (hact : 89 ≤ s.activeWords.toNat)
    (hstack : rest =
      Shift.entrySlots mem n bsize esize ++ Exp.outer n bsize esize msize)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 2811 = true)
    (env : Environment artifact fork (frame s mem 3357 rest)) :
    GasSteps (frame s mem 3357 rest)
      (frame s (phaseSwitchMemory mem n) 2811
        (UInt256.ofNat (n / 4) :: Shift.entrySlots mem n bsize esize ++
          Exp.outer n bsize esize msize)) :=
  blocks.switch.steps env rfl (run_phaseSwitch s mem n bsize esize msize rest hn hbs hrest hact hstack hdest)

#print axioms PhaseBlocks.guardZeroSteps
#print axioms PhaseBlocks.guardOneSteps
#print axioms PhaseBlocks.switchSteps
end RootE3PhaseRun
