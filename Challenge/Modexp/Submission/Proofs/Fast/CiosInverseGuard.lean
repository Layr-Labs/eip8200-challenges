import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel WindowTwentyOneBinding

def stateAt (pc : Nat) (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat pc
    stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
    memory := mem }

def guardProgram : List Instr :=
  [.op .JUMPDEST, .push 2 2720, .op .MLOAD, .push 1 1, .op .EQ,
   .push 2 5300, .op .JUMPI]
def passProgram : List Instr := [.push 2 3561, .op .JUMP]
def fallbackProgram : List Instr := [.op .JUMPDEST, .op .POP, .push 2 1215, .op .JUMP]

def guardBlock : Block Artifact.submissionArtifact .Osaka 5284 guardProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4041 7 5284 guardProgram
    (by decide) (by rfl) (by rfl) (by decide)
def passBlock : Block Artifact.submissionArtifact .Osaka 5296 passProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4048 2 5296 passProgram
    (by decide) (by rfl) (by rfl) (by decide)
def fallbackBlock : Block Artifact.submissionArtifact .Osaka 5300 fallbackProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4050 4 5300 fallbackProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5284 = true :=
  Artifact.isValidJumpDest_index 4041 (by rfl)
theorem jumpDestFallback : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5300 = true :=
  Artifact.isValidJumpDest_index 4050 (by rfl)

theorem run_guardPass (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hact : 88 ≤ s.activeWords.toNat)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1) :
    runInstructions guardProgram (stateAt 5284 s mem hd pa pb pdst ret rest) =
      some (stateAt 5296 s mem hd pa pb pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hne : (UInt256.ofNat 1).toNat ≠ (MachineState.readWord mem 2720).toNat := by
    intro h
    apply hguard
    apply Challenge.EvmProof.Word.word_ext
    exact h.symm
  have hc : ¬ UInt256.isTrue ((UInt256.ofNat 1).eq (MachineState.readWord mem 2720)) := by
    rw [UInt256.eq, if_neg hne]
    decide
  have ha := Monpro.activeWords_fix s 2720 32 (by decide) (by omega) hact
  simp [guardProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    hc5, hc6, hc7, hc, State.activeWordsAfterUInt256, ha,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_guardFallback (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hguard : MachineState.readWord mem 2720 = UInt256.ofNat 1) :
    runInstructions guardProgram (stateAt 5284 s mem hd pa pb pdst ret rest) =
      some (stateAt 5300 s mem hd pa pb pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 5300 = true := by
    rw [hcode]; exact jumpDestFallback
  have hc : UInt256.isTrue ((UInt256.ofNat 1).eq (UInt256.ofNat 1)) := by decide
  have ha := Monpro.activeWords_fix s 2720 32 (by decide) (by omega) hact
  simp [guardProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    hc5, hc6, hc7, hguard, hc, hjd, State.activeWordsAfterUInt256, ha,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_pass (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions passProgram (stateAt 5296 s mem hd pa pb pdst ret rest) =
      some (CiosCached.setupState s mem hd pa pb pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 3561 = true := by
    rw [hcode]; exact Artifact.isValidJumpDest_index 2645 (by rfl)
  simp [passProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    CiosCached.setupState, hc5, hc6, hjd,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_fallback (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions fallbackProgram (stateAt 5300 s mem hd pa pb pdst ret rest) =
      some (Monpro.mpEntryState s mem pa pb pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 1215 = true := by
    rw [hcode]; exact jumpDest1865
  simp [fallbackProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    Monpro.mpEntryState, hc4, hc5, hjd,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard
