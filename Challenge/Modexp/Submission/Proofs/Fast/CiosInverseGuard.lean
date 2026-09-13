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
  [.op .JUMPDEST, .push 2 2720, .op .MLOAD, .push 1 1, .op .SUB,
   .push 2 3561, .op .JUMPI]

def fallbackProgram : List Instr := [.op .POP, .push 2 1215, .op .JUMP]

def guardBlock : Block Artifact.submissionArtifact .Osaka 5298 guardProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4054 7 5298 guardProgram
    (by decide) (by rfl) (by rfl) (by decide)
def fallbackBlock : Block Artifact.submissionArtifact .Osaka 5310 fallbackProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4061 3 5310 fallbackProgram
    (by decide) (by rfl) (by rfl) (by decide)
theorem jumpDest : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5298 = true :=
  Artifact.isValidJumpDest_index 4054 (by rfl)

theorem run_guardPass (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1) :
    runInstructions guardProgram (stateAt 5298 s mem hd pa pb pdst ret rest) =
      some (CiosCached.setupState s mem hd pa pb pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hne : (MachineState.readWord mem 2720).toNat ≠ 1 := by
    intro h
    apply hguard
    apply Challenge.EvmProof.Word.word_ext
    simpa using h
  have hc : UInt256.isTrue (UInt256.ofNat 1 - MachineState.readWord mem 2720) := by
    change (UInt256.ofNat 1 - MachineState.readWord mem 2720).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_sub_cond]
    simp only [show (UInt256.ofNat 1).toNat = 1 by decide]
    have hb : (MachineState.readWord mem 2720).toNat < 2 ^ 256 :=
      (MachineState.readWord mem 2720).val.isLt
    split <;> omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 3561 = true := by
    rw [hcode]
    exact Artifact.isValidJumpDest_index 2645 (by rfl)
  have ha := Monpro.activeWords_fix s 2720 32 (by decide) (by omega) hact
  simp [guardProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    CiosCached.setupState, hc5, hc6, hc7, hc, hjd, State.activeWordsAfterUInt256, ha,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_guardFallback (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hact : 88 ≤ s.activeWords.toNat)
    (hguard : MachineState.readWord mem 2720 = UInt256.ofNat 1) :
    runInstructions guardProgram (stateAt 5298 s mem hd pa pb pdst ret rest) =
      some (stateAt 5310 s mem hd pa pb pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc : ¬ UInt256.isTrue (UInt256.ofNat 1 - UInt256.ofNat 1) := by decide
  have ha := Monpro.activeWords_fix s 2720 32 (by decide) (by omega) hact
  simp [guardProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    hc5, hc6, hc7, hguard, hc, State.activeWordsAfterUInt256, ha,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_fallback (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions fallbackProgram (stateAt 5310 s mem hd pa pb pdst ret rest) =
      some (Monpro.mpEntryState s mem pa pb pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 1215 = true := by
    rw [hcode]; exact jumpDest1865
  simp [fallbackProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    Monpro.mpEntryState, hc4, hc5, hjd,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

#print axioms run_guardPass
#print axioms run_guardFallback
#print axioms run_fallback
end Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard
