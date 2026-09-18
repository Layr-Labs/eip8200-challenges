import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubInstructions
import Challenge.Modexp.Submission.Proofs.Fast.RetainedTNormalizer

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
The retained-accumulator entry of `CSUB`: a caller that keeps its canonical
accumulator at 2112 jumps here with only the return address on the stack.  The
block compares the leading limbs; a strictly smaller accumulator returns at once
through the tail `JUMPDEST; JUMP`, otherwise the destination 2112 is pushed and
the existing subtraction entry at 4501 runs in place.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.RetainedT
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.EvmProof.Word

def entryProgram : List Instr :=
  [.op .JUMPDEST, .push 0 0, .op .MLOAD, .push 2 2112, .op .MLOAD, .op .LT,
   .push 2 5249, .op .JUMPI]
/-- The fall-through push of the retained destination, ahead of the subtraction entry 4501. -/
def pushProgram : List Instr := [.push 2 2112]
def tailProgram : List Instr := [.op .JUMPDEST, .op .JUMP]

def entryBlock : Block Artifact.submissionArtifact .Osaka 4229 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3373 8 4229 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)
def pushBlock : Block Artifact.submissionArtifact .Osaka 4241 pushProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3381 1 4241 pushProgram
    (by decide) (by rfl) (by rfl) (by decide)
def tailBlock : Block Artifact.submissionArtifact .Osaka 5249 tailProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4210 2 5249 tailProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4486 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4229 = true :=
  Artifact.isValidJumpDest_index 3373 (by rfl)
theorem jumpDest5326 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5249 = true :=
  Artifact.isValidJumpDest_index 4210 (by rfl)

/-- The comparison word the entry block tests. -/
def skipWord (mem : ByteArray) : UInt256 :=
  UInt256.lt (MachineState.readWord mem 2112) (MachineState.readWord mem 0)

theorem skipWord_eq (mem : ByteArray) :
    UInt256.lt (MachineState.readWord mem 2112) (MachineState.readWord mem 0) = skipWord mem := rfl

theorem skipWord_toNat (mem : ByteArray) :
    (skipWord mem).toNat = if RetainedTNormalizer.Skip mem then 1 else 0 := by
  unfold skipWord
  rw [word_toNat_lt]
  by_cases h : (MachineState.readWord mem 2112).toNat < (MachineState.readWord mem 0).toNat
  · rw [if_pos h, if_pos (show RetainedTNormalizer.Skip mem from h)]
  · rw [if_neg h, if_neg (show ¬ RetainedTNormalizer.Skip mem from h)]

def entryState (s : State) (mem : ByteArray) (ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4229, stack := ret :: rest, memory := mem }
def tailState (s : State) (mem : ByteArray) (ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 5249, stack := ret :: rest, memory := mem }
def pushState (s : State) (mem : ByteArray) (ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4241, stack := ret :: rest, memory := mem }
def returnedState (s : State) (mem : ByteArray) (ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := ret, stack := rest, memory := mem }

theorem run_entry (s : State) (mem : ByteArray) (ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions entryProgram (entryState s mem ret rest) =
      some (if RetainedTNormalizer.Skip mem then tailState s mem ret rest
        else pushState s mem ret rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have h0 : ({val := 0} : UInt256).toNat = 0 := rfl
  have h2112 : (2112 : UInt256).toNat = 2112 := by decide
  have heq5326 : (5249 : UInt256) = UInt256.ofNat 5249 := by decide
  have h5326 : (5249 : UInt256).toNat = 5249 := by decide
  have heq2112 : (2112 : UInt256) = UInt256.ofNat 2112 := by decide
  have ha0 := EarlyCsub.activeWords_fix s 0 32 (by decide) (by omega) hact
  have haT := EarlyCsub.activeWords_fix s 2112 32 (by decide) (by omega) hact
  by_cases hskip : RetainedTNormalizer.Skip mem
  · have hz : (skipWord mem).toNat ≠ 0 := by rw [skipWord_toNat, if_pos hskip]; decide
    simp [entryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      entryState, tailState, State.activeWordsAfterUInt256, h0, h2112, h5326,
      ha0, haT, Nat.add_assoc, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, skipWord_eq, UInt256.isTrue,
      hskip, hz, hcode, jumpDest5326, heq5326]
  · have hz : (skipWord mem).toNat = 0 := by rw [skipWord_toNat, if_neg hskip]
    simp [entryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      entryState, pushState, State.activeWordsAfterUInt256, h0, h2112, h5326,
      ha0, haT, Nat.add_assoc, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, skipWord_eq, UInt256.isTrue,
      hskip, hz]

theorem run_push (s : State) (mem : ByteArray) (ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) :
    runInstructions pushProgram (pushState s mem ret rest) =
      some (Csub.subEntryState s mem (UInt256.ofNat 2112) ret rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have heq2112 : (2112 : UInt256) = UInt256.ofNat 2112 := by decide
  simp [pushProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    pushState, Csub.subEntryState, hc1, hc2, Nat.add_assoc,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, heq2112]

theorem run_tail (s : State) (mem : ByteArray) (ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true) :
    runInstructions tailProgram (tailState s mem ret rest) =
      some (returnedState s mem ret rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  simp [tailProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    tailState, returnedState, hc1, Nat.add_assoc, hcode, hjump,
    Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Every outcome of the leading-limb test reaches the caller with the
retained accumulator holding `resultMemory`. -/
def gasSteps_retained (s : State) (memory : ByteArray) (n : Nat)
    (ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hml : MachineState.readWord memory 2752 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord memory 2784 = UInt256.ofNat (2080+32*n))
    (hs32 : MachineState.readWord (Csub.csStep memory n n).memory 2688 = UInt256.ofNat (32*n))
    (htn : (MachineState.readWord (Csub.csStep memory n n).memory 2080).toNat ≤ 1)
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps (entryState s memory ret rest)
      (returnedState s (RetainedTNormalizer.resultMemory memory n) ret rest) := by
  have he := entryBlock.steps
    (EarlyCsub.environment (entryState s memory ret rest) hcode hfork hrun hnp) rfl
    (run_entry s memory ret rest hcap hact hcode)
  by_cases hskip : RetainedTNormalizer.Skip memory
  · rw [if_pos hskip] at he
    have ht := tailBlock.steps
      (EarlyCsub.environment (tailState s memory ret rest) hcode hfork hrun hnp) rfl
      (run_tail s memory ret rest hcap hcode hjump)
    rw [RetainedTNormalizer.result_of_skip memory n hskip]
    exact he.trans ht
  · rw [if_neg hskip] at he
    have hp := pushBlock.steps
      (EarlyCsub.environment (pushState s memory ret rest) hcode hfork hrun hnp) rfl
      (run_push s memory ret rest hcap)
    have hk := Csub.gasSteps_csub_sub s memory n (UInt256.ofNat 2112) ret rest hcap hcode hfork
      hrun hnp hact hn hn32 hjump hml htl hs32
      (by rw [show (UInt256.ofNat 2112).toNat = 2112 by decide]; omega) htn hfast
    rw [RetainedTNormalizer.result_of_not_skip memory n hskip]
    have hend : Csub.subReturnedState s memory n n (UInt256.ofNat 2112) ret rest =
        returnedState s (Csub.subResultMemory memory n 2112) ret rest := by
      simp only [Csub.subReturnedState, returnedState, Csub.subResultMemory,
        show (UInt256.ofNat 2112).toNat = 2112 by decide]
    rw [← hend]
    exact (he.trans hp).trans hk

#print axioms gasSteps_retained
end Challenge.Modexp.Submission.Proofs.Fast.RetainedT
