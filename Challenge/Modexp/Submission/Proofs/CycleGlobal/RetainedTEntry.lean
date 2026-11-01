import Challenge.Modexp.Submission.Proofs.CycleGlobal.CsubCore
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.EarlyCsubInstructions
import Challenge.Modexp.Submission.Proofs.Fast.RetainedTNormalizer

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
The retained-accumulator entry of `CSUB`: a caller that keeps its canonical
accumulator at 2112 jumps here with only the return address on the stack.  The
block compares the leading limbs; a strictly smaller accumulator returns at once
directly through `SWAP1; JUMPI`, otherwise the return address and the destination 2112 are pushed and
the existing subtraction entry at 4529 runs in place.
-/

namespace CycleSubmission.Global.Fast.RetainedT
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.EvmProof.Word

def entryProgram : List Instr :=
  [.op .JUMPDEST, .push 0 0, .op .MLOAD, .push 2 2112, .op .MLOAD, .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .JUMPI]
/-- The fall-through pushes of the caller's return address (the entry is only called from
`blk2874`, which returns to 2412) and of the retained destination, ahead of the subtraction
entry at 3509. -/
def pushProgram : List Instr := [.push 2 2412, .push 2 2112]

def entryBlock : Block CycleSubmission.Artifact.artifact .Osaka 3493 entryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2709 8 3493 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)
def pushBlock : Block CycleSubmission.Artifact.artifact .Osaka 3503 pushProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2717 2 3503 pushProgram
    (by decide) (by rfl) (by rfl) (by decide)
theorem jumpDest4486 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3493 = true :=
  CycleSubmission.Global.Binding.jumpDest 2709 (by rfl)
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
  { s with pc := UInt256.ofNat 3493, stack := ret :: rest, memory := mem }
def pushState (s : State) (mem : ByteArray) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3503, stack := rest, memory := mem }
def returnedState (s : State) (mem : ByteArray) (ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := ret, stack := rest, memory := mem }

theorem run_entry (s : State) (mem : ByteArray) (ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true) :
    runInstructions entryProgram (entryState s mem ret rest) =
      some (if RetainedTNormalizer.Skip mem then returnedState s mem ret rest
        else pushState s mem rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have h0 : ({val := 0} : UInt256).toNat = 0 := rfl
  have h2112 : (2112 : UInt256).toNat = 2112 := by decide
  have heq2112 : (2112 : UInt256) = UInt256.ofNat 2112 := by decide
  have ha0 := EarlyCsub.activeWords_fix s 0 32 (by decide) (by omega) hact
  have haT := EarlyCsub.activeWords_fix s 2112 32 (by decide) (by omega) hact
  by_cases hskip : RetainedTNormalizer.Skip mem
  · have hz : (skipWord mem).toNat ≠ 0 := by rw [skipWord_toNat, if_pos hskip]; decide
    simp [entryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      entryState, returnedState, State.activeWordsAfterUInt256, h0, h2112,
      ha0, haT, Nat.add_assoc, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, skipWord_eq, UInt256.isTrue,
      hskip, hz, hcode, hjump, List.exchange]
  · have hz : (skipWord mem).toNat = 0 := by rw [skipWord_toNat, if_neg hskip]
    simp [entryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      entryState, pushState, State.activeWordsAfterUInt256, h0, h2112,
      ha0, haT, Nat.add_assoc, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, hc1, hc2, hc3, hc4, skipWord_eq, UInt256.isTrue,
      hskip, hz, List.exchange]

theorem run_push (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) :
    runInstructions pushProgram (pushState s mem rest) =
      some (Csub.subEntryState s mem (UInt256.ofNat 2112) (UInt256.ofNat 2412) rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have heq2112 : (2112 : UInt256) = UInt256.ofNat 2112 := by decide
  have heq2412 : (2412 : UInt256) = UInt256.ofNat 2412 := by decide
  have hc0 : rest.length < 1024 := by omega
  simp [pushProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    pushState, Csub.subEntryState, hc0, hc1, hc2, hc3, Nat.add_assoc,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, heq2112, heq2412]

/-- Every outcome of the leading-limb test reaches the caller with the
retained accumulator holding `resultMemory`. -/
def gasSteps_retained (s : State) (memory : ByteArray) (n : Nat)
    (ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hret : ret = UInt256.ofNat 2412)
    (hml : MachineState.readWord memory 2752 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord memory 2784 = UInt256.ofNat (2080+32*n))
    (hs32 : MachineState.readWord (Csub.csStep memory n n).memory 2688 = UInt256.ofNat (32*n))
    (htn : (MachineState.readWord (Csub.csStep memory n n).memory 2080).toNat ≤ 1)
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps (entryState s memory ret rest)
      (returnedState s (RetainedTNormalizer.resultMemory memory n) ret rest) := by
  have he := entryBlock.steps
    (EarlyCsub.environment (entryState s memory ret rest) hcode hfork hrun hnp) rfl
    (run_entry s memory ret rest hcap hact hcode hjump)
  by_cases hskip : RetainedTNormalizer.Skip memory
  · rw [if_pos hskip] at he
    rw [RetainedTNormalizer.result_of_skip memory n hskip]
    exact he
  · rw [if_neg hskip] at he
    have hp := pushBlock.steps
      (EarlyCsub.environment (pushState s memory rest) hcode hfork hrun hnp) rfl
      (run_push s memory rest hcap)
    subst hret
    have hk := Csub.gasSteps_csub_sub s memory n (UInt256.ofNat 2112) (UInt256.ofNat 2412) rest hcap hcode hfork
      hrun hnp hact hn hn32 hjump hml htl hs32
      (by rw [show (UInt256.ofNat 2112).toNat = 2112 by decide]; omega) htn hfast
    rw [RetainedTNormalizer.result_of_not_skip memory n hskip]
    have hend : Csub.subReturnedState s memory n n (UInt256.ofNat 2112) (UInt256.ofNat 2412) rest =
        returnedState s (Csub.subResultMemory memory n 2112) (UInt256.ofNat 2412) rest := by
      simp only [Csub.subReturnedState, returnedState, Csub.subResultMemory,
        show (UInt256.ofNat 2112).toNat = 2112 by decide]
    rw [← hend]
    exact (he.trans hp).trans hk

end CycleSubmission.Global.Fast.RetainedT
